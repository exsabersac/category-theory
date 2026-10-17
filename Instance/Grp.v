Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * The category of groups *)

(*
 nLab:      https://ncatlab.org/nlab/show/group
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the category of groups的来源与用途

   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:  Riehl, "Category Theory in Context", Dover, 2016, Section 1.4
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
   Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950

   本节说明函子、Eilenberg–Moore、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record GrpObject := {
  grp_setoid :> SetoidObject;

  grp_unit : carrier grp_setoid;
  grp_mul  : carrier grp_setoid → carrier grp_setoid → carrier grp_setoid;
  grp_inv  : carrier grp_setoid → carrier grp_setoid;

  grp_mul_respects : Proper (equiv ==> equiv ==> equiv) grp_mul;

  grp_mul_assoc : ∀ a b c,
    grp_mul (grp_mul a b) c ≈ grp_mul a (grp_mul b c);
  grp_mul_unit_l : ∀ a, grp_mul grp_unit a ≈ a;
  grp_mul_inv_l  : ∀ a, grp_mul (grp_inv a) a ≈ grp_unit;

  (* The carrier is a SET: its `≈` is logically equivalent to a [Prop]-valued
     relation.  See Lib/Setoid/Propositional.v. *)
  grp_prop : PropEquiv (is_setoid grp_setoid)
}.

#[export] Existing Instance grp_mul_respects.
#[export] Existing Instance grp_prop.

Section GrpFacts.

Context (G : GrpObject).

(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_mul_inv_r (a : carrier G) : grp_mul G a (grp_inv G a) ≈ grp_unit G.
Proof.
  assert (Hinner : grp_mul G (grp_inv G a) (grp_mul G a (grp_inv G a))
                     ≈ grp_inv G a).
  { rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l. }
  transitivity (grp_mul G (grp_inv G (grp_inv G a))
                  (grp_mul G (grp_inv G a) (grp_mul G a (grp_inv G a)))).
  - rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    symmetry; apply grp_mul_unit_l.
  - rewrite Hinner.
    apply grp_mul_inv_l.
Qed.

(* 相关说明。 （已译） *)
Lemma grp_mul_unit_r (a : carrier G) : grp_mul G a (grp_unit G) ≈ a.
Proof.
  transitivity (grp_mul G a (grp_mul G (grp_inv G a) a)).
  - rewrite grp_mul_inv_l.
    reflexivity.
  - rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_l.
Qed.

(* 相关说明。 （已译） *)
Lemma grp_inv_unique_r (a b : carrier G) :
  grp_mul G a b ≈ grp_unit G → b ≈ grp_inv G a.
Proof.
  intro Hab.
  transitivity (grp_mul G (grp_unit G) b).
  - symmetry; apply grp_mul_unit_l.
  - rewrite <- (grp_mul_inv_l G a).
    rewrite grp_mul_assoc.
    rewrite Hab.
    apply grp_mul_unit_r.
Qed.

(* Uniqueness of inverses, left-handed form. *)
Lemma grp_inv_unique_l (a b : carrier G) :
  grp_mul G b a ≈ grp_unit G → b ≈ grp_inv G a.
Proof.
  intro Hba.
  transitivity (grp_mul G b (grp_unit G)).
  - symmetry; apply grp_mul_unit_r.
  - rewrite <- (grp_mul_inv_r a).
    rewrite <- grp_mul_assoc.
    rewrite Hba.
    apply grp_mul_unit_l.
Qed.

(* 相关说明。 （已译） *)
Lemma grp_inv_respects_law (a b : carrier G) :
  a ≈ b → grp_inv G a ≈ grp_inv G b.
Proof.
  intro Hab.
  apply grp_inv_unique_l.
  rewrite <- Hab.
  apply grp_mul_inv_l.
Qed.

End GrpFacts.

#[export] Instance grp_inv_Proper (G : GrpObject) :
  Proper (equiv ==> equiv) (grp_inv G) := grp_inv_respects_law G.

Section GrpFacts2.

Context (G : GrpObject).

Lemma grp_inv_unit : grp_inv G (grp_unit G) ≈ grp_unit G.
Proof.
  symmetry.
  apply grp_inv_unique_l.
  apply grp_mul_unit_l.
Qed.

Lemma grp_inv_inv (a : carrier G) : grp_inv G (grp_inv G a) ≈ a.
Proof.
  symmetry.
  apply grp_inv_unique_l.
  apply grp_mul_inv_r.
Qed.

(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_inv_mul (a b : carrier G) :
  grp_inv G (grp_mul G a b) ≈ grp_mul G (grp_inv G b) (grp_inv G a).
Proof.
  symmetry.
  apply grp_inv_unique_l.
  rewrite grp_mul_assoc.
  rewrite <- (grp_mul_assoc G (grp_inv G a) a b).
  rewrite grp_mul_inv_l.
  rewrite grp_mul_unit_l.
  apply grp_mul_inv_l.
Qed.

Lemma grp_cancel_l (a b c : carrier G) :
  grp_mul G a b ≈ grp_mul G a c → b ≈ c.
Proof.
  intro Habc.
  transitivity (grp_mul G (grp_mul G (grp_inv G a) a) b).
  - rewrite grp_mul_inv_l.
    symmetry; apply grp_mul_unit_l.
  - rewrite grp_mul_assoc.
    rewrite Habc.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l.
Qed.

Lemma grp_cancel_r (a b c : carrier G) :
  grp_mul G b a ≈ grp_mul G c a → b ≈ c.
Proof.
  intro Habc.
  transitivity (grp_mul G b (grp_mul G a (grp_inv G a))).
  - rewrite grp_mul_inv_r.
    symmetry; apply grp_mul_unit_r.
  - rewrite <- grp_mul_assoc.
    rewrite Habc.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_r.
Qed.

End GrpFacts2.

(* 相关说明。 （已译） *)
Record GrpHom (G H : GrpObject) := {
  grp_map :> SetoidMorphism (grp_setoid G) (grp_setoid H);

  grp_map_unit : grp_map (grp_unit G) ≈ grp_unit H;
  grp_map_mul : ∀ a b,
    grp_map (grp_mul G a b) ≈ grp_mul H (grp_map a) (grp_map b)
}.

Arguments grp_map {G H} _.
Arguments grp_map_unit {G H} _.
Arguments grp_map_mul {G H} _ _ _.

(* Homomorphisms preserve inversion.  f (a⁻¹) is a left inverse of f a,
   because f carries a⁻¹ * a ≈ e to f(a⁻¹) * f(a) ≈ e; uniqueness of left
   inverses finishes. *)
Lemma grp_map_inv {G H : GrpObject} (f : GrpHom G H) (a : carrier G) :
  grp_map f (grp_inv G a) ≈ grp_inv H (grp_map f a).
Proof.
  apply grp_inv_unique_l.
  rewrite <- grp_map_mul.
  rewrite grp_mul_inv_l.
  apply grp_map_unit.
Qed.

(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma grp_map_unit_from_mul {G H : GrpObject}
      (f : SetoidMorphism (grp_setoid G) (grp_setoid H))
      (Hmul : ∀ a b, f (grp_mul G a b) ≈ grp_mul H (f a) (f b)) :
  f (grp_unit G) ≈ grp_unit H.
Proof.
  apply (grp_cancel_l H (f (grp_unit G))).
  rewrite <- Hmul.
  rewrite grp_mul_unit_l.
  symmetry; apply grp_mul_unit_r.
Qed.

(* Smart constructor: a setoid map preserving multiplication is already a
   group homomorphism. *)
Definition Build_GrpHom' {G H : GrpObject}
        (f : SetoidMorphism (grp_setoid G) (grp_setoid H))
        (Hmul : ∀ a b, f (grp_mul G a b) ≈ grp_mul H (f a) (f b)) :
  GrpHom G H :=
  {| grp_map      := f
   ; grp_map_unit := grp_map_unit_from_mul f Hmul
   ; grp_map_mul  := Hmul |}.

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)
#[export]
Program Instance GrpHom_Setoid {G H : GrpObject} : Setoid (GrpHom G H) := {|
  equiv := fun f g => ∀ a, grp_map f a ≈ grp_map g a
|}.
Next Obligation.
  intros G H.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (grp_map g a).
    + apply Hfg.
    + apply Hgh.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance GrpHom_PropEquiv {G H : GrpObject} :
  PropEquiv (@GrpHom_Setoid G H).
Proof.
  unshelve refine
    {| pequiv := fun f g : GrpHom G H =>
                   forall a : carrier (grp_setoid G),
                     @pequiv _ _ (grp_prop H) (grp_map f a) (grp_map g a) |}.
  - intros f g Hfg a; exact (pequiv_to _ _ (Hfg a)).
  - intros f g Hfg a; exact (pequiv_from _ _ (Hfg a)).
Defined.

(* The 恒等 homomorphism: 恒等 setoid map, preserves the
 unit operation nose. （已译） *)
Program Definition grp_hom_id {G : GrpObject} : GrpHom G G := {|
  grp_map := setoid_morphism_id
|}.
Next Obligation.
  intros G; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G a b; simpl.
  reflexivity.
Qed.

(* Composition homomorphisms: 复合 underlying setoid maps;
 preservation unit operation composes. （已译） *)
Program Definition grp_hom_compose {G H K : GrpObject}
        (f : GrpHom H K) (g : GrpHom G H) : GrpHom G K := {|
  grp_map := setoid_morphism_compose (grp_map f) (grp_map g)
|}.
Next Obligation.
  intros G H K f g; simpl.
  unfold Basics.compose.
  rewrite (grp_map_unit g).
  apply (grp_map_unit f).
Qed.
Next Obligation.
  intros G H K f g a b; simpl.
  unfold Basics.compose.
  rewrite (grp_map_mul g).
  apply (grp_map_mul f).
Qed.

Lemma grp_hom_compose_respects {G H K : GrpObject} :
  Proper (equiv ==> equiv ==> equiv) (@grp_hom_compose G H K).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(* The 范畴 groups.

 对象: groups over setoids
 arrows: 单位- operation-preserving setoid maps
 恒等: 恒等 setoid map
 复合: 复合 setoid maps（已译） *)
(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Grp@{u p} : Category@{u p p} := {|
  obj     := GrpObject@{p p p};
  hom     := GrpHom@{p};
  homset  := @GrpHom_Setoid@{p};
  id      := @grp_hom_id@{p};
  compose := @grp_hom_compose@{u p};

  compose_respects := @grp_hom_compose_respects@{u p}
|}.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Grp_LocallyPropositional : LocallyPropositional Grp.
Proof.
  constructor.
  intros G H.
  exact (@GrpHom_PropEquiv G H).
Defined.

(* The forgetful 函子 [Sets], dropping group structure. （已译） *)
Program Definition Grp_Forget : Grp ⟶ Sets := {|
  fobj := fun G => grp_setoid G;
  fmap := fun _ _ f => grp_map f
|}.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros G a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G H K f g a; simpl.
  reflexivity.
Qed.

(* [Grp_Forget] is faithful by construction, since equivalence of
   homomorphisms in [Grp] IS equivalence of the underlying setoid maps. *)
#[export] Program Instance Grp_Forget_Faithful : Faithful Grp_Forget.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.

(* * ** The zero 对象: trivial group （已译） *)

(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grp_trivial@{p} : GrpObject@{p p p}.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := poly_unit@{p}; is_setoid := unit_setoid@{p p} |};
    grp_unit := ttt;
    grp_mul := fun _ _ => ttt;
    grp_inv := fun _ => ttt;
    grp_prop := unit_PropEquiv@{p p}
  |}.
  - intros x y Hxy u v Huv.
    reflexivity.
  - intros a b c.
    reflexivity.
  - intros a.
    destruct a.
    reflexivity.
  - intros a.
    reflexivity.
Defined.

(* The unique homomorphism 进入 trivial group: everything the
 point. （已译） *)
Definition Grp_one@{u p} (G : GrpObject@{p p p}) :
  G ~{Grp@{u p}}~> Grp_trivial@{p}.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G Grp_trivial {| morphism := fun _ => ttt |} _ _).
  - intros a b Hab.
    reflexivity.
  - reflexivity.
  - intros a b.
    reflexivity.
Defined.

(* Uniqueness into the trivial group: both images live in [poly_unit]. *)
Lemma Grp_one_unique@{u p} (G : GrpObject@{p p p})
  (f g : G ~{Grp@{u p}}~> Grp_trivial@{p}) : f ≈ g.
Proof.
  intro a.
  destruct (grp_map f a), (grp_map g a).
  reflexivity.
Qed.

Definition Grp_Terminal@{u p} : @Terminal Grp@{u p} :=
  @Build_Terminal Grp@{u p} Grp_trivial@{p} Grp_one@{u p} Grp_one_unique@{u p}.

(* 相关说明。 （已译） *)
Definition Grp_zero_hom@{u p} (G : GrpObject@{p p p}) :
  Grp_trivial@{p} ~{Grp@{u p}}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom Grp_trivial G {| morphism := fun _ => grp_unit G |} _ _).
  - intros a b Hab.
    reflexivity.
  - reflexivity.
  - intros a b.
    symmetry.
    apply grp_mul_unit_l.
Defined.

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Grp_zero_hom_unique@{u p} (G : GrpObject@{p p p})
  (f g : Grp_trivial@{p} ~{Grp@{u p}}~> G) : f ≈ g.
Proof.
  intro a.
  destruct a.
  transitivity (grp_unit G).
  - exact (grp_map_unit f).
  - symmetry.
    exact (grp_map_unit g).
Qed.

Definition Grp_Initial@{u p} : @Initial Grp@{u p} :=
  @Build_Terminal (Grp@{u p}^op) Grp_trivial@{p} Grp_zero_hom@{u p}
    Grp_zero_hom_unique@{u p}.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Grp_Zero@{u p} : ZeroObject Grp@{u p} :=
  @Build_ZeroObject Grp@{u p} Grp_Terminal@{u p} Grp_Initial@{u p}
    iso_id@{u p p u}.

(** ** Binary direct products *)

(* 相关说明。 （已译） *)
Definition Grp_product (G H : GrpObject) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := (carrier G * carrier H)%type
                   ; is_setoid := @prod_setoid _ _
                       (is_setoid (grp_setoid G))
                       (is_setoid (grp_setoid H)) |};
    grp_unit := (grp_unit G, grp_unit H);
    grp_mul := fun p q =>
      (grp_mul G (fst p) (fst q), grp_mul H (snd p) (snd q));
    grp_inv := fun p => (grp_inv G (fst p), grp_inv H (snd p));
    grp_prop := prod_PropEquiv (grp_prop G) (grp_prop H)
  |}.
  - intros p p' Hp q q' Hq.
    destruct Hp as [Hp1 Hp2], Hq as [Hq1 Hq2].
    split; simpl.
    + now rewrite Hp1, Hq1.
    + now rewrite Hp2, Hq2.
  - intros a b c.
    split; simpl; apply grp_mul_assoc.
  - intros a.
    split; simpl; apply grp_mul_unit_l.
  - intros a.
    split; simpl; apply grp_mul_inv_l.
Defined.

(* Left projection [fst]: a homomorphism on the nose. *)
Definition Grp_exl {G H : GrpObject} : Grp_product G H ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G H) G {| morphism := fun p => fst p |} _ _).
  - intros p q Hpq.
    exact (fst Hpq).
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* Right projection [snd]. *)
Definition Grp_exr {G H : GrpObject} : Grp_product G H ~{Grp}~> H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G H) H {| morphism := fun p => snd p |} _ _).
  - intros p q Hpq.
    exact (snd Hpq).
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* The mediating morphism a ↦ (f a, g a): componentwise a homomorphism. *)
Definition Grp_fork {K G H : GrpObject}
  (f : K ~{Grp}~> G) (g : K ~{Grp}~> H) : K ~{Grp}~> Grp_product G H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom K (Grp_product G H)
       {| morphism := fun a => (grp_map f a, grp_map g a) |} _ _).
  - intros a b Hab.
    split; simpl; now rewrite Hab.
  - split; simpl.
    + apply (grp_map_unit f).
    + apply (grp_map_unit g).
  - intros a b.
    split; simpl.
    + apply (grp_map_mul f).
    + apply (grp_map_mul g).
Defined.

(* The 普遍性质 holds because 等价 pairs the
 product setoid IS componentwise 等价, so both halves of
 [ump_products] projections that. （已译） *)
#[export] Program Instance Grp_Cartesian : @Cartesian Grp := {
  product_obj := Grp_product;
  fork := @Grp_fork;
  exl := @Grp_exl;
  exr := @Grp_exr
}.
Next Obligation.
  intros K G H f f' Hf g g' Hg a.
  split; simpl.
  - exact (Hf a).
  - exact (Hg a).
Qed.
Next Obligation.
  intros K G H f g h.
  split.
  - intro Hh.
    split; intro a.
    + exact (fst (Hh a)).
    + exact (snd (Hh a)).
  - intros [H1 H2] a.
    split; simpl.
    + exact (H1 a).
    + exact (H2 a).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_kernel_carrier {G H : GrpObject} (f : G ~{Grp}~> H) : Type :=
  { a : carrier G & grp_map f a ≈ grp_unit H }.

(* Two kernel elements equivalent underlying elements are;
 membership witness ignored, so no 证明 irrelevance needed. （已译） *)
Program Definition grp_kernel_setoid {G H : GrpObject} (f : G ~{Grp}~> H) :
  Setoid (grp_kernel_carrier f) := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.
Next Obligation.
  intros G H f.
  constructor.
  - intro p.
    reflexivity.
  - intros p q Hpq.
    now symmetry.
  - intros p q r Hpq Hqr.
    now transitivity (projT1 q).
Qed.

Definition Grp_kernel {G H : GrpObject} (f : G ~{Grp}~> H) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := grp_kernel_carrier f
                   ; is_setoid := grp_kernel_setoid f |};
    grp_unit := existT _ (grp_unit G) (grp_map_unit f);
    grp_mul := fun p q =>
      existT _ (grp_mul G (projT1 p) (projT1 q)) _;
    grp_inv := fun p => existT _ (grp_inv G (projT1 p)) _
  |}.
  - (* the product of two kernel elements is a kernel element *)
    rewrite grp_map_mul, (projT2 p), (projT2 q).
    apply grp_mul_unit_l.
  - (* the inverse of a kernel element is a kernel element *)
    rewrite grp_map_inv, (projT2 p).
    apply grp_inv_unit.
  - intros p p' Hp q q' Hq.
    simpl in *.
    now rewrite Hp, Hq.
  - intros a b c.
    simpl.
    apply grp_mul_assoc.
  - intros a.
    simpl.
    apply grp_mul_unit_l.
  - intros a.
    simpl.
    apply grp_mul_inv_l.
  - (*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    unshelve refine (sigma_first_PropEquiv _ _ _ (grp_prop G)).
    + intros p q Hpq; exact Hpq.
    + intros p q Hpq; exact Hpq.
Defined.

(* The two probe maps out kernel: 含入 ... （已译） *)
Definition Grp_kernel_incl {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_kernel f ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_kernel f) G {| morphism := fun p => projT1 p |} _ _).
  - intros p q Hpq.
    exact Hpq.
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* ... 常值 map at unit. （已译） *)
Definition Grp_kernel_triv {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_kernel f ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_kernel f) G
       {| morphism := fun _ => grp_unit G |} _ _).
  - intros p q Hpq.
    reflexivity.
  - reflexivity.
  - intros p q.
    symmetry.
    apply grp_mul_unit_l.
Defined.

(* f cannot tell two probe maps apart: it sends every kernel element
 unit 定义 kernel, unit unit by
 [grp_map_unit]. （已译） *)
Lemma Grp_kernel_probe {G H : GrpObject} (f : G ~{Grp}~> H) :
  f ∘ Grp_kernel_incl f ≈ f ∘ Grp_kernel_triv f.
Proof.
  intro p.
  simpl.
  unfold Basics.compose.
  transitivity (grp_unit H).
  - exact (projT2 p).
  - symmetry.
    apply (grp_map_unit f).
Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Grp_injectivity_is_monic {G H : GrpObject} (f : G ~{Grp}~> H) :
  (∀ a b : carrier G, grp_map f a ≈ grp_map f b → a ≈ b) ↔ Monic f.
Proof.
  split.
  - intro Hinj.
    constructor.
    intros K g1 g2 Hg a.
    apply Hinj.
    exact (Hg a).
  - intros [Hmonic] a b Hab.
    assert (Hker : grp_map f (grp_mul G a (grp_inv G b)) ≈ grp_unit H).
    { rewrite grp_map_mul, grp_map_inv, Hab.
      apply grp_mul_inv_r. }
    pose proof (Hmonic (Grp_kernel f) (Grp_kernel_incl f) (Grp_kernel_triv f)
                  (Grp_kernel_probe f)) as Htriv.
    specialize (Htriv (existT _ (grp_mul G a (grp_inv G b)) Hker)).
    simpl in Htriv.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite grp_mul_inv_r.
    exact Htriv.
Qed.

(* * ** The opposite-group 函子 inversion (Riehl, Example 1.4.4(vi)) （已译） *)

(* 相关说明。 （已译） *)
Definition Grp_op_obj (G : GrpObject) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := grp_setoid G;
    grp_prop := grp_prop G;
    grp_unit := grp_unit G;
    grp_mul := fun a b => grp_mul G b a;
    grp_inv := grp_inv G
  |}.
  - intros a a' Ha b b' Hb.
    now rewrite Ha, Hb.
  - intros a b c.
    symmetry.
    apply grp_mul_assoc.
  - intros a.
    apply grp_mul_unit_r.
  - intros a.
    apply grp_mul_inv_r.
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grp_op_map {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_op_obj G ~{Grp}~> Grp_op_obj H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_op_obj G) (Grp_op_obj H) (grp_map f) _ _).
  - apply (grp_map_unit f).
  - intros a b.
    apply (grp_map_mul f).
Defined.

Program Definition Grp_Op : Grp ⟶ Grp := {|
  fobj := Grp_op_obj;
  fmap := @Grp_op_map
|}.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros G a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G H K f g a; simpl.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition Grp_inv_to (G : GrpObject) : G ~{Grp}~> Grp_op_obj G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G (Grp_op_obj G) {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - exact (grp_inv_unit G).
  - intros a b.
    exact (grp_inv_mul G a b).
Defined.

(* The same map read backwards, a homomorphism G^op ~> G. *)
Definition Grp_inv_from (G : GrpObject) : Grp_op_obj G ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_op_obj G) G {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - exact (grp_inv_unit G).
  - intros a b.
    exact (grp_inv_mul G b a).
Defined.

(* Naturality in both orientations is [grp_map_inv]: homomorphisms commute
   with inversion. *)
Program Definition Grp_inv_Transform : @Id Grp ⟹ Grp_Op := {|
  transform := Grp_inv_to
|}.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  apply grp_map_inv.
Qed.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.

Program Definition Grp_inv_Transform_inv : Grp_Op ⟹ @Id Grp := {|
  transform := Grp_inv_from
|}.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  apply grp_map_inv.
Qed.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.

(* The 恒等 函子 [Grp] naturally isomorphic the
 opposite-group 函子, component at G being inversion. Both round
 trips [grp_inv_inv]. （已译） *)
Program Definition Grp_op_Isomorphism :
  @Isomorphism ([Grp, Grp]) (@Id Grp) Grp_Op := {|
  to   := Grp_inv_Transform;
  from := Grp_inv_Transform_inv
|}.
Next Obligation.
  intros G a; simpl.
  unfold Basics.compose.
  apply grp_inv_inv.
Qed.
Next Obligation.
  intros G a; simpl.
  unfold Basics.compose.
  apply grp_inv_inv.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_prod_Monoidal : @Monoidal Sets :=
  @CC_Monoidal Sets Sets_Cartesian Sets_Terminal.

Definition Sets_CartesianMonoidal : @CartesianMonoidal Sets :=
  @CC_CartesianMonoidal Sets Sets_Cartesian Sets_Terminal.

Program Definition Grp_unit_map (G : GrpObject) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> grp_setoid G :=
  {| morphism := fun _ => grp_unit G |}.

Program Definition Grp_mul_map (G : GrpObject) :
  @product_obj Sets Sets_Cartesian (grp_setoid G) (grp_setoid G)
    ~{Sets}~> grp_setoid G :=
  {| morphism := fun p => grp_mul G (fst p) (snd p) |}.
Next Obligation.
  intros G p q Hpq.
  destruct Hpq as [H1 H2].
  simpl in *.
  now rewrite H1, H2.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grp_MonoidObject (G : GrpObject) :
  @MonoidObject Sets Sets_prod_Monoidal (grp_setoid G).
Proof.
  unshelve notypeclasses refine
    (@Build_MonoidObject Sets Sets_prod_Monoidal (grp_setoid G)
       (Grp_unit_map G) (Grp_mul_map G) _ _ _).
  - intro p; simpl.
    apply grp_mul_unit_l.
  - intro p; simpl.
    apply grp_mul_unit_r.
  - intro p; simpl.
    apply grp_mul_assoc.
Defined.

Program Definition Grp_inverse_map (G : GrpObject) :
  grp_setoid G ~{Sets}~> grp_setoid G := {| morphism := grp_inv G |}.

(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grp_GroupObject (G : GrpObject) :
  @GroupObject Sets Sets_CartesianMonoidal (grp_setoid G).
Proof.
  unshelve notypeclasses refine
    (@Build_GroupObject Sets Sets_CartesianMonoidal (grp_setoid G)
       (Grp_MonoidObject G) (Grp_inverse_map G) _ _).
  - intro a; simpl.
    apply grp_mul_inv_l.
  - intro a; simpl.
    apply grp_mul_inv_r.
Defined.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GroupObject_GrpObject (X : Sets)
  (PX : PropEquiv (is_setoid X))
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) : GrpObject.
Proof.
  destruct GO as [mon inv Hleft Hright].
  destruct mon as [me ma Hunitl Hunitr Hassoc].
  unshelve notypeclasses refine {|
    grp_setoid := X;
    grp_unit := me ttt;
    grp_mul := fun a b => ma (a, b);
    grp_inv := fun a => inv a;
    grp_prop := PX
  |}.
  - intros a a' Ha b b' Hb.
    apply proper_morphism.
    split; assumption.
  - intros a b c.
    exact (Hassoc ((a, b), c)).
  - intros a.
    exact (Hunitl (ttt, a)).
  - intros a.
    exact (Hleft a).
Defined.

(* 相关说明。 （已译） *)
Example Grp_GroupObject_roundtrip_unit (G : GrpObject) :
  grp_unit (GroupObject_GrpObject (grp_setoid G) (grp_prop G) (Grp_GroupObject G))
    ≈ grp_unit G.
Proof. reflexivity. Qed.

Example Grp_GroupObject_roundtrip_mul (G : GrpObject) (a b : carrier G) :
  grp_mul (GroupObject_GrpObject (grp_setoid G) (grp_prop G) (Grp_GroupObject G)) a b
    ≈ grp_mul G a b.
Proof. reflexivity. Qed.

Example Grp_GroupObject_roundtrip_inv (G : GrpObject) (a : carrier G) :
  grp_inv (GroupObject_GrpObject (grp_setoid G) (grp_prop G) (Grp_GroupObject G)) a
    ≈ grp_inv G a.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Grp 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition bool_setoid@{u} : Setoid@{u u} bool :=
  {| equiv := @eq bool; setoid_equiv := eq_equivalence@{u u} |}.

Definition Z2@{p} : GrpObject@{p p p}.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := bool ; is_setoid := bool_setoid@{p} |};
    grp_unit := false;
    grp_mul  := xorb;
    grp_inv  := fun b => b;
    (* [bool_setoid]'s `≈` is [@eq bool], already a [Prop]; instance
       resolution sees through the hand [Program Definition] to
       [eq_PropEquiv]. *)
    grp_prop := eq_PropEquiv bool
  |}.
  - intros x y Hxy u v Huv; simpl in *; subst; reflexivity.
  - intros a b c; simpl; now destruct a, b, c.
  - intros a; simpl; now destruct a.
  - intros a; simpl; now destruct a.
Defined.

(* Z2 is genuinely nontrivial. *)
Lemma Z2_nontrivial : (@equiv _ (grp_setoid Z2) true false) -> False.
Proof. simpl. discriminate. Qed.

(* The unique hom Z2 ~> 1 is NOT injective ... *)
Lemma Z2_to_one_not_injective :
  (forall a b : carrier Z2, grp_map (Grp_one Z2) a ≈ grp_map (Grp_one Z2) b -> a ≈ b) -> False.
Proof.
  intro Hinj.
  apply Z2_nontrivial.
  apply Hinj.
  simpl. reflexivity.
Qed.

(* ... hence NOT monic.  So `Monic` in Grp is a non-vacuous predicate. *)
Theorem Monic_in_Grp_is_not_vacuous : Monic (Grp_one Z2) -> False.
Proof.
  intro Hm.
  apply Z2_to_one_not_injective.
  destruct (Grp_injectivity_is_monic (Grp_one Z2)) as [_ Hback].
  exact (Hback Hm).
Qed.

(* And some map IS monic: 恒等 Z2. （已译） *)
Theorem Monic_in_Grp_is_inhabited : @Monic Grp Z2 Z2 (@id Grp Z2).
Proof. apply (@id_monic Grp Z2). Qed.

(* 相关说明。 （已译） *)
Definition ker_true : carrier (Grp_kernel (Grp_one Z2)).
Proof. exists true. simpl. reflexivity. Defined.

Lemma Grp_kernel_nondegenerate :
  (@equiv _ (grp_setoid (Grp_kernel (Grp_one Z2)))
        ker_true (grp_unit (Grp_kernel (Grp_one Z2)))) -> False.
Proof. simpl. discriminate. Qed.

(* ===================================================================== *)
(* E: the OTHER round trip, GroupObject -> GrpObject -> GroupObject.      *)
(*    Is it provable?  (It is NOT stated in Instance/Grp.v.)              *)
(* ===================================================================== *)

(* 相关说明。 （已译） *)
Example rt_back_unit (X : Sets) (PX : PropEquiv (is_setoid X))
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) :
  @mempty Sets Sets_prod_Monoidal X
     (Grp_MonoidObject (GroupObject_GrpObject X PX GO))
  ≈ @mempty Sets Sets_prod_Monoidal X GO.
Proof. intro u; destruct u; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.

Example rt_back_mul (X : Sets) (PX : PropEquiv (is_setoid X))
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) :
  @mappend Sets Sets_prod_Monoidal X
     (Grp_MonoidObject (GroupObject_GrpObject X PX GO))
  ≈ @mappend Sets Sets_prod_Monoidal X GO.
Proof. intro p; destruct p; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.

Section RTInv.
#[local] Existing Instance Sets_CartesianMonoidal.
Context (X : Sets).
Context (PX : PropEquiv (is_setoid X)).
Context `{GO : @GroupObject Sets Sets_CartesianMonoidal X}.
Example rt_back_inv : Grp_inverse_map (GroupObject_GrpObject X PX GO) ≈ inverse[X].
Proof. intro a; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.
End RTInv.

(* ===================================================================== *)
(* Is Grp_Op an involution on the nose?                                   *)
(* ===================================================================== *)

