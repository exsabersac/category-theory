(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** ** Objects *)

Record OrdObject := {
  ord_setoid :> SetoidObject;

  ord_le : carrier ord_setoid → carrier ord_setoid → Prop;

  ord_le_respects : Proper (equiv ==> equiv ==> iff) ord_le;

  ord_refl  : ∀ x, ord_le x x;
  ord_trans : ∀ x y z, ord_le x y → ord_le y z → ord_le x z
}.

#[export] Existing Instance ord_le_respects.

(** The order is implied by the carrier's own equivalence: this is the one
    consequence of [ord_le_respects] that the development below consumes. *)
Lemma ord_le_of_equiv (P : OrdObject) (x y : carrier (ord_setoid P)) :
  x ≈ y → ord_le P x y.
Proof.
  intro Hxy.
  assert (Hxx : x ≈ x) by reflexivity.
  exact (proj1 (ord_le_respects P x x Hxx x y Hxy) (ord_refl P x)).
Qed.


(** ** Morphisms *)

Record OrdHom (P Q : OrdObject) := {
  ord_fn :> SetoidMorphism (ord_setoid P) (ord_setoid Q);
  ord_mono : ∀ x y, ord_le P x y → ord_le Q (ord_fn x) (ord_fn y)
}.

Arguments ord_fn {P Q} _.
Arguments ord_mono {P Q} _ _ _ _.

#[local] Obligation Tactic := idtac.

#[export]
Program Instance OrdHom_Setoid {P Q : OrdObject} : Setoid (OrdHom P Q) := {|
  equiv := fun f g => ∀ a, ord_fn f a ≈ ord_fn g a
|}.
Next Obligation.
  intros P Q. constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a;
    transitivity (ord_fn g a); [apply Hfg|apply Hgh].
Qed.

Program Definition ord_hom_id {P : OrdObject} : OrdHom P P := {|
  ord_fn := setoid_morphism_id
|}.
Next Obligation. intros P x y H; exact H. Qed.

Program Definition ord_hom_compose {P Q R : OrdObject}
        (g : OrdHom Q R) (f : OrdHom P Q) : OrdHom P R := {|
  ord_fn := setoid_morphism_compose (ord_fn g) (ord_fn f)
|}.
Next Obligation.
  intros P Q R g f x y H; simpl.
  apply (ord_mono g), (ord_mono f); exact H.
Qed.

Program Instance ord_hom_compose_respects {P Q R : OrdObject} :
  Proper (equiv ==> equiv ==> equiv) (@ord_hom_compose P Q R).
Next Obligation.
  intros P Q R g g' Hg f f' Hf a; simpl.
  transitivity (ord_fn g (ord_fn f' a)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category *)

Program Definition Ord : Category := {|
  obj     := OrdObject;
  hom     := OrdHom;
  homset  := @OrdHom_Setoid;
  id      := @ord_hom_id;
  compose := @ord_hom_compose;
  compose_respects := @ord_hom_compose_respects
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

Program Definition Ord_Forget : Ord ⟶ Sets := {|
  fobj := fun P => ord_setoid P;
  fmap := fun _ _ f => ord_fn f
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

(** ** Partial orders as a full subcategory *)

Definition OrdAntisymmetric (P : OrdObject) : Type :=
  ∀ x y : carrier (ord_setoid P),
    ord_le P x y → ord_le P y x → x ≈ y.

Definition Pos_Sub : Subcategory Ord :=
  @Build_Subcategory Ord
    OrdAntisymmetric
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Posets : Category := Sub Ord Pos_Sub.

Lemma Pos_Sub_Full :
  Category.Construction.Subcategory.Full Ord Pos_Sub.
Proof. intros x y ox oy g; exact I. Defined.

Lemma Posets_Incl_Full : Functor.Full (Incl Ord Pos_Sub).
Proof. exact (Full_Implies_Full_Functor Ord Pos_Sub Pos_Sub_Full). Defined.

Lemma Posets_Incl_Faithful : Functor.Faithful (Incl Ord Pos_Sub).
Proof. exact (Incl_Faithful Ord Pos_Sub). Defined.

(** ** Comparison with the pre-existing [Pos] *)

Definition OrdObject_of_Poset (P : PosetObject) : OrdObject := {|
  ord_setoid      := pos_setoid P;
  ord_le          := pos_le P;
  ord_le_respects := pos_le_respects P;
  ord_refl        := pos_refl P;
  ord_trans       := pos_trans P
|}.

Definition Poset_of_antisym (P : OrdObject) (H : OrdAntisymmetric P)
  : PosetObject := {|
  pos_setoid      := ord_setoid P;
  pos_le          := ord_le P;
  pos_le_respects := ord_le_respects P;
  pos_refl        := ord_refl P;
  pos_trans       := ord_trans P;
  pos_antisym     := H
|}.

Example poset_ord_poset_round (P : PosetObject) :
  Poset_of_antisym (OrdObject_of_Poset P) (pos_antisym P) = P := eq_refl.

Example ord_poset_ord_round (P : OrdObject) (H : OrdAntisymmetric P) :
  OrdObject_of_Poset (Poset_of_antisym P H) = P := eq_refl.

Definition OrdHom_of_MonoHom {P Q : PosetObject} (f : MonoHom P Q)
  : OrdHom (OrdObject_of_Poset P) (OrdObject_of_Poset Q) :=
  @Build_OrdHom (OrdObject_of_Poset P) (OrdObject_of_Poset Q)
    (mono_fn f) (mono_le f).

Definition MonoHom_of_OrdHom {P Q : OrdObject}
    (HP : OrdAntisymmetric P) (HQ : OrdAntisymmetric Q) (f : OrdHom P Q)
  : MonoHom (Poset_of_antisym P HP) (Poset_of_antisym Q HQ) :=
  @Build_MonoHom (Poset_of_antisym P HP) (Poset_of_antisym Q HQ)
    (ord_fn f) (ord_mono f).

Program Definition Pos_to_Posets : Pos ⟶ Posets := {|
  fobj := fun P => (OrdObject_of_Poset P; pos_antisym P);
  fmap := fun _ _ f => (OrdHom_of_MonoHom f; I)
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

Program Definition Posets_to_Pos : Posets ⟶ Pos := {|
  fobj := fun x => Poset_of_antisym `1 x `2 x;
  fmap := fun x y f => MonoHom_of_OrdHom `2 x `2 y `1 f
|}.
Next Obligation. intros x y f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros x a; simpl; reflexivity. Qed.
Next Obligation. intros x y z f g a; simpl; reflexivity. Qed.

Example pos_to_posets_obj (P : PosetObject) :
  `1 (fobj[Pos_to_Posets] P) = OrdObject_of_Poset P := eq_refl.

Example posets_to_pos_obj (x : Posets) :
  fobj[Posets_to_Pos] x = Poset_of_antisym `1 x `2 x := eq_refl.

Example pos_roundtrip_obj (P : PosetObject) :
  fobj[Posets_to_Pos] (fobj[Pos_to_Posets] P) = P := eq_refl.

Example pos_roundtrip_map (P Q : PosetObject) (f : MonoHom P Q)
    (a : carrier (pos_setoid P)) :
  mono_fn (fmap[Posets_to_Pos] (fmap[Pos_to_Posets] f)) a = mono_fn f a
  := eq_refl.

Lemma posets_pos_posets_obj (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x.
Proof. destruct x as [P HP]; exact eq_refl. Defined.

Program Definition Pos_Posets_strict_iso :
  @Isomorphism StrictCat Pos Posets := {|
  to   := Pos_to_Posets;
  from := Posets_to_Pos
|}.
Next Obligation.
  exists posets_pos_posets_obj.
  intros x y f; destruct x as [P HP], y as [Q HQ]; simpl.
  intro a; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun P : PosetObject => eq_refl).
  intros P Q f a; simpl; reflexivity.
Qed.

(** ** A preorder as a thin category, and the reviewer's distinction *)

Definition ord_preorder (P : OrdObject)
  : RelationClasses.PreOrder (ord_le P).
Proof.
  constructor.
  - exact (ord_refl P).
  - intros x y z f g; exact (ord_trans P x y z f g).
Defined.

Definition OrdAsCategory (P : OrdObject) : Category :=
  Proset (ord_preorder P).

Program Definition OrdHomAsFunctor {P Q : OrdObject} (f : OrdHom P Q)
  : OrdAsCategory P ⟶ OrdAsCategory Q := {|
  fobj := fun x => ord_fn f x;
  fmap := fun x y h => ord_mono f x y h
|}.
Next Obligation. intros P Q f x y g h Hgh; exact I. Qed.
Next Obligation. intros P Q f x; exact I. Qed.
Next Obligation. intros P Q f x y z g h; exact I. Qed.

Example ord_functor_fobj {P Q : OrdObject} (f : OrdHom P Q)
    (x : carrier (ord_setoid P)) :
  fobj[OrdHomAsFunctor f] x = ord_fn f x := eq_refl.

Example Ord_obj_are_preorders : obj[Ord] = OrdObject := eq_refl.

Example OrdAsCategory_obj_are_points (P : OrdObject) :
  obj[OrdAsCategory P] = carrier (ord_setoid P) := eq_refl.
