Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Twist.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(** * Two functors with the same object function, over groups *)

(*
 nLab: https://ncatlab.org/nlab/show/functor
 nLab: https://ncatlab.org/nlab/show/inner+automorphism

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** Inner automorphisms *)

(* Conjugation by t is a group homomorphism: t(ab)t⁻¹ collapses to
   (tat⁻¹)(tbt⁻¹) once the inner t⁻¹t is cancelled. *)
Definition Grp_conj (G : GrpObject) (t : carrier G) : G ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G G
       {| morphism := fun a => grp_mul G (grp_mul G t a) (grp_inv G t) |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - simpl.
    rewrite grp_mul_unit_r.
    apply grp_mul_inv_r.
  - intros a b; simpl.
    rewrite (grp_mul_assoc G (grp_mul G t a) (grp_inv G t)
               (grp_mul G (grp_mul G t b) (grp_inv G t))).
    rewrite <- (grp_mul_assoc G (grp_inv G t) (grp_mul G t b) (grp_inv G t)).
    rewrite <- (grp_mul_assoc G (grp_inv G t) t b).
    rewrite grp_mul_inv_l.
    rewrite grp_mul_unit_l.
    rewrite <- (grp_mul_assoc G (grp_mul G t a) b (grp_inv G t)).
    rewrite (grp_mul_assoc G t a b).
    reflexivity.
Defined.

(* Conjugation by t and by t⁻¹ are mutually inverse, so conjugation is an
   automorphism -- an INNER automorphism of G. *)
Definition Grp_conj_iso (G : GrpObject) (t : carrier G) :
  @Isomorphism Grp G G.
Proof.
  unshelve notypeclasses refine
    (@Build_Isomorphism Grp G G (Grp_conj G t) (Grp_conj G (grp_inv G t)) _ _).
  - intro a; simpl.
    unfold Basics.compose; simpl.
    rewrite grp_inv_inv.
    rewrite <- (grp_mul_assoc G t (grp_mul G (grp_inv G t) a) t).
    rewrite <- (grp_mul_assoc G t (grp_inv G t) a).
    rewrite grp_mul_inv_r.
    rewrite grp_mul_unit_l.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_r.
  - intro a; simpl.
    unfold Basics.compose; simpl.
    rewrite grp_inv_inv.
    rewrite <- (grp_mul_assoc G (grp_inv G t) (grp_mul G t a) (grp_inv G t)).
    rewrite <- (grp_mul_assoc G (grp_inv G t) t a).
    rewrite grp_mul_inv_l.
    rewrite grp_mul_unit_l.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_r.
Defined.

(* THE DEGENERACY CHECK, PROVED.  Over an abelian group every conjugation
   is the identity morphism, so a twist by an inner automorphism there is
   the identity functor and separates nothing. *)
Lemma Grp_conj_abelian (G : GrpObject)
  (comm : ∀ a b : carrier G, grp_mul G a b ≈ grp_mul G b a)
  (t : carrier G) : Grp_conj G t ≈ @id Grp G.
Proof.
  intro a; simpl.
  rewrite (comm t a).
  rewrite grp_mul_assoc.
  rewrite grp_mul_inv_r.
  apply grp_mul_unit_r.
Qed.

(* The in-tree abelian witness is Z/2, and it does collapse. *)
Example Z2_conj_trivial (t : carrier Z2) : Grp_conj Z2 t ≈ @id Grp Z2.
Proof.
  apply Grp_conj_abelian.
  intros a b; simpl.
  now destruct a, b.
Qed.

(** ** The symmetric group on three letters *)

(* Z/3, written additively, as the rotation part. *)
Inductive rot : Type := rot0 | rot1 | rot2.

Definition rot_add (a b : rot) : rot :=
  match a, b with
  | rot0, rot0 => rot0 | rot0, rot1 => rot1 | rot0, rot2 => rot2
  | rot1, rot0 => rot1 | rot1, rot1 => rot2 | rot1, rot2 => rot0
  | rot2, rot0 => rot2 | rot2, rot1 => rot0 | rot2, rot2 => rot1
  end.

Definition rot_neg (a : rot) : rot :=
  match a with rot0 => rot0 | rot1 => rot2 | rot2 => rot1 end.

(* An element of S3 is a pair (i, b): the rotation r^i followed by the
   reflection s^b.  Multiplication is the semidirect product rule
   r^i s^b · r^j s^c = r^(i ± j) s^(b+c), the sign being negative exactly
   when b is the reflection -- this is s r s⁻¹ = r⁻¹. *)
Definition S3carrier : Type := (rot * bool)%type.

Definition s3_mul (p q : S3carrier) : S3carrier :=
  (rot_add (fst p) (if snd p then rot_neg (fst q) else fst q),
   xorb (snd p) (snd q)).

Definition s3_inv (p : S3carrier) : S3carrier :=
  if snd p then p else (rot_neg (fst p), false).

Definition s3_unit : S3carrier := (rot0, false).

Program Definition s3_setoid : Setoid S3carrier := {| equiv := @eq S3carrier |}.

(* Every law is a finite check: associativity is 216 cases, the unit and
   inverse laws 6 each. *)
Definition S3 : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := S3carrier ; is_setoid := s3_setoid |};
    grp_unit := s3_unit;
    grp_mul  := s3_mul;
    grp_inv  := s3_inv;
    (* [s3_setoid]'s `≈` is [@eq S3carrier], already a [Prop]. *)
    grp_prop := eq_PropEquiv S3carrier
  |}.
  - intros x y Hxy u v Huv; simpl in *; subst; reflexivity.
  - intros [i b] [j c] [k d]; destruct i, j, k, b, c, d; reflexivity.
  - intros [j c]; destruct j, c; reflexivity.
  - intros [j c]; destruct j, c; reflexivity.
Defined.

(* The setoid of S3 IS propositional equality, in both directions.  This is
   what licenses closing the distinctness arguments below by [discriminate]
   on carrier elements: the refuted statement is the hom-setoid equation
   itself. *)
Example S3_equiv_is_eq (a b : carrier S3) (H : a ≈ b) : a = b := H.
Example S3_eq_is_equiv (a b : carrier S3) (H : a = b) : a ≈ b := H.

(* The rotation and the reflection. *)
Definition S3_r : carrier S3 := (rot1, false).
Definition S3_s : carrier S3 := (rot0, true).

(* S3 is nonabelian: r * s and s * r are different reflections. *)
Lemma S3_nonabelian :
  grp_mul S3 S3_r S3_s ≈ grp_mul S3 S3_s S3_r → False.
Proof. simpl; discriminate. Qed.

(* Consequently conjugation by the reflection is not the identity: it
   inverts the rotation. *)
Lemma S3_conj_s_nontrivial : Grp_conj S3 S3_s ≈ @id Grp S3 → False.
Proof.
  intro H.
  pose proof (H S3_r) as Hr.
  simpl in Hr.
  discriminate.
Qed.

(** ** The full subcategory of Grp on a single group *)

(* One object, whose endomorphism monoid in [Grp] supplies the morphisms;
   the category laws are those of [Grp] at the object G. *)
Program Definition GrpAt (G : GrpObject) : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => G ~{Grp}~> G;
  homset  := fun _ _ => @homset Grp G G;
  id      := fun _ => @id Grp G;
  compose := fun _ _ _ f g => f ∘ g
|}.
(* [compose_respects] is discharged by typeclass resolution from [Grp]'s own
   instance; the four remaining obligations are the category laws, which are
   [Grp]'s laws at the object G. *)
Next Obligation.
  intros G x y f.
  apply id_left.
Qed.
Next Obligation.
  intros G x y f.
  apply id_right.
Qed.
Next Obligation.
  intros G x y z w f g h.
  apply comp_assoc.
Qed.
Next Obligation.
  intros G x y z w f g h.
  apply comp_assoc_sym.
Qed.

(* The inclusion into [Grp]. *)
Program Definition GrpAt_Incl (G : GrpObject) : GrpAt G ⟶ Grp := {|
  fobj := fun _ => G;
  fmap := fun _ _ f => f
|}.
Next Obligation.
  intros G x y f g Hfg.
  exact Hfg.
Qed.
Next Obligation.
  intros G x.
  reflexivity.
Qed.
Next Obligation.
  intros G x y z f g.
  reflexivity.
Qed.

#[export] Program Instance GrpAt_Incl_Full (G : GrpObject) :
  Full (GrpAt_Incl G) := {|
  prefmap := fun _ _ g => g
|}.
Next Obligation.
  intros G x y g.
  reflexivity.
Qed.

#[export] Program Instance GrpAt_Incl_Faithful (G : GrpObject) :
  Faithful (GrpAt_Incl G).
Next Obligation.
  intros G x y f g Hfg.
  exact Hfg.
Qed.

(* The object map is injective, so [GrpAt G] is a subcategory of [Grp] in
   the strict sense of the word and not merely a category mapping into it.
   NOTE HOW LITTLE THIS COSTS, since an audit rightly asked: the object
   type of [GrpAt G] is [poly_unit], so any two objects are equal and the
   injectivity hypothesis is discarded outright; fullness and faithfulness
   are definitional too, the hom-type being [Grp]'s own on the nose.  All
   three are worth stating -- they are what "full subcategory" means, and
   this development has been strict about the word -- but none of the
   three has content.  What follows;
   with fullness and faithfulness above, it is the full subcategory on G. *)
Lemma GrpAt_Incl_injective_on_objects (G : GrpObject) (x y : GrpAt G) :
  fobj[GrpAt_Incl G] x = fobj[GrpAt_Incl G] y → x = y.
Proof.
  intros _.
  destruct x, y.
  reflexivity.
Qed.

(* An isomorphism of G with itself in [Grp] is one in [GrpAt G]: the
   morphisms, composition, identity and hom-setoids agree definitionally. *)
Definition GrpAt_iso {G : GrpObject} (i : @Isomorphism Grp G G)
  (x : GrpAt G) : @Isomorphism (GrpAt G) x x :=
  @Build_Isomorphism (GrpAt G) x x (to i) (from i)
    (iso_to_from i) (iso_from_to i).

(* Uniqueness of identity proofs on the single object, by Hedberg from the
   (trivially) decidable equality of [poly_unit]. *)
Definition poly_unit_eq_dec (x y : poly_unit) : {x = y} + {x <> y} :=
  left (match x, y with ttt, ttt => eq_refl end).

(** ** The two functors *)

(* The twist of the identity functor of the full subcategory on S3 by
   conjugation with the reflection. *)
Definition S3_twist_family : ∀ x : GrpAt S3, x ≅ x :=
  GrpAt_iso (Grp_conj_iso S3 S3_s).

Definition S3_Twist : GrpAt S3 ⟶ GrpAt S3 :=
  Twist (@Id (GrpAt S3)) S3_twist_family.

(* Both functors have the identity object function, by computation.  The
   [=] here is on OBJECTS, where propositional equality is the right
   notion and the one [Functor_StrictEq_Setoid] itself uses; morphisms
   stay compared with ≈ throughout. *)
Lemma S3_Twist_fobj (x : GrpAt S3) : fobj[S3_Twist] x = fobj[@Id (GrpAt S3)] x.
Proof. reflexivity. Qed.

(* Indeed the object functions agree as FUNCTIONS, not merely pointwise:
   both are [fun x => x] after unfolding. *)
Example S3_Twist_object_function :
  fobj[S3_Twist] = fobj[@Id (GrpAt S3)].
Proof. reflexivity. Qed.

(* The separating morphism: the inner automorphism by the rotation, read as
   an endomorphism of the single object of [GrpAt S3].  The type ascription
   is what lets [fmap] find its source and target, since the hom-type of a
   one-object category does not mention them. *)
Definition S3_conj_r : ttt ~{GrpAt S3}~> ttt := Grp_conj S3 S3_r.

(* The concrete separating datum: at that morphism, the two functors take
   different values on the reflection. *)
Example S3_twist_value :
  grp_map (fmap[S3_Twist] S3_conj_r) S3_s ≈ (rot1, true).
Proof. reflexivity. Qed.

Example S3_id_value :
  grp_map (fmap[@Id (GrpAt S3)] S3_conj_r) S3_s ≈ (rot2, true).
Proof. reflexivity. Qed.

(* Hence the two arrow maps differ IN THE HOM-SETOID of [GrpAt S3], which
   is the hom-setoid of [Grp] at S3: two homomorphisms are equivalent there
   exactly when they agree at every element, and these disagree at [S3_s]. *)
Theorem S3_twist_differs_on_conj_r :
  fmap[S3_Twist] S3_conj_r
    ≈ fmap[@Id (GrpAt S3)] S3_conj_r → False.
Proof.
  intro H.
  pose proof (H S3_s) as Hs.
  simpl in Hs.
  discriminate.
Qed.

(* The naturality that breaks down: conjugation by the reflection does not
   commute with conjugation by the rotation, since S3 is nonabelian.  This
   is the single datum the separation rests on. *)
Lemma S3_conj_not_central :
  S3_twist_family ttt ∘ S3_conj_r
    ≈ fmap[@Id (GrpAt S3)] S3_conj_r ∘ S3_twist_family ttt → False.
Proof.
  intro H.
  pose proof (H S3_s) as Hs.
  simpl in Hs.
  discriminate.
Qed.

(* The two functors are distinct in the strict functor setoid.  The
   argument goes through the general criterion of Functor/Twist.v: a twist
   differs from the identity exactly where its family is not natural,
   the object components of a strict equality being collapsed to [eq_refl]
   by uniqueness of identity proofs on the single object. *)
Theorem S3_two_functors_distinct :
  @equiv _ Functor_StrictEq_Setoid S3_Twist (@Id (GrpAt S3)) → False.
Proof.
  unfold S3_Twist.
  exact (Twist_not_strict_id (@Id (GrpAt S3)) S3_twist_family
           (uip_of_dec poly_unit_eq_dec) (x:=ttt) (y:=ttt)
           (f:=S3_conj_r) S3_conj_not_central).
Qed.

(* And they are IDENTIFIED by the weak setoid, the hom-setoid of [Cat]:
   the conjugation family is itself the natural isomorphism.  This is why
   the statement above has to be made strictly. *)
Theorem S3_two_functors_weakly_equal :
  @equiv _ Functor_Setoid S3_Twist (@Id (GrpAt S3)).
Proof. exact (Twist_Id_weak_equiv S3_twist_family). Qed.

(* The same two statements read off the two categories of categories: the
   pair is one and the same morphism of [Cat], and two different morphisms
   of [StrictCat].  The hom-setoids are the two functor setoids on the
   nose, as Test/Issue138.v records. *)
Example S3_pair_equal_in_Cat :
  @equiv _ (@homset Cat (GrpAt S3) (GrpAt S3)) S3_Twist (@Id (GrpAt S3)).
Proof. exact S3_two_functors_weakly_equal. Qed.

Theorem S3_pair_distinct_in_StrictCat :
  @equiv _ (@homset StrictCat (GrpAt S3) (GrpAt S3))
    S3_Twist (@Id (GrpAt S3)) → False.
Proof. exact S3_two_functors_distinct. Qed.

(** ** The uniform candidate over all of Grp, and its collapse *)

(* Inversion as an isomorphism from a group to its opposite
   (Instance/Grp.v); both round trips are [grp_inv_inv]. *)
Definition Grp_inv_iso (G : GrpObject) : @Isomorphism Grp G (Grp_Op G).
Proof.
  unshelve notypeclasses refine
    (@Build_Isomorphism Grp G (Grp_Op G) (Grp_inv_to G) (Grp_inv_from G) _ _).
  - intro a; simpl.
    unfold Basics.compose.
    apply grp_inv_inv.
  - intro a; simpl.
    unfold Basics.compose.
    apply grp_inv_inv.
Defined.

(* Twisting the opposite-group functor by inversion gives an endofunctor of
   the WHOLE of [Grp] whose object function is the identity -- the shape
   Mac Lane's exercise asks for. *)
Definition Grp_op_twist : Grp ⟶ Grp := Twist Grp_Op Grp_inv_iso.

Lemma Grp_op_twist_fobj (G : Grp) : fobj[Grp_op_twist] G = G.
Proof. reflexivity. Qed.

Example Grp_op_twist_object_function : fobj[Grp_op_twist] = fobj[@Id Grp].
Proof. reflexivity. Qed.

(* But it is the identity functor, strictly: inversion is natural (that is
   [grp_map_inv], every homomorphism commutes with inversion), and a
   natural family produces nothing new ([Twist_natural_strict_id]).  So
   this candidate -- a family of isomorphisms available uniformly at every
   group, and the one the tree already builds as [Grp_op_Isomorphism]
   (Instance/Grp.v) -- does not answer the exercise, and the file does
   not pretend otherwise. *)
Theorem Grp_op_twist_is_Id :
  @equiv _ Functor_StrictEq_Setoid Grp_op_twist (@Id Grp).
Proof.
  apply Twist_natural_strict_id.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.
