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

(* * * Two 函子 same 对象 function, over groups （已译） *)

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

(* 相关说明。 （已译） *)
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

(* THE DEGENERACY CHECK, PROVED. Over abelian group every conjugation
 恒等 态射, so twist inner automorphism there is
 恒等 函子 separates nothing. （已译） *)
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

(* 相关说明。 （已译） *)
Example Z2_conj_trivial (t : carrier Z2) : Grp_conj Z2 t ≈ @id Grp Z2.
Proof.
  apply Grp_conj_abelian.
  intros a b; simpl.
  now destruct a, b.
Qed.

(* 相关说明。 （已译） *)

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

(*
   本节说明 TwoFunctors 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition S3carrier : Type := (rot * bool)%type.

Definition s3_mul (p q : S3carrier) : S3carrier :=
  (rot_add (fst p) (if snd p then rot_neg (fst q) else fst q),
   xorb (snd p) (snd q)).

Definition s3_inv (p : S3carrier) : S3carrier :=
  if snd p then p else (rot_neg (fst p), false).

Definition s3_unit : S3carrier := (rot0, false).

Program Definition s3_setoid : Setoid S3carrier := {| equiv := @eq S3carrier |}.

(* 相关说明。 （已译） *)
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

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example S3_equiv_is_eq (a b : carrier S3) (H : a ≈ b) : a = b := H.
Example S3_eq_is_equiv (a b : carrier S3) (H : a = b) : a ≈ b := H.

(* The rotation and the reflection. *)
Definition S3_r : carrier S3 := (rot1, false).
Definition S3_s : carrier S3 := (rot0, true).

(* 相关说明。 （已译） *)
Lemma S3_nonabelian :
  grp_mul S3 S3_r S3_s ≈ grp_mul S3 S3_s S3_r → False.
Proof. simpl; discriminate. Qed.

(* Consequently conjugation reflection not 恒等: it
 inverts rotation. （已译） *)
Lemma S3_conj_s_nontrivial : Grp_conj S3 S3_s ≈ @id Grp S3 → False.
Proof.
  intro H.
  pose proof (H S3_r) as Hr.
  simpl in Hr.
  discriminate.
Qed.

(* 相关说明。 （已译） *)

(* One 对象, whose endomorphism 幺半群 [Grp] supplies 态射;
 范畴 laws those [Grp] at 对象 G. （已译） *)
Program Definition GrpAt (G : GrpObject) : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => G ~{Grp}~> G;
  homset  := fun _ _ => @homset Grp G G;
  id      := fun _ => @id Grp G;
  compose := fun _ _ _ f g => f ∘ g
|}.
(* [compose_respects] discharged typeclass resolution [Grp]'s own
 instance; four remaining obligations 范畴 laws, are
 [Grp]'s laws at 对象 G. （已译） *)
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

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma GrpAt_Incl_injective_on_objects (G : GrpObject) (x y : GrpAt G) :
  fobj[GrpAt_Incl G] x = fobj[GrpAt_Incl G] y → x = y.
Proof.
  intros _.
  destruct x, y.
  reflexivity.
Qed.

(* An 同构 G itself [Grp] one [GrpAt G]: the
 态射, 复合, 恒等 hom-setoids agree definitionally. （已译） *)
Definition GrpAt_iso {G : GrpObject} (i : @Isomorphism Grp G G)
  (x : GrpAt G) : @Isomorphism (GrpAt G) x x :=
  @Build_Isomorphism (GrpAt G) x x (to i) (from i)
    (iso_to_from i) (iso_from_to i).

(* Uniqueness 恒等 proofs single 对象, Hedberg the
 (trivially) decidable equality [poly_unit]. （已译） *)
Definition poly_unit_eq_dec (x y : poly_unit) : {x = y} + {x <> y} :=
  left (match x, y with ttt, ttt => eq_refl end).

(** ** The two functors *)

(* The twist 恒等 函子 full subcategory S3 by
 conjugation reflection. （已译） *)
Definition S3_twist_family : ∀ x : GrpAt S3, x ≅ x :=
  GrpAt_iso (Grp_conj_iso S3 S3_s).

Definition S3_Twist : GrpAt S3 ⟶ GrpAt S3 :=
  Twist (@Id (GrpAt S3)) S3_twist_family.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma S3_Twist_fobj (x : GrpAt S3) : fobj[S3_Twist] x = fobj[@Id (GrpAt S3)] x.
Proof. reflexivity. Qed.

(* Indeed 对象 functions agree FUNCTIONS, not merely pointwise:
 both [fun x => x] after unfolding. （已译） *)
Example S3_Twist_object_function :
  fobj[S3_Twist] = fobj[@Id (GrpAt S3)].
Proof. reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition S3_conj_r : ttt ~{GrpAt S3}~> ttt := Grp_conj S3 S3_r.

(* The concrete separating datum: at 态射, two 函子 take
 different values reflection. （已译） *)
Example S3_twist_value :
  grp_map (fmap[S3_Twist] S3_conj_r) S3_s ≈ (rot1, true).
Proof. reflexivity. Qed.

Example S3_id_value :
  grp_map (fmap[@Id (GrpAt S3)] S3_conj_r) S3_s ≈ (rot2, true).
Proof. reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_twist_differs_on_conj_r :
  fmap[S3_Twist] S3_conj_r
    ≈ fmap[@Id (GrpAt S3)] S3_conj_r → False.
Proof.
  intro H.
  pose proof (H S3_s) as Hs.
  simpl in Hs.
  discriminate.
Qed.

(*
   本节说明 TwoFunctors 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma S3_conj_not_central :
  S3_twist_family ttt ∘ S3_conj_r
    ≈ fmap[@Id (GrpAt S3)] S3_conj_r ∘ S3_twist_family ttt → False.
Proof.
  intro H.
  pose proof (H S3_s) as Hs.
  simpl in Hs.
  discriminate.
Qed.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_two_functors_distinct :
  @equiv _ Functor_StrictEq_Setoid S3_Twist (@Id (GrpAt S3)) → False.
Proof.
  unfold S3_Twist.
  exact (Twist_not_strict_id (@Id (GrpAt S3)) S3_twist_family
           (uip_of_dec poly_unit_eq_dec) (x:=ttt) (y:=ttt)
           (f:=S3_conj_r) S3_conj_not_central).
Qed.

(* And they IDENTIFIED weak setoid, hom-setoid [Cat]:
 conjugation family itself natural 同构. This why
 statement above has made strictly. （已译） *)
Theorem S3_two_functors_weakly_equal :
  @equiv _ Functor_Setoid S3_Twist (@Id (GrpAt S3)).
Proof. exact (Twist_Id_weak_equiv S3_twist_family). Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example S3_pair_equal_in_Cat :
  @equiv _ (@homset Cat (GrpAt S3) (GrpAt S3)) S3_Twist (@Id (GrpAt S3)).
Proof. exact S3_two_functors_weakly_equal. Qed.

Theorem S3_pair_distinct_in_StrictCat :
  @equiv _ (@homset StrictCat (GrpAt S3) (GrpAt S3))
    S3_Twist (@Id (GrpAt S3)) → False.
Proof. exact S3_two_functors_distinct. Qed.

(* 相关说明。 （已译） *)

(* Inversion 同构 group opposite
 (Instance/Grp.v); both round trips [grp_inv_inv]. （已译） *)
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

(* Twisting opposite-group 函子 inversion gives 自函子 of
 WHOLE [Grp] whose 对象 function 恒等 -- shape
 Mac Lane's exercise asks for. （已译） *)
Definition Grp_op_twist : Grp ⟶ Grp := Twist Grp_Op Grp_inv_iso.

Lemma Grp_op_twist_fobj (G : Grp) : fobj[Grp_op_twist] G = G.
Proof. reflexivity. Qed.

Example Grp_op_twist_object_function : fobj[Grp_op_twist] = fobj[@Id Grp].
Proof. reflexivity. Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Grp_op_twist_is_Id :
  @equiv _ Functor_StrictEq_Setoid Grp_op_twist (@Id Grp).
Proof.
  apply Twist_natural_strict_id.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.
