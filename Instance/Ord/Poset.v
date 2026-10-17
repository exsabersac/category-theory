(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出偏序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ord.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* 相关说明。 （已译） *)

Definition poset_refl_equiv (P : OrdObject)
    (x y : carrier (ord_setoid P)) : Prop :=
  ord_le P x y ∧ ord_le P y x.

#[local] Obligation Tactic := idtac.

Program Definition poset_refl_setoid (P : OrdObject)
  : Setoid (carrier (ord_setoid P)) := {|
  equiv := poset_refl_equiv P
|}.
Next Obligation.
  intro P; constructor.
  - intro x; split; apply ord_refl.
  - intros x y [Hxy Hyx]; split; assumption.
  - intros x y z [Hxy Hyx] [Hyz Hzy]; split.
    + exact (ord_trans P x y z Hxy Hyz).
    + exact (ord_trans P z y x Hzy Hyx).
Qed.

Definition poset_refl_carrier (P : OrdObject) : SetoidObject := {|
  carrier   := carrier (ord_setoid P);
  is_setoid := poset_refl_setoid P
|}.

Program Definition PosetReflection (P : OrdObject) : OrdObject := {|
  ord_setoid := poset_refl_carrier P;
  ord_le     := ord_le P;
  ord_refl   := ord_refl P;
  ord_trans  := ord_trans P
|}.
Next Obligation.
  intros P x x' [Hxx' Hx'x] y y' [Hyy' Hy'y]; split; intro H.
  - exact (ord_trans P x' x y' Hx'x (ord_trans P x y y' H Hyy')).
  - exact (ord_trans P x x' y Hxx' (ord_trans P x' y' y H Hy'y)).
Qed.

(** Antisymmetry reflection DEFINITION [≈]: two
 order proofs handed ARE pair coarser 等价 asks for. （已译） *)
Lemma PosetReflection_Antisymmetric (P : OrdObject)
  : OrdAntisymmetric (PosetReflection P).
Proof. intros x y Hxy Hyx; split; assumption. Defined.

Definition PosetReflectionObj (P : OrdObject) : Posets :=
  (PosetReflection P; PosetReflection_Antisymmetric P).

Program Definition reflection_proj (P : OrdObject)
  : P ~{Ord}~> PosetReflection P :=
  @Build_OrdHom P (PosetReflection P)
    {| morphism := fun x : carrier (ord_setoid P) => x |} _.
Next Obligation.
  intros P x y Hxy; split; apply ord_le_of_equiv.
  - exact Hxy.
  - symmetry; exact Hxy.
Qed.
Next Obligation. intros P x y H; exact H. Qed.

(** ** The universal property *)

Program Definition poset_med {P D : OrdObject} (HD : OrdAntisymmetric D)
    (f : P ~{Ord}~> D) : PosetReflection P ~{Ord}~> D :=
  @Build_OrdHom (PosetReflection P) D
    {| morphism := fun x : carrier (ord_setoid P) => ord_fn f x |} _.
Next Obligation.
  intros P D HD f x y [Hxy Hyx]; simpl.
  exact (HD _ _ (ord_mono f x y Hxy) (ord_mono f y x Hyx)).
Qed.
Next Obligation. intros P D HD f x y H; exact (ord_mono f x y H). Qed.

Theorem poset_reflection_universal (P : OrdObject) :
  ∀ (d : Posets) (f : P ~{Ord}~> Incl Ord Pos_Sub d),
    ∃! g : PosetReflectionObj P ~{Posets}~> d,
      f ≈ fmap[Incl Ord Pos_Sub] g ∘ reflection_proj P.
Proof.
  intros d f.
  unshelve eexists.
  - exact (poset_med `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition poset_reflection_universal_arrow (P : OrdObject)
  : @UniversalArrow Ord Posets P (Incl Ord Pos_Sub) :=
  @universal_arrow_from_UMP Ord Posets P (Incl Ord Pos_Sub)
    (PosetReflectionObj P) (reflection_proj P)
    (poset_reflection_universal P).

Definition Poset_reflector : Ord ⟶ Posets :=
  LeftAdjointFunctorFromUniversalArrows (Incl Ord Pos_Sub)
    poset_reflection_universal_arrow.

Definition Poset_adj : Poset_reflector ⊣ Incl Ord Pos_Sub :=
  AdjunctionFromUniversalArrows (Incl Ord Pos_Sub)
    poset_reflection_universal_arrow.

Definition Poset_Reflective_in_Ord : Reflective Pos_Sub :=
  @Build_Reflective Ord Pos_Sub Pos_Sub_Full
    Poset_reflector Poset_adj.

(** ** Strict readbacks *)

Example poset_reflector_obj (P : OrdObject) :
  `1 (fobj[Poset_reflector] P) = PosetReflection P := eq_refl.

Example poset_arrow_is_proj (P : OrdObject) :
  @arrow Ord Posets P (Incl Ord Pos_Sub)
    (poset_reflection_universal_arrow P)
    = reflection_proj P := eq_refl.

Example poset_arrow_obj (P : OrdObject) :
  @arrow_obj Ord Posets P (Incl Ord Pos_Sub)
    (poset_reflection_universal_arrow P)
    = PosetReflectionObj P := eq_refl.

Definition poset_unit (P : OrdObject)
  : P ~{Ord}~> Incl Ord Pos_Sub (fobj[Poset_reflector] P) :=
  @Category.Theory.Adjunction.unit _ _ _ _ Poset_adj P.

Example poset_unit_is_proj (P : OrdObject)
    (x : carrier (ord_setoid P)) :
  ord_fn (poset_unit P) x = ord_fn (reflection_proj P) x := eq_refl.

Lemma poset_unit_is_proj_hom (P : OrdObject) :
  poset_unit P ≈ reflection_proj P.
Proof. intro a; reflexivity. Defined.

Example poset_reflection_carrier (P : OrdObject) :
  carrier (ord_setoid (PosetReflection P)) = carrier (ord_setoid P)
  := eq_refl.

Example poset_reflection_order (P : OrdObject) :
  ord_le (PosetReflection P) = ord_le P := eq_refl.

(** ** The counit at a partial order *)

Definition poset_reflect_iso (x : Posets) :
  fobj[Poset_reflector] (Incl Ord Pos_Sub x) ≅[Posets] x :=
  reflective_counit_iso Poset_Reflective_in_Ord x.

(** ** Non-vacuity: three preorders *)

(*
   本节说明 Poset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Chaos2 : OrdObject := {|
  ord_setoid := bool_setoid_object;
  ord_le     := fun _ _ => True
|}.
Next Obligation. intro x; exact I. Qed.
Next Obligation. intros x y z Hxy Hyz; exact I. Qed.

Lemma Chaos2_not_antisymmetric : OrdAntisymmetric Chaos2 → False.
Proof. intro H; exact (Bool.diff_true_false (H true false I I)). Qed.

Lemma chaos2_merges :
  (true : carrier (ord_setoid (PosetReflection Chaos2))) ≈ false.
Proof. split; exact I. Defined.

(** The naturals under [le]: already partial order, so reflection is
 inert it counit 同构 applies. （已译） *)
Program Definition NatLe : OrdObject := {|
  ord_setoid := {| carrier := nat ; is_setoid := eq_Setoid nat |};
  ord_le     := Nat.le
|}.
Next Obligation. intro x; apply Nat.le_refl. Qed.
Next Obligation. intros x y z Hxy Hyz; exact (Nat.le_trans _ _ _ Hxy Hyz). Qed.

Lemma NatLe_antisymmetric : OrdAntisymmetric NatLe.
Proof. intros x y Hxy Hyx; exact (Nat.le_antisymm x y Hxy Hyx). Qed.

Definition NatLePos : Posets := (NatLe; NatLe_antisymmetric).

Definition natle_reflect_iso :
  fobj[Poset_reflector] (Incl Ord Pos_Sub NatLePos) ≅[Posets] NatLePos :=
  poset_reflect_iso NatLePos.

Lemma natle_reflection_inert (x y : carrier (ord_setoid NatLe)) :
  (x : carrier (ord_setoid (PosetReflection NatLe))) ≈ y → x = y.
Proof. intros [Hxy Hyx]; exact (Nat.le_antisymm x y Hxy Hyx). Qed.

(** 本节：A MIXED preorder: two mutually related points one strictly above
 them. The reflection merges exactly pair keeps top apart. （已译） *)
Inductive MixPt : Set := mleft | mright | mtop.

Definition mix_le (x y : MixPt) : Prop :=
  match x, y with
  | mtop, mtop => True
  | mtop, _    => False
  | _, _       => True
  end.

Program Definition MixOrd : OrdObject := {|
  ord_setoid := {| carrier := MixPt ; is_setoid := eq_Setoid MixPt |};
  ord_le     := mix_le
|}.
Next Obligation. intro x; destruct x; exact I. Qed.
Next Obligation. intros x y z; destruct x, y, z; simpl; tauto. Qed.

Lemma MixOrd_not_antisymmetric : OrdAntisymmetric MixOrd → False.
Proof. intro H; discriminate (H mleft mright I I). Qed.

Lemma mix_merges :
  (mleft : carrier (ord_setoid (PosetReflection MixOrd))) ≈ mright.
Proof. split; exact I. Defined.

Lemma mix_top_stays_apart :
  (mleft : carrier (ord_setoid (PosetReflection MixOrd))) ≈ mtop → False.
Proof. intros [_ H]; exact H. Qed.

Lemma mix_proj_merges :
  ord_fn (reflection_proj MixOrd) mleft
    ≈ ord_fn (reflection_proj MixOrd) mright.
Proof. exact mix_merges. Defined.
