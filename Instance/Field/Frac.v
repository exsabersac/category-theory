Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Frac.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Notation num := Frac.num.

(*
   nLab: https://ncatlab.org/nlab/show/field+of+fractions
   nLab: https://ncatlab.org/nlab/show/universal+construction

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition field_dom (F : FieldObject) : DomObject := {|
  dom_ring       := field_ring F;
  dom_comm       := field_comm F;
  dom_nontrivial := field_one_neq_zero F
|}.
Next Obligation.
  intros F a b c Hc H.
  transitivity (rig_mul F (rig_mul F a c) (finv F c)).
  - rewrite rig_mul_assoc.
    rewrite (finv_r F c Hc).
    symmetry; apply rig_mul_one_r.
  - rewrite H.
    rewrite rig_mul_assoc.
    rewrite (finv_r F c Hc).
    apply rig_mul_one_r.
Qed.

(* * ** The 范畴 integral domains ALL homomorphisms （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Dom : Category := {|
  obj     := DomObject;
  hom     := fun D E => RigHom (dom_ring D) (dom_ring E);
  homset  := fun D E => @RigHom_Setoid (dom_ring D) (dom_ring E);
  id      := fun D => @rig_hom_id (dom_ring D);
  compose := fun _ _ _ f g => rig_hom_compose f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects _ _ _
|}.
Next Obligation. intros D E f a; simpl; reflexivity. Qed.
Next Obligation. intros D E f a; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h a; simpl; reflexivity. Qed.
Next Obligation. intros D E F G f g h a; simpl; reflexivity. Qed.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition IntDom_Dom : IntDom ⟶ Dom := {|
  fobj := fun D => D;
  fmap := fun _ _ f => dom_map f
|}.
Next Obligation. intros D E f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros D a; simpl; reflexivity. Qed.
Next Obligation. intros D E F f g a; simpl; reflexivity. Qed.

#[export] Instance IntDom_Dom_Faithful : Faithful IntDom_Dom.
Proof. constructor; intros D E f g H x; exact (H x). Qed.

(* * ** The forgetful 函子 ALL homomorphisms, unconditionally （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Field_Dom : Field ⟶ Dom := {|
  fobj := field_dom;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Dom_Faithful : Faithful Field_Dom.
Proof. constructor; intros F K f g H x; exact (H x). Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StableField_Sub : Subcategory Field :=
  @Build_Subcategory Field
    (fun F : FieldObject => FieldStableAtZero F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition StableField : Category := Sub Field StableField_Sub.

(* Full: every field homomorphism between selected objects is selected. *)
Lemma StableField_Full :
  Category.Construction.Subcategory.Full Field StableField_Sub.
Proof. intros F K oF oK g; exact I. Qed.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StableField_of_dec (F : FieldObject)
  (dec : ∀ a b : carrier (rig_setoid F), (a ≈ b) + (a ≈ b → False)) :
  StableField :=
  (F; field_stable_stable_at_zero F (field_dec_stable F dec)).

Definition Q_StableField : StableField := StableField_of_dec _ Q_Field_dec.

Definition F2_StableField : StableField := StableField_of_dec _ F2_Field_dec.

(* * ** The forgetful 函子 进入 范畴 MONOMORPHISMS （已译） *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition StableField_IntDom : StableField ⟶ IntDom := {|
  fobj := fun F => field_dom `1 F;
  fmap := fun F K f =>
    {| dom_map     := `1 f;
       dom_map_inj := field_stable_at_zero_suffices `1 f `2 F |}
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance StableField_IntDom_Faithful : Faithful StableField_IntDom.
Proof. constructor; intros F K f g H x; exact (H x). Qed.

(*
   本节说明函子、（余）强度、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Field_IntDom
  (stab : ∀ F : FieldObject, FieldStableAtZero F) : Field ⟶ IntDom := {|
  fobj := field_dom;
  fmap := fun F K f =>
    Build_DomHom (field_dom F) (field_dom K) f
      (field_stable_at_zero_suffices f (stab F))
|}.
Next Obligation. intros stab F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros stab F a; simpl; reflexivity. Qed.
Next Obligation. intros stab F K T f g a; simpl; reflexivity. Qed.

Example Field_IntDom_agrees_obj
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F : StableField) :
  Field_IntDom stab (Incl Field StableField_Sub F) = StableField_IntDom F
  := eq_refl.

Example Field_IntDom_agrees_map
  (stab : ∀ F : FieldObject, FieldStableAtZero F) (F K : StableField)
  (f : F ~{StableField}~> K) :
  fmap[Field_IntDom stab] (fmap[Incl Field StableField_Sub] f)
    ≈ fmap[StableField_IntDom] f.
Proof. intro a; simpl; reflexivity. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StableField_Dom : StableField ⟶ Dom :=
  Field_Dom ◯ Incl Field StableField_Sub.

Example StableField_IntDom_Dom_obj (F : StableField) :
  IntDom_Dom (StableField_IntDom F) = StableField_Dom F := eq_refl.

Example StableField_IntDom_Dom_map (F K : StableField) (f : F ~{StableField}~> K) :
  fmap[IntDom_Dom] (fmap[StableField_IntDom] f) = fmap[StableField_Dom] f
  := eq_refl.

(** ** Division in a field *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FieldArith.

Context (K : FieldObject).

Local Notation k0 := (rig_zero K).
Local Notation k1 := (rig_one K).
Local Infix "*" := (rig_mul K).
Local Infix "+" := (rig_add K).
Local Notation "/ x" := (finv K x).

Lemma kmulC (a b : carrier (rig_setoid K)) : a * b ≈ b * a.
Proof. apply field_comm. Qed.

Lemma kmulA (a b c : carrier (rig_setoid K)) : (a * b) * c ≈ a * (b * c).
Proof. apply rig_mul_assoc. Qed.

Lemma kmul_swap_r (a b c : carrier (rig_setoid K)) :
  (a * b) * c ≈ (a * c) * b.
Proof.
  rewrite kmulA, (kmulC b c), <- kmulA; reflexivity.
Qed.

Lemma kmul4_shuffle1 (a b c d : carrier (rig_setoid K)) :
  (a * b) * (c * d) ≈ (a * c) * (b * d).
Proof.
  rewrite kmulA, <- (kmulA b c d), (kmulC b c), (kmulA c b d), <- kmulA.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma field_mul_nonzero (a b : carrier (rig_setoid K)) :
  (a ≈ k0 → False) → (b ≈ k0 → False) → a * b ≈ k0 → False.
Proof. exact (dom_mul_nonzero (field_dom K) a b). Qed.

Lemma finv_one : / k1 ≈ k1.
Proof.
  rewrite <- (rig_mul_one_r K (/ k1)).
  apply finv_l, (field_one_neq_zero K).
Qed.

(* (a/b)·b ≈ a. *)
Lemma field_div_elim (a b : carrier (rig_setoid K)) (Hb : b ≈ k0 → False) :
  (a * / b) * b ≈ a.
Proof.
  rewrite kmulA.
  rewrite (kmulC (/ b) b).
  rewrite (finv_r K b Hb).
  apply rig_mul_one_r.
Qed.

(* To prove q ≈ a/b it is enough to clear the denominator. *)
Lemma field_div_intro (q a b : carrier (rig_setoid K)) (Hb : b ≈ k0 → False) :
  q * b ≈ a → q ≈ a * / b.
Proof.
  intro H.
  transitivity ((q * b) * / b).
  - rewrite kmulA, (finv_r K b Hb).
    symmetry; apply rig_mul_one_r.
  - now rewrite H.
Qed.

(* Cross-multiplication decides equality of quotients. *)
Lemma field_div_eq (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  a * d ≈ c * b → a * / b ≈ c * / d.
Proof.
  intro H.
  apply (field_div_intro _ _ _ Hd).
  rewrite kmul_swap_r.
  rewrite H.
  rewrite kmulA.
  rewrite (finv_r K b Hb).
  apply rig_mul_one_r.
Qed.

Lemma field_div_add (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  a * / b + c * / d ≈ (a * d + c * b) * / (b * d).
Proof.
  apply (field_div_intro _ _ _ (field_mul_nonzero b d Hb Hd)).
  rewrite rig_distr_r.
  apply rig_add_respects.
  - rewrite <- kmulA.
    rewrite (field_div_elim a b Hb).
    reflexivity.
  - rewrite (kmulC b d), <- kmulA.
    rewrite (field_div_elim c d Hd).
    reflexivity.
Qed.

Lemma field_div_mul (a b c d : carrier (rig_setoid K))
  (Hb : b ≈ k0 → False) (Hd : d ≈ k0 → False) :
  (a * / b) * (c * / d) ≈ (a * c) * / (b * d).
Proof.
  apply (field_div_intro _ _ _ (field_mul_nonzero b d Hb Hd)).
  rewrite kmul4_shuffle1.
  rewrite (field_div_elim a b Hb).
  rewrite (field_div_elim c d Hd).
  reflexivity.
Qed.

End FieldArith.

(* 相关说明。 （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FracExtension.

Context (D : DomObject).
Context (K : FieldObject).
Context (f : DomHom D (field_dom K)).

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma frac_hom_den_nonzero (x : frac_carrier D) :
  dom_map f (den D x) ≈ rig_zero K → False.
Proof.
  intro H.
  apply (den_nonzero D x).
  apply (dom_map_inj f).
  rewrite H.
  symmetry.
  apply (rig_map_zero (dom_map f)).
Qed.

(* n/d ↦ f n · (f d)⁻¹. *)
Definition frac_extend_map (x : frac_carrier D) : carrier (rig_setoid K) :=
  rig_mul K (dom_map f (num D x)) (finv K (dom_map f (den D x))).

Program Definition frac_extend : RigHom (FracRing D) (field_ring K) := {|
  rig_map := {| morphism := frac_extend_map |}
|}.
Next Obligation.
  intros x y Hxy; unfold frac_extend_map.
  apply (field_div_eq K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
  rewrite <- !(rig_map_mul (dom_map f)).
  exact (proper_morphism (rig_map (dom_map f)) _ _ Hxy).
Qed.
Next Obligation.
  unfold frac_extend_map, frac_zero, Frac.num, Frac.den, mk_frac; simpl.
  rewrite (rig_map_zero (dom_map f)).
  apply rig_mul_zero_l.
Qed.
Next Obligation.
  intros x y.
  unfold frac_extend_map, frac_add, Frac.num, Frac.den, mk_frac; simpl.
  rewrite (rig_map_add (dom_map f)).
  rewrite !(rig_map_mul (dom_map f)).
  symmetry.
  apply (field_div_add K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
Qed.
Next Obligation.
  unfold frac_extend_map, frac_one, Frac.num, Frac.den, mk_frac; simpl.
  rewrite !(rig_map_one (dom_map f)).
  apply finv_r, (field_one_neq_zero K).
Qed.
Next Obligation.
  intros x y.
  unfold frac_extend_map, frac_mul, Frac.num, Frac.den, mk_frac; simpl.
  rewrite !(rig_map_mul (dom_map f)).
  symmetry.
  apply (field_div_mul K _ _ _ _
           (frac_hom_den_nonzero x) (frac_hom_den_nonzero y)).
Qed.

(* 相关说明。 （已译） *)
Lemma frac_extend_embed (a : carrier (rig_setoid D)) :
  frac_extend (frac_embed D a) ≈ dom_map f a.
Proof.
  unfold frac_extend, frac_extend_map, frac_embed, Frac.num, Frac.den, mk_frac;
    simpl.
  rewrite (rig_map_one (dom_map f)).
  rewrite (finv_one K).

  apply rig_mul_one_r.
Qed.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma frac_embed_den (x : frac_carrier D) :
  rig_mul (FracRing D) (frac_embed D (den D x)) x ≈ frac_embed D (num D x).
Proof.
  simpl; unfold frac_eq, frac_mul, Frac.num, Frac.den, mk_frac; simpl.
  rewrite rig_mul_one_r.
  rewrite rig_mul_one_l.
  apply dom_comm.
Qed.

Lemma frac_extend_unique (g : RigHom (FracRing D) (field_ring K))
  (Hg : ∀ a, rig_map g (frac_embed D a) ≈ dom_map f a) (x : frac_carrier D) :
  rig_map g x ≈ frac_extend x.
Proof.
  (* g 恒等 above, embedding legs replaced f （已译） *)
  assert (Hgx : rig_mul K (dom_map f (den D x)) (rig_map g x)
                  ≈ dom_map f (num D x)).
  { transitivity (rig_map g (rig_mul (FracRing D) (frac_embed D (den D x)) x)).
    - rewrite (rig_map_mul g).
      rewrite (Hg (den D x)).
      reflexivity.
    - rewrite (proper_morphism (rig_map g) _ _ (frac_embed_den x)).
      apply Hg. }
  unfold frac_extend, frac_extend_map; simpl.
  apply (field_div_intro K _ _ _ (frac_hom_den_nonzero x)).
  rewrite (field_comm K).
  exact Hgx.
Qed.

End FracExtension.

(* * ** The 普遍映射性质, over EVERY field （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem frac_ump (D : DomObject) (K : FieldObject) (f : DomHom D (field_dom K)) :
  ∃! g : RigHom (FracRing D) (field_ring K),
    ∀ a : carrier (rig_setoid D), rig_map g (frac_embed D a) ≈ dom_map f a.
Proof.
  unshelve esplit.
  - exact (frac_extend D K f).
  - exact (frac_extend_embed D K f).
  - intros g Hg x; symmetry; exact (frac_extend_unique D K f g Hg x).
Qed.

(* 相关说明。 （已译） *)

Lemma frac_eq_zero (D : DomObject) (x : frac_carrier D) :
  frac_eq D x (frac_zero D) → num D x ≈ rig_zero D.
Proof.
  unfold frac_eq, frac_zero, Frac.num, Frac.den, mk_frac; simpl; intro H.
  rewrite <- (rig_mul_one_r D (fst `1 x)).
  rewrite H.
  apply rig_mul_zero_l.
Qed.

Lemma frac_zero_eq (D : DomObject) (x : frac_carrier D) :
  num D x ≈ rig_zero D → frac_eq D x (frac_zero D).
Proof.
  unfold frac_eq, frac_zero, Frac.num, Frac.den, mk_frac; simpl; intro H.
  rewrite rig_mul_one_r.
  rewrite H.
  symmetry; apply rig_mul_zero_l.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition DomZeroDec (D : DomObject) : Type :=
  ∀ a : carrier (rig_setoid D),
    (a ≈ rig_zero D) + (a ≈ rig_zero D → False).

Definition DomEqDec (D : DomObject) : Type :=
  ∀ a b : carrier (rig_setoid D), (a ≈ b) + (a ≈ b → False).

Definition dom_eq_dec_zero_dec (D : DomObject) (dec : DomEqDec D) :
  DomZeroDec D := fun a => dec a (rig_zero D).

Lemma dom_zero_dec_eq_dec (D : DomObject) (dec : DomZeroDec D) : DomEqDec D.
Proof.
  intros a b.
  destruct (dec (rig_add D a (ring_neg D b))) as [H | H].
  - left; exact (ring_sub_zero (dom_ring D) a b H).
  - right; intro Hab; apply H; exact (ring_zero_sub (dom_ring D) a b Hab).
Qed.

Section FracField.

Context (D : DomObject).
Context (dec : DomZeroDec D).

Definition frac_zero_dec (x : frac_carrier D) :
  (frac_eq D x (frac_zero D)) + (frac_eq D x (frac_zero D) → False) :=
  match dec (num D x) with
  | inl H => inl (frac_zero_eq D x H)
  | inr H => inr (fun Heq => H (frac_eq_zero D x Heq))
  end.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition frac_finv (x : frac_carrier D) : frac_carrier D :=
  match dec (num D x) with
  | inl _  => frac_zero D
  | inr Hn => mk_frac D (den D x) (num D x) Hn
  end.

Program Definition FracField : FieldObject := {|
  field_ring         := FracRing D;
  field_comm         := FracRing_comm D;
  finv               := frac_finv
|}.
Next Obligation.
  (* 1 ≉ 0 fractions, since 1 ≉ 0 D. The 假设 a
 cross-multiplication equation conversion, read one. （已译） *)
  intro H.
  assert (H' : rig_mul D (rig_one D) (rig_one D)
                 ≈ rig_mul D (rig_zero D) (rig_one D)) by exact H.
  apply (dom_nontrivial D).
  rewrite <- (rig_mul_one_r D (rig_one D)).
  rewrite H'.
  apply rig_mul_zero_l.
Qed.
Next Obligation.
  (*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros x y Hxy.
  assert (Hxy' : rig_mul D (num D x) (den D y) ≈ rig_mul D (num D y) (den D x))
    by exact Hxy.
  unfold frac_finv.
  destruct (dec (num D x)) as [Hx | Hx]; destruct (dec (num D y)) as [Hy | Hy].
  - reflexivity.
  - exfalso; apply Hy.
    apply (dom_cancel D _ _ (den D x) (den_nonzero D x)).
    rewrite rig_mul_zero_l.
    rewrite <- Hxy'.
    rewrite Hx.
    apply rig_mul_zero_l.
  - exfalso; apply Hx.
    apply (dom_cancel D _ _ (den D y) (den_nonzero D y)).
    rewrite rig_mul_zero_l.
    rewrite Hxy'.
    rewrite Hy.
    apply rig_mul_zero_l.
  - assert (Hres : rig_mul D (den D x) (num D y)
                     ≈ rig_mul D (den D y) (num D x)).
    { rewrite (dom_comm D (den D x) (num D y)).
      rewrite <- Hxy'.
      apply dom_comm. }
    exact Hres.
Qed.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros x Hx; unfold frac_finv.
  destruct (dec (num D x)) as [Hn | Hn].
  - destruct (Hx (frac_zero_eq D x Hn)).
  - assert (Hres : rig_mul D (rig_mul D (den D x) (num D x)) (rig_one D)
                     ≈ rig_mul D (rig_one D) (rig_mul D (num D x) (den D x))).
    { rewrite rig_mul_one_r, rig_mul_one_l; apply dom_comm. }
    exact Hres.
Qed.

(* Decidability at zero passes to the fractions, hence so does
   ¬¬-stability, so [FracField] is an object of [StableField]. *)
Definition FracField_stable : FieldStableAtZero FracField :=
  fun a Hnn =>
    match frac_zero_dec a with
    | inl H => H
    | inr H => match Hnn H with end
    end.

Definition FracStableField : StableField := (FracField; FracField_stable).

(* 相关说明。 （已译） *)
Definition frac_unit : D ~{IntDom}~> StableField_IntDom FracStableField :=
  Build_DomHom D (field_dom FracField) (frac_embed D) (frac_embed_inj D).

(* * ** ⟨Q(D), n ↦ n/1⟩ 泛箭头 （已译） *)

Program Instance frac_universal_arrow :
  AUniversalArrow (D : IntDom) StableField_IntDom FracStableField := {|
  universal_arrow := frac_unit
|}.
Next Obligation.
  intros K f.
  unshelve esplit.
  - exact (frac_extend D `1 K f; I).
  - exact (frac_extend_embed D `1 K f).
  - intros g Hg x; symmetry; exact (frac_extend_unique D `1 K f `1 g Hg x).
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition frac_universal : UniversalArrow (D : IntDom) StableField_IntDom.
Proof using D dec.
  unshelve eapply (universal_arrow_from_UMP (D : IntDom) StableField_IntDom
                     FracStableField frac_unit).
  intros K f.
  unshelve esplit.
  - exact (frac_extend D `1 K f; I).
  - intro x; symmetry; exact (frac_extend_embed D `1 K f x).
  - intros g Hg x.
    assert (Hg' : ∀ a : carrier (rig_setoid D),
               rig_map `1 g (frac_embed D a) ≈ dom_map f a).
    { intro a; symmetry; exact (Hg a). }
    symmetry; exact (frac_extend_unique D `1 K f `1 g Hg' x).
Defined.

End FracField.

(* * ** Reduction mod 2, 态射 [IntDom] does not have （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* Only FOUR obligations are generated: both setoids here carry Leibniz
 equality, so [Proper (equiv ==> equiv) Z.odd] is discharged by
 实例 resolution during elaboration never becomes one.（已译） *)
Program Definition ZtoF2 : Int_Ring ~{Rng}~> F2_Ring := {|
  rig_map := {| morphism := Z.odd |}
|}.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; apply Z.odd_add. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. intros a b; apply Z.odd_mul. Qed.

(* It not injective — 0 2 collide — exactly why it a
 态射 [Dom] not [IntDom]. （已译） *)
Theorem ZtoF2_not_injective :
  (∀ a b : carrier (rig_setoid Int_Ring),
     rig_map ZtoF2 a ≈ rig_map ZtoF2 b → a ≈ b) → False.
Proof.
  intro Hinj.
  assert (H : (0%Z : carrier (rig_setoid Int_Ring)) ≈ 2%Z)
    by (apply Hinj; reflexivity).
  discriminate H.
Qed.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_DomHom_Z_F2 : DomHom Int_Dom (field_dom F2_Field) → False.
Proof.
  intro f.
  assert (H : (0%Z : carrier (rig_setoid Int_Dom)) ≈ 2%Z).
  { apply (dom_map_inj f).
    transitivity (rig_zero F2_Field).
    - apply (rig_map_zero (dom_map f)).
    - symmetry.
      transitivity (rig_add F2_Field (rig_map (dom_map f) (rig_one Int_Dom))
                      (rig_map (dom_map f) (rig_one Int_Dom))).
      + apply (rig_map_add (dom_map f) 1%Z 1%Z).
      + rewrite (rig_map_one (dom_map f)).
        exact F2_ftwo_zero. }
  discriminate H.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_field_over_Q_and_F2 (K : FieldObject)
  (u : RigHom K Q_Field) (v : RigHom K F2_Field) : False.
Proof.
  assert (Hnz : ftwo K ≈ rig_zero K → False).
  { intro H.
    apply Q_ftwo_nonzero.
    rewrite <- (ftwo_map u).
    rewrite H.
    apply (rig_map_zero u). }
  apply (field_hom_nonzero v _ Hnz).
  rewrite (ftwo_map v).
  exact F2_ftwo_zero.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary no_field_maps_to_all_fields (K : FieldObject)
  (h : ∀ L : FieldObject, RigHom K L) : False.
Proof. exact (no_field_over_Q_and_F2 K (h Q_Field) (h F2_Field)). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem IntDom_Dom_not_Full :
  Category.Theory.Functor.Full IntDom_Dom → False.
Proof.
  intros [pre _].
  exact (no_DomHom_Z_F2 (@pre Int_Dom (field_dom F2_Field) ZtoF2)).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem IntDom_Incl_not_Full :
  Category.Theory.Functor.Full IntDom_Incl → False.
Proof.
  intros [pre _].
  exact (no_DomHom_Z_F2 (@pre Int_Dom (field_dom F2_Field) (existT _ ZtoF2 I))).
Qed.

(* * ** maclane:III.1: no 泛箭头 ℤ over ALL homomorphisms （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_universal_arrow_Z_Dom
  (U : UniversalArrow (Int_Dom : Dom) Field_Dom) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact (unique_obj (ump_universal_arrows U
             (ZtoQ : Int_Dom ~{Dom}~> Field_Dom Q_Field))).
  - exact (unique_obj (ump_universal_arrows U
             (ZtoF2 : Int_Dom ~{Dom}~> Field_Dom F2_Field))).
Qed.

Theorem no_auniversal_arrow_Z_Dom (K : Field)
  (U : AUniversalArrow (Int_Dom : Dom) Field_Dom K) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact (unique_obj (@universal_arrow_universal _ _ _ _ _ U Q_Field
             (ZtoQ : Int_Dom ~{Dom}~> Field_Dom Q_Field))).
  - exact (unique_obj (@universal_arrow_universal _ _ _ _ _ U F2_Field
             (ZtoF2 : Int_Dom ~{Dom}~> Field_Dom F2_Field))).
Qed.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_universal_arrow_Z_Dom_stable
  (U : UniversalArrow (Int_Dom : Dom) StableField_Dom) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact `1 (unique_obj (ump_universal_arrows U
             (ZtoQ : Int_Dom ~{Dom}~> StableField_Dom Q_StableField))).
  - exact `1 (unique_obj (ump_universal_arrows U
             (ZtoF2 : Int_Dom ~{Dom}~> StableField_Dom F2_StableField))).
Qed.

Theorem no_auniversal_arrow_Z_Dom_stable (K : StableField)
  (U : AUniversalArrow (Int_Dom : Dom) StableField_Dom K) : False.
Proof.
  eapply no_field_over_Q_and_F2.
  - exact `1 (unique_obj (@universal_arrow_universal _ _ _ _ _ U Q_StableField
             (ZtoQ : Int_Dom ~{Dom}~> StableField_Dom Q_StableField))).
  - exact `1 (unique_obj (@universal_arrow_universal _ _ _ _ _ U F2_StableField
             (ZtoF2 : Int_Dom ~{Dom}~> StableField_Dom F2_StableField))).
Qed.

(* 相关说明。 （已译） *)

Definition Int_zero_dec : DomZeroDec Int_Dom :=
  fun a => match Z.eq_dec a 0%Z with
           | left H  => inl H
           | right H => inr H
           end.

(* Q(ℤ), as an object of the field category. *)
Definition Frac_Z : StableField := FracStableField Int_Dom Int_zero_dec.

(* The inclusion ℤ ↪ ℚ as a morphism of [IntDom]: [inject_Z] is
   injective because a · 1 ≈ b · 1 in ℤ. *)
Definition ZtoQ_Dom : DomHom Int_Dom (field_dom Q_Field).
Proof.
  refine (Build_DomHom Int_Dom (field_dom Q_Field) ZtoQ _).
  intros a b H.
  assert (H' : (inject_Z a == inject_Z b)%Q) by exact H.
  unfold Qeq, inject_Z in H'; simpl in H'.
  now rewrite !Z.mul_1_r in H'.
Defined.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem frac_universal_over_monos_not_over_all :
  AUniversalArrow (Int_Dom : IntDom) StableField_IntDom Frac_Z
  * (∀ K : StableField,
       AUniversalArrow (Int_Dom : Dom) StableField_Dom K → False).
Proof.
  split.
  - exact (frac_universal_arrow Int_Dom Int_zero_dec).
  - exact no_auniversal_arrow_Z_Dom_stable.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example frac_extend_Z_half :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) = (1 # 2)%Q := eq_refl.

Example frac_extend_Z_three :
  rig_map (frac_extend Int_Dom Q_Field ZtoQ_Dom)
    (frac_embed Int_Dom 3%Z) = (3 # 1)%Q := eq_refl.

(*
   本节说明 Frac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem frac_embed_Z_not_surjective (n : carrier (rig_setoid Int_Dom)) :
  frac_eq Int_Dom (frac_embed Int_Dom n)
    (mk_frac Int_Dom 1%Z 2%Z two_nonzero) → False.
Proof.
  intro H.
  assert (H' : (n * 2)%Z = (1 * 1)%Z) by exact H.
  assert (Hodd : Z.odd (n * 2) = Z.odd (1 * 1)) by (now rewrite H').
  rewrite Z.odd_mul in Hodd; simpl in Hodd.
  destruct (Z.odd n); discriminate Hodd.
Qed.
