Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(* * * The core 函子, 伴随 含入 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/Grpd
   Wikipedia: https://en.wikipedia.org/wiki/Core_(group_theory)
   Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,

   本文件给出核心定义。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma functor_ginv {A B : Category} (HA : IsGroupoid A) (HB : IsGroupoid B)
      (F : A ⟶ B) {x y : A} (f : x ~> y) :
  fmap[F] (ginv HA f) ≈ ginv HB (fmap[F] f).
Proof.
  symmetry.
  apply ginv_unique_r.
  rewrite <- fmap_comp.
  rewrite ginv_right.
  apply fmap_id.
Qed.

(*
   本节说明 Core 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example core_ginv_eq {C : Category} {x y : Groupoid C} (f : x ~> y) :
  ginv (core_is_groupoid C) f = iso_sym f := eq_refl.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition core_iso {D : Category} {a b : D} (i : a ≅ b) :
  a ≅[Groupoid D] b := {|
  to          := i;
  from        := iso_sym i;
  iso_to_from := iso_sym_right_inverse i;
  iso_from_to := iso_sym_left_inverse i
|}.

(** ** The core of a functor *)

Program Definition CoreMap {C D : Category} (F : C ⟶ D) :
  Groupoid C ⟶ Groupoid D := {|
  fobj := fun x => F x;
  fmap := fun _ _ f => {| to := fmap[F] (to f); from := fmap[F] (from f) |}
|}.
Next Obligation.
  rewrite <- fmap_comp, iso_to_from.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp, iso_from_to.
  apply fmap_id.
Qed.
Next Obligation.
  intros f g [Hto Hfrom]; split; simpl.
  - now rewrite Hto.
  - now rewrite Hfrom.
Qed.
(* 相关说明。 （已译） *)
Next Obligation. split; simpl; apply fmap_comp. Qed.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma CoreMap_respects {C D : Category} (F F' : C ⟶ D) :
  F ≈ F' → CoreMap F ≈ CoreMap F'.
Proof.
  intros [n Hn].
  exists (fun x => core_iso (n x)).
  intros x y f; split; simpl.
  - apply (Hn _ _ (to f)).
  - rewrite (Hn _ _ (from f)).
    now rewrite comp_assoc.
Qed.

Program Definition Core : Cat ⟶ Grpd := {|
  fobj := fun C => ((Groupoid C; core_is_groupoid C) : Grpd);
  fmap := fun _ _ F => (CoreMap F; I)
|}.
(* Only [fmap_respects] survives ambient [cat_simpl]; two 函子
 laws [Core] 恒等 natural 同构 both sides it
 discharges them. （已译） *)
Next Obligation.
  intros F F1 HF; simpl.
  now apply CoreMap_respects.
Qed.

(* * ** The counit: reading 同构 态射 （已译） *)

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition ForgetCore (C : Category) : Groupoid C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => to f
|}.

Lemma ForgetCore_Faithful (C : Category) : Faithful (ForgetCore C).
Proof.
  construct.
  now apply to_equiv_implies_iso_equiv.
Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition core_lift {G : Category} (HG : IsGroupoid G)
        {C : Category} (F : G ⟶ C) : G ⟶ Groupoid C := {|
  fobj := fun x => F x;
  fmap := fun _ _ f => {| to := fmap[F] f; from := fmap[F] (ginv HG f) |}
|}.
Next Obligation.
  rewrite <- fmap_comp, ginv_right.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp, ginv_left.
  apply fmap_id.
Qed.
Next Obligation.
  intros f g Hfg; split; simpl.
  - now rewrite Hfg.
  - (* [ginv_respects] is what carries `≈` under the chosen inverse. *)
    now rewrite Hfg.
Qed.
Next Obligation.
  split; simpl.
  - apply fmap_id.
  - rewrite ginv_id.
    apply fmap_id.
Qed.
Next Obligation.
  split; simpl.
  - apply fmap_comp.
  - rewrite ginv_comp.
    apply fmap_comp.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma core_functor_from {G : Category} (HG : IsGroupoid G) {C : Category}
      (P : G ⟶ Groupoid C) {x y : G} (f : x ~> y) :
  to (fmap[P] (ginv HG f)) ≈ from (fmap[P] f).
Proof.
  exact (fst (functor_ginv HG (core_is_groupoid C) P f)).
Qed.

(** ** The two round trips *)

Lemma core_lift_forget {G : Category} (HG : IsGroupoid G) {C : Category}
      (F : G ⟶ C) : ForgetCore C ◯ core_lift HG F ≈ F.
Proof.
  exists (fun x => @iso_id C (F x)).
  intros x y f; simpl; cat.
Qed.

Lemma forget_core_lift {G : Category} (HG : IsGroupoid G) {C : Category}
      (P : G ⟶ Groupoid C) : core_lift HG (ForgetCore C ◯ P) ≈ P.
Proof.
  exists (fun x => @iso_id (Groupoid C) (P x)).
  intros x y f; split; simpl.
  - cat.
  - rewrite core_functor_from.
    cat.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma core_lift_respects {G : Category} (HG : IsGroupoid G) {C : Category}
      (F F' : G ⟶ C) : F ≈ F' → core_lift HG F ≈ core_lift HG F'.
Proof.
  intros [n Hn].
  exists (fun x => core_iso (n x)).
  intros x y f; split; simpl.
  - apply (Hn _ _ f).
  - rewrite (Hn _ _ (ginv HG f)).
    now rewrite comp_assoc.
Qed.

(** ** The adjunction Incl ⊣ Core *)

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Incl_Core_Adjunction : Adjunction Grpd_Incl Core.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros G C.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun F => (core_lift (`2 G) F; I)).
      * abstract (intros F F' HF; simpl; now apply core_lift_respects).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun P => ForgetCore C ◯ `1 P).
      * abstract (intros P Q HPQ; simpl;
                  exact (Compose_respects (ForgetCore C) (ForgetCore C)
                           (Equivalence_Reflexive _) _ _ HPQ)).
    + abstract (intro P; simpl; apply forget_core_lift).
    + abstract (intro F; simpl; exact (core_lift_forget (`2 G) F)).
  - abstract (intros G G' C f g; simpl;
              exists (fun x => @iso_id (Groupoid C) (f (`1 g x)));
              intros x y h; split; simpl;
              [ cat
              | rewrite id_left, id_right;
                apply fmap_respects;
                apply (functor_ginv (`2 G) (`2 G') (`1 g) h) ]).
  - abstract (intros G C C' f g; simpl;
              exists (fun x => @iso_id (Groupoid C') (f (g x)));
              intros x y h; split; simpl; cat).
Defined.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem core_factorization {G : Grpd} {C : Category} (F : `1 G ⟶ C) :
  { P : `1 G ⟶ Groupoid C
  & (ForgetCore C ◯ P ≈ F) *
    (∀ Q : `1 G ⟶ Groupoid C, ForgetCore C ◯ Q ≈ F → Q ≈ P) }.
Proof.
  exists (core_lift (`2 G) F).
  split.
  - apply core_lift_forget.
  - intros Q HQ.
    rewrite <- (forget_core_lift (`2 G) Q).
    now apply core_lift_respects.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example core_counit_is_ForgetCore (C : Cat) :
  @counit Cat Grpd Grpd_Incl Core Incl_Core_Adjunction C ≈ ForgetCore C.
Proof. apply fun_equiv_id_right. Qed.

(* The unit sends arrow groupoid itself regarded an
 同构 -- exactly [core_lift] applied 恒等
 函子. （已译） *)

Example core_unit_is_core_lift_Id (G : Grpd) :
  `1 (@unit Cat Grpd Grpd_Incl Core Incl_Core_Adjunction G)
    ≈ core_lift (`2 G) Id.
Proof. reflexivity. Qed.
