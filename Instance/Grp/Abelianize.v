Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Abelianization.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.


(*
 nLab: https://ncatlab.org/nlab/show/abelianization

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ab_is_abelian (A : AbObject) (a b : carrier (Ab_to_GrpOb A)) :
  grp_mul (Ab_to_GrpOb A) a b ≈ grp_mul (Ab_to_GrpOb A) b a.
Proof. apply cmon_plus_comm. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma abel_kills {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b.
Proof.
  intro Hab.
  apply (@pequiv_to _ _ (cmon_prop A)).
  destruct Hab as [Hab].
  apply pequiv_from.
  pose proof (hom_to_abelian_kills (ab_is_abelian A) f _ Hab) as E.
  rewrite (grp_map_mul f), (grp_map_inv f) in E.
  apply (grp_cancel_r _ (grp_inv (Ab_to_GrpOb A) (grp_map f b))).
  rewrite E.
  symmetry; apply grp_mul_inv_r.
Qed.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition abelianize_med {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) : AbelianizationOb G ~{Ab}~> A := {|
  cmon_map := {| morphism := fun a : carrier G => grp_map f a |}
|}.
Next Obligation. intros G A f a b Hab; exact (abel_kills f a b Hab). Qed.
Next Obligation. intros G A f; exact (grp_map_unit f). Qed.
Next Obligation. intros G A f a b; exact (grp_map_mul f a b). Qed.

Example abelianize_med_computes {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a : carrier G) :
  cmon_map (abelianize_med f) a = grp_map f a := eq_refl.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem abelianize_universal (G : Grp) :
  ∀ (A : Ab) (f : G ~{Grp}~> Ab_to_Grp A),
    ∃! g : AbelianizationOb G ~{Ab}~> A,
      f ≈ fmap[Ab_to_Grp] g ∘ abel_proj G.
Proof.
  intros A f.
  unshelve eexists.
  - exact (abelianize_med f).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example abelianize_universal_med (G : Grp) (A : Ab)
  (f : G ~{Grp}~> Ab_to_Grp A) :
  unique_obj (abelianize_universal G A f) = abelianize_med f := eq_refl.

(** Packaged as an initial object of the comma category [=(G) ↓
    Ab_to_Grp]. *)
Definition abelianize_universal_arrow (G : Grp)
  : UniversalArrow G Ab_to_Grp :=
  universal_arrow_from_UMP G Ab_to_Grp (AbelianizationOb G) (abel_proj G)
    (abelianize_universal G).

(** The same content direct encoding, where universal 对象
 named rather than projected out comma 范畴. （已译） *)
Program Definition abelianize_AUniversalArrow (G : Grp)
  : AUniversalArrow G Ab_to_Grp (AbelianizationOb G) := {|
  universal_arrow := abel_proj G
|}.
Next Obligation.
  intros G A f.
  unshelve eexists.
  - exact (abelianize_med f).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    symmetry; exact (Hg a).
Qed.

(** [universal_arrow_from_UMP] stores supplied 态射 the
 second projection comma 对象 it builds, so both readings
 nose. （已译） *)
Example abelianize_arrow_is_proj (G : Grp) :
  @arrow _ _ G Ab_to_Grp (abelianize_universal_arrow G) = abel_proj G
  := eq_refl.

Example abelianize_arrow_obj (G : Grp) :
  @arrow_obj _ _ G Ab_to_Grp (abelianize_universal_arrow G)
    = AbelianizationOb G := eq_refl.

Example abelianize_AUniversalArrow_arrow (G : Grp) :
  @universal_arrow _ _ G Ab_to_Grp _ (abelianize_AUniversalArrow G)
    = abel_proj G := eq_refl.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition abelianize_left : Grp ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_to_Grp abelianize_universal_arrow.

Definition abelianize_adjunction : abelianize_left ⊣ Ab_to_Grp :=
  AdjunctionFromUniversalArrows Ab_to_Grp abelianize_universal_arrow.

Example abelianize_left_obj (G : Grp) :
  abelianize_left G = Abelianization_Functor G := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma abelianize_left_fmap {G H : Grp} (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f ≈ fmap[Abelianization_Functor] f.
Proof.
  apply (uniqueness (ump_universal_arrows (abelianize_universal_arrow G) _)).
  intro a; simpl; apply abel_eq_refl.
Qed.

(** The two facts assembled: 同构 函子 范畴
 whose components identities. （已译） *)
Program Definition abelianize_left_iso :
  @Isomorphism ([Grp, Ab]) abelianize_left Abelianization_Functor := {|
  to   := {| transform := fun G => @id Ab (Abelianization_Functor G) |};
  from := {| transform := fun G => @id Ab (Abelianization_Functor G) |}
|}.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G H k a; simpl.
  first [ exact (abelianize_left_fmap k a)
        | exact (abel_eq_sym H _ _ (abelianize_left_fmap k a)) ].
Qed.
Next Obligation.
  intros G a; simpl.
  first [ apply abel_eq_refl
        | exact (@fmap_id _ _ abelianize_left G a)
        | exact (abel_eq_sym G _ _ (@fmap_id _ _ abelianize_left G a)) ].
Qed.
Next Obligation.
  intros G a; simpl.
  first [ apply abel_eq_refl
        | exact (@fmap_id _ _ abelianize_left G a)
        | exact (abel_eq_sym G _ _ (@fmap_id _ _ abelianize_left G a)) ].
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition abelianize_counit_hom (A : AbObject) :
  AbelianizationOb (Ab_to_GrpOb A) ~{Ab}~> A := {|
  cmon_map := {| morphism := fun a : carrier (cmon_setoid A) => a |}
|}.
Next Obligation.
  intros A a b Hab.
  exact (abel_kills (@id Grp (Ab_to_GrpOb A)) a b Hab).
Qed.
Next Obligation. intros A; simpl; reflexivity. Qed.
Next Obligation. intros A a b; simpl; reflexivity. Qed.

(** The counit, concretely: 恒等 elements. （已译） *)
Example abelianize_counit_computes (A : AbObject)
  (a : carrier (cmon_setoid A)) :
  cmon_map (abelianize_counit_hom A) a = a := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition abelianize_counit_inv (A : AbObject) :
  A ~{Ab}~> AbelianizationOb (Ab_to_GrpOb A) := {|
  cmon_map := {| morphism := fun a : carrier (cmon_setoid A) => a |}
|}.
Next Obligation.
  intros A a b Hab; exact (abel_eq_of_eq (Ab_to_GrpOb A) a b Hab).
Qed.
Next Obligation. intros A; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros A a b; simpl; apply abel_eq_refl. Qed.

Program Definition abelianize_counit_iso (A : AbObject) :
  AbelianizationOb (Ab_to_GrpOb A) ≅[Ab] A := {|
  to   := abelianize_counit_hom A;
  from := abelianize_counit_inv A
|}.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A a; simpl; apply abel_eq_refl. Qed.

(** The counit 自然变换. Both 自然性 squares
 have 恒等 both legs, so both [reflexivity]. （已译） *)
Program Definition abelianize_counit :
  Abelianization_Functor ◯ Ab_to_Grp ⟹ @Id Ab := {|
  transform := abelianize_counit_hom
|}.
Next Obligation. intros A B f a; simpl; reflexivity. Qed.
Next Obligation. intros A B f a; simpl; reflexivity. Qed.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition abelianize_transform :
  Abelianization_Functor ∹ Ab_to_Grp := {|
  Transformation.unit   := abel_projection;
  Transformation.counit := abelianize_counit
|}.
Next Obligation. intros X a; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros X a; simpl; reflexivity. Qed.

Definition abelianize_adjunction_via_transform
  : Abelianization_Functor ⊣ Ab_to_Grp :=
  Adjunction_from_Transform abelianize_transform.

Example abelianize_transform_unit :
  unit[abelianize_transform] = abel_projection := eq_refl.

Example abelianize_transform_counit :
  counit[abelianize_transform] = abelianize_counit := eq_refl.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example abelianize_routes_agree_to (G : Grp) (A : Ab)
  (f : Abelianization_Functor G ~{Ab}~> A) :
  to (@adj _ _ _ _ abelianize_adjunction G A) f
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

Theorem abelianize_routes_agree (G : Grp) (A : Ab) :
  (∀ f : Abelianization_Functor G ~{Ab}~> A,
      to (@adj _ _ _ _ abelianize_adjunction G A) f
        = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f)
  * (∀ f : G ~{Grp}~> Ab_to_Grp A,
      from (@adj _ _ _ _ abelianize_adjunction G A) f
        ≈ from (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f).
Proof.
  split.
  - intro f; exact eq_refl.
  - intro f.
    apply (uniqueness (ump_universal_arrows (abelianize_universal_arrow G) f)).
    intro a; simpl; reflexivity.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example abelianize_unit_computes (G : Grp) (a : carrier G) :
  grp_map (@Category.Theory.Adjunction.unit _ _ _ _
             abelianize_adjunction G) a = a := eq_refl.

Example abelianize_unit_computes_via_transform (G : Grp) (a : carrier G) :
  grp_map (@Category.Theory.Adjunction.unit _ _ _ _
             abelianize_adjunction_via_transform G) a = a := eq_refl.

Example abelianize_counit_computes_via_transform (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (@Category.Theory.Adjunction.counit _ _ _ _
             abelianize_adjunction_via_transform A) a = a := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Ab_to_Grp_Faithful : Faithful Ab_to_Grp := {|
  fmap_inj := fun A B f g H => H
|}.

Program Definition Ab_to_Grp_Full : Full Ab_to_Grp := {|
  prefmap := fun A B (h : Ab_to_GrpOb A ~{Grp}~> Ab_to_GrpOb B) =>
    {| cmon_map      := grp_map h
     ; cmon_map_zero := grp_map_unit h
     ; cmon_map_plus := grp_map_mul h |}
|}.
Next Obligation. intros A B h a; simpl; reflexivity. Qed.

(* * ** Non-vacuity over S₃

 Every separation below obtained 映射 OUT quotient:
 no induction generation [InCommutator] could produce a
 negative. The target ℤ/2 read [AbObject]. （已译） *)

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_two_peq (x y : grp_two_carrier) : Prop :=
  match x, y with
  | inl _, inl _ => True
  | inr _, inr _ => True
  | _, _ => False
  end.

Definition grp_two_PropEquiv : PropEquiv (is_setoid (grp_setoid GrpTwo)).
Proof.
  unshelve refine
    (@PropEquiv_of_relation _ (is_setoid (grp_setoid GrpTwo)) grp_two_peq _ _).
  - intros [u|u] [v|v] H; simpl in *; try contradiction; exact ttt.
  - intros [u|u] [v|v] H; simpl in *; try contradiction; exact I.
Defined.

Program Definition AbTwo : AbObject := {|
  ab_cmon := {| cmon_setoid := grp_setoid GrpTwo
              ; cmon_zero   := grp_unit GrpTwo
              ; cmon_plus   := grp_mul GrpTwo
              ; cmon_prop   := grp_prop GrpTwo |}
 ; ab_neg := grp_inv GrpTwo
|}.
Solve All Obligations with
  (first [ exact (grp_mul_respects GrpTwo)
         | exact (grp_mul_assoc GrpTwo)
         | exact GrpTwo_abelian
         | exact (grp_mul_unit_l GrpTwo)
         | exact (grp_inv_Proper GrpTwo)
         | exact (grp_mul_inv_l GrpTwo) ]).

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ab_two_sign : S3 ~{Grp}~> Ab_to_GrpOb AbTwo :=
  Build_GrpHom S3 (Ab_to_GrpOb AbTwo)
    (grp_map s3_sign) (grp_map_unit s3_sign) (grp_map_mul s3_sign).

(** 本节：The projection MERGES: commutator two generators becomes
 unit abelianization. （已译） *)
Lemma abelianize_S3_identifies : abel_eq S3 (gcomm S3 S3_r S3_s) s3_unit.
Proof.
  constructor.
  apply (inc_resp (a := gcomm S3 S3_r S3_s)).
  - vm_compute; reflexivity.
  - apply inc_comm.
Qed.

(** 本节：…and what it merges was apart S₃, so abelianization S₃ is
 PROPER quotient. The second half donor's
 [commutator_S3_nontrivial]; nothing reproved. （已译） *)
Theorem abelianize_S3_proper :
  abel_eq S3 (gcomm S3 S3_r S3_s) s3_unit *
  (gcomm S3 S3_r S3_s ≈ s3_unit → False).
Proof.
  split.
  - exact abelianize_S3_identifies.
  - exact (snd commutator_S3_nontrivial).
Qed.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example abelianize_S3_med_s :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) S3_s
    = grp_two_one := eq_refl.

Example abelianize_S3_med_unit :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) s3_unit
    = grp_two_zero := eq_refl.

Theorem abelianize_S3_separates :
  cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign)) S3_s
    ≈ cmon_map (unique_obj (abelianize_universal S3 AbTwo ab_two_sign))
        s3_unit → False.
Proof. intro H; vm_compute in H; exact H. Qed.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example abelianize_S3_factors (a : carrier S3) :
  grp_map ab_two_sign a
    = grp_map (fmap[Ab_to_Grp]
                 (unique_obj (abelianize_universal S3 AbTwo ab_two_sign))
                 ∘ abel_proj S3) a := eq_refl.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example abelianize_probe_instrument : true = false := eq_refl.

(* Positive controls. *)
Example probe_ctl_left : Grp ⟶ Ab := abelianize_left.
Example probe_ctl_functor : Grp ⟶ Ab := Abelianization_Functor.
Example probe_ctl_adj : abelianize_left ⊣ Ab_to_Grp := abelianize_adjunction.
Example probe_ctl_adj_transform : Abelianization_Functor ⊣ Ab_to_Grp :=
  abelianize_adjunction_via_transform.
Example probe_ctl_fmap (G H : Grp) (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f ≈ fmap[Abelianization_Functor] f :=
  abelianize_left_fmap f.
Example probe_ctl_counit_hom (A : Ab) :
  AbelianizationOb (Ab_to_GrpOb A) ~{Ab}~> A := abelianize_counit_hom A.
Example probe_ctl_sign : S3 ~{Grp}~> Ab_to_GrpOb AbTwo := ab_two_sign.
Example probe_ctl_grptwo : GrpObject := GrpTwo.
Example probe_ctl_abtwo : AbObject := AbTwo.
Example probe_ctl_med (G : Grp) (A : Ab) (f : G ~{Grp}~> Ab_to_Grp A) :
  AbelianizationOb G ~{Ab}~> A := abelianize_med f.
Example probe_ctl_arrow (G : Grp) :
  @arrow _ _ G Ab_to_Grp (abelianize_universal_arrow G) = abel_proj G
  := eq_refl.
Example probe_ctl_aua (G : Grp) :
  AUniversalArrow G Ab_to_Grp (AbelianizationOb G) :=
  abelianize_AUniversalArrow G.
Example probe_ctl_counit_iso (A : Ab) :
  AbelianizationOb (Ab_to_GrpOb A) ≅[Ab] A := abelianize_counit_iso A.
Example probe_ctl_transform : Abelianization_Functor ∹ Ab_to_Grp :=
  abelianize_transform.
Example probe_ctl_left_iso :
  @Isomorphism ([Grp, Ab]) abelianize_left Abelianization_Functor :=
  abelianize_left_iso.
Example probe_ctl_kills {G : GrpObject} {A : AbObject}
  (f : G ~{Grp}~> Ab_to_GrpOb A) (a b : carrier G) :
  abel_eq G a b → grp_map f a ≈ grp_map f b := abel_kills f a b.
Example probe_ctl_counit_nat :
  Abelianization_Functor ◯ Ab_to_Grp ⟹ @Id Ab := abelianize_counit.
Example probe_ctl_counit_inv (A : Ab) :
  A ~{Ab}~> AbelianizationOb (Ab_to_GrpOb A) := abelianize_counit_inv A.
Example probe_ctl_full : Full Ab_to_Grp := Ab_to_Grp_Full.
Example probe_ctl_faithful : Faithful Ab_to_Grp := Ab_to_Grp_Faithful.

Example probe_control_obj (G : Grp) :
  abelianize_left G = Abelianization_Functor G := eq_refl.

Example probe_control_to (G : Grp) (A : Ab)
  (f : Abelianization_Functor G ~{Ab}~> A) :
  to (@adj _ _ _ _ abelianize_adjunction G A) f
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

Example probe_control_counit (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (abelianize_counit_hom A) a = a := eq_refl.

(* NEGATIVE 1 (conversion). The two left adjoints not same
 函子: arrow actions differ. （已译） *)
Fail Example probe_left_functors :
  abelianize_left = Abelianization_Functor := eq_refl.

(* NEGATIVE 2 (conversion).  Located precisely: the arrow actions.
   [ump_universal_arrows] is a [Qed] Corollary, so
   [unique_obj (ump_universal_arrows …)] reduces to nothing. *)
Fail Example probe_left_fmap_strict (G H : Grp) (f : G ~{Grp}~> H) :
  fmap[abelianize_left] f = fmap[Abelianization_Functor] f := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe_routes_to_record (G : Grp) (A : Ab) :
  to (@adj _ _ _ _ abelianize_adjunction G A)
    = to (@adj _ _ _ _ abelianize_adjunction_via_transform G A) := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe_routes_from (G : Grp) (A : Ab)
  (f : G ~{Grp}~> Ab_to_Grp A) :
  from (@adj _ _ _ _ abelianize_adjunction G A) f
    = from (@adj _ _ _ _ abelianize_adjunction_via_transform G A) f
  := eq_refl.

(* NEGATIVE 5 (conversion).  The DISCRIMINATING one: route one's
   derived counit does not compute, while route two's does
   ([abelianize_counit_computes_via_transform]) and the named component
   does ([probe_control_counit]).  Same derived constant, same
   statement shape. *)
Fail Example probe_counit_route_one (A : Ab)
  (a : carrier (cmon_setoid A)) :
  cmon_map (@Category.Theory.Adjunction.counit _ _ _ _
              abelianize_adjunction A) a = a := eq_refl.

(* NEGATIVE 6 (conversion).  Route two's derived counit computes on
   elements but is not the named component as a whole record: it is
   [abelianize_counit_hom A ∘ fmap[Abelianization_Functor] id]. *)
Fail Example probe_derived_counit_is_named (A : Ab) :
  @Category.Theory.Adjunction.counit _ _ _ _
    abelianize_adjunction_via_transform A = abelianize_counit_hom A
  := eq_refl.

(*
   本节说明 Abelianize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_abtwo_is_grptwo : Ab_to_GrpOb AbTwo = GrpTwo := eq_refl.
