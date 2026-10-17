(*
   本文件为测试：ProbeFullFaithful367。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The Require list of Functor/Hom/Transfer.v. *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Functor.Hom.

(* The extra Requires of Adjunction/FullFaithful.v. *)
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Fullness.
Require Import Category.Adjunction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

(* The two targets. *)
Require Import Category.Functor.Hom.Transfer.
Require Import Category.Adjunction.FullFaithful.

(* 相关说明。 （已译） *)
Require Import Category.Instance.Coq.Monoid.Free.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

(* 相关说明。 （已译） *)

Fail Check probe_367_no_such_reference.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section TransferComparison.

Context {A : Category}.
Context {a b : A}.
Context (f : b ~> a).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @hom_transfer.
Check @Curried_Hom.
Check (@hom_transfer_is_fmap_value A a b f).
Check (@hom_transfer_is_fmap A a b f).

Example ctrl_transfer_value (c : A) (h : a ~> c) :
  transform[hom_transfer f] c h
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c h
  := eq_refl.

(*
   本节说明 ProbeFullFaithful367 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example neg1_whole_record :
  hom_transfer f = fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)
  := eq_refl.

(*
   本节说明 ProbeFullFaithful367 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example neg2_component_record (c : A) :
  transform[hom_transfer f] c
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c
  := eq_refl.

(* CONTROL.  The Yoneda-side readback holds at [≈]. *)

Check (@hom_transfer_at_id A a b f).

(* 相关说明。 （已译） *)

Fail Example neg3_transfer_at_id :
  transform[hom_transfer f] a id = f := eq_refl.

End TransferComparison.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section SplitVersusMonic.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(* 相关说明。 （已译） *)

Check @right_adjoint_full_iff_counit_split_monic.

Definition ctrl_section (HU : Functor.Full U) (a : C) :
  Section (@counit C D F U A a) :=
  fst right_adjoint_full_iff_counit_split_monic HU a.

(*
   本节说明 ProbeFullFaithful367 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition neg4_section_is_not_monic (HU : Functor.Full U) (a : C) :
  Monic (@counit C D F U A a) :=
  fst right_adjoint_full_iff_counit_split_monic HU a.

(* 相关说明。 （已译） *)

Definition ctrl_section_gives_monic (HU : Functor.Full U) (a : C) :
  Monic (@counit C D F U A a) :=
  sections_are_monic _ _ _ (ctrl_section HU a).

End SplitVersusMonic.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ReflectiveOpacity.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (x : Sub C S).

(* CONTROL. Section (G) target derives conclusion of
 Construction/Reflective.v Theorem 1(iii), existing
 引理 nameable here. （已译） *)

Check (@reflective_counit_IsIsomorphism_general C S R x).
Check (@reflective_counit_iso C S R x).
Check (to (@reflective_counit_iso C S R x)).
Check @reflector.
Check @Incl.
Check @reflective_adj.

(*
   本节说明 ProbeFullFaithful367 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example neg5_reflective_to_is_counit :
  to (@reflective_counit_iso C S R x)
  = @counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x
  := eq_refl.

End ReflectiveOpacity.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomProofDonor.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (u v : Cu).
Context (g : u ~{Cu}~> v).

(* CONTROLS accepted at these very levels: naming a hom, an identity, and
   a composite. *)

Check (u ~{Cu}~> v).
Check (@id Cu u).
Check (g ∘ @id Cu u).
Check @Retraction.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (@Epic Cu u v g).
Fail Check (@Monic Cu u v g).
Fail Check (@Section Cu u v g).
Fail Check (@Retraction Cu u v g).

End HomProofDonor.

Section AdjunctionHomDonor.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Cu : Category@{ao ah ah}).
Context (Du : Category@{bo bh bh}).

(* CONTROL accepted at these levels: 函子 direction the
 constraint allows. （已译） *)

Check (Cu ⟶ Du).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Du ⟶ Cu).

End AdjunctionHomDonor.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PriorArt.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition ctrl_prior_art_free (HU : Functor.Faithful U) (a : C) :
  Epic (@counit C D F U A a) :=
  adjunction_counit_epic A HU a.

Definition ctrl_prior_art_target (HU : Functor.Faithful U) (a : C) :
  Epic (@counit C D F U A a) :=
  @counit_epic_of_faithful C D F U A HU a.

(* 相关说明。 （已译） *)

Check (@adjunction_counit_underlying_retraction C D F U A).

End PriorArt.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pointed_erase_adj :
  @Diagonal PointedSets _1
    (@initial_obj PointedSets (@zero_initial PointedSets PointedSets_Zero))
  ⊣ Erase PointedSets :=
  zero_erase_adjunction PointedSets_Zero.

Definition pointed_counit_Section (a : PointedSets) :
  Section (@counit PointedSets _1 _ (Erase PointedSets)
             pointed_erase_adj a) :=
  fst (@right_adjoint_full_iff_counit_split_monic PointedSets _1 _
         (Erase PointedSets) pointed_erase_adj)
      (Full_Erase_of_ZeroObject PointedSets_Zero) a.

Lemma pointed_counit_family_not_Epic :
  (∀ a : PointedSets,
      Epic (@counit PointedSets _1 _ (Erase PointedSets)
              pointed_erase_adj a)) → False.
Proof.
  intros H.
  apply Erase_PointedSets_not_Faithful.
  exact (snd (@right_adjoint_faithful_iff_counit_epic PointedSets _1 _
                (Erase PointedSets) pointed_erase_adj) H).
Qed.

(* 相关说明。 （已译） *)

Check pointed_counit_not_IsIsomorphism.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition mon_coq_forget : @Mon Coq Coq_Monoidal ⟶ Coq :=
  @Mon_Forget Coq Coq_Monoidal.

Definition free_mon_faithful : Functor.Faithful mon_coq_forget.
Proof. constructor; intros x y f g H; exact H. Qed.

Definition free_mon_counit_Epic (L : @Mon Coq Coq_Monoidal) :
  Epic (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
          free_monoid_adjunction L) :=
  fst (@right_adjoint_faithful_iff_counit_epic
         (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
         free_monoid_adjunction) free_mon_faithful L.

Lemma free_mon_forget_not_Full : Functor.Full mon_coq_forget → False.
Proof.
  intros HFull.
  pose (W := FreeMon bool).
  pose (k := (fun _ : list bool => Datatypes.cons true Datatypes.nil)
             : mon_coq_forget W ~{Coq}~> mon_coq_forget W).
  pose proof (@fmap_sur _ _ mon_coq_forget HFull W W k) as Hs.
  pose proof (hom_mone (@prefmap _ _ mon_coq_forget HFull W W k)) as Hu.
  specialize (Hs (@mone W)).
  simpl in Hs, Hu.
  rewrite Hu in Hs.
  discriminate Hs.
Qed.

Lemma free_mon_counit_family_not_Section :
  (∀ L : @Mon Coq Coq_Monoidal,
      Section (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                 mon_coq_forget free_monoid_adjunction L)) → False.
Proof.
  intros H.
  apply free_mon_forget_not_Full.
  exact (snd (@right_adjoint_full_iff_counit_split_monic
                (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
                free_monoid_adjunction) H).
Qed.

(* And combined reading: (iii), counit 伴随 is
 not componentwise 同构 either. （已译） *)

Lemma free_mon_counit_family_not_iso :
  (∀ L : @Mon Coq Coq_Monoidal,
      IsIsomorphism (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                       mon_coq_forget free_monoid_adjunction L)) → False.
Proof.
  intros H.
  apply free_mon_forget_not_Full.
  exact (fst (snd (@right_adjoint_fully_faithful_iff_counit_iso
                     (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                     mon_coq_forget free_monoid_adjunction) H)).
Qed.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbeFullFaithful367 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check @hom_transfer_monic_iff_epic.
Check @hom_transfer_epic_iff_section.
Check @hom_transfer_component.
Check @hom_transfer_component_injective_iff.
Check @hom_transfer_component_surjective_iff.
Check @epic_of_hom_transfer_monic.
Check @hom_transfer_monic_of_epic.
Check @section_of_hom_transfer_epic.
Check @hom_transfer_epic_of_section.
Check @Epic_Section_IsIsomorphism.
Check @counit_precomp_is_from_adj_fmap_U.
Check @transfer_at_counit_is_precomp.
Check @fmap_U_is_transfer_then_transpose.
Check @counit_transfer_monic_of_faithful.
Check @counit_epic_of_faithful.
Check @faithful_of_counit_epic.
Check @right_adjoint_faithful_iff_counit_epic.
Check @counit_transfer_epic_of_full.
Check @counit_section_via_transfer.
Check @full_data_of_counit_section.
Check @full_of_counit_section.
Check @right_adjoint_fully_faithful_iff_counit_iso.
Check @from_adj_id_is_counit.
Check @from_adj_epic_of_epic_direct.
Check @from_adj_epic_of_epic.
Check @right_adjoint_faithful_iff_from_adj_epic.
Check @op_counit_is_unit.
Check @op_unit_is_counit.
Check @left_adjoint_faithful_iff_unit_monic.
Check @left_adjoint_full_iff_unit_split_epic.
Check @left_adjoint_fully_faithful_iff_unit_iso.
Check @unit_retract_agrees.
Check @reflective_incl_Full.
Check @reflective_incl_Faithful.
Check @reflective_counit_Isomorphism_general.
Check @reflection_counit_Epic.
