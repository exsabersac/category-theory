(*
   本文件为测试：ProbeAbsolute477。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Lift.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Two.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Equalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Contractible.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Constant.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p477_absent_name.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Cones.

Context {J C : Category} {K : J ⟶ C}.

(* 相关说明。 （已译） *)
Example p477_c1_id_apex (N : Cone K) :
  vertex_obj[FCone Id N] = vertex_obj[N] := eq_refl.

(* C2: ... and its legs. *)
Example p477_c2_id_leg (N : Cone K) (x : J) :
  cone_leg (FCone Id N) x = cone_leg N x := eq_refl.

(* R1 *)
Fail Example p477_r1_id_comp : Id ◯ K = K := eq_refl.

(* 相关说明。 （已译） *)
Definition p477_c3_is_limit (N : Cone K) (A : AbsoluteLimitCone N) :
  IsLimitCone N := fun M => A C Id (cone_id_comp M).

(* 相关说明。 （已译） *)
Example p477_c4_of_op_op (N : Cocone K) (A : AbsoluteColimitCocone N) :
  AbsoluteColimitCocone_of_op (AbsoluteColimitCocone_op A) = A := eq_refl.

(* C5: ... both ways. *)
Example p477_c5_op_of_op (N : Cocone K)
  (A : @AbsoluteLimitCone (J^op) (C^op) (K^op) N) :
  AbsoluteColimitCocone_op (AbsoluteColimitCocone_of_op A) = A := eq_refl.

(* R2 *)
Fail Example p477_r2_dual_same (N : Cocone K) :
  AbsoluteColimitCocone N = @AbsoluteLimitCone (J^op) (C^op) (K^op) N
  := eq_refl.

(* C6: the limit predicate applies to a bundled limit ... *)
Definition p477_c6_bundled_limit (L : Limit K) (A : AbsoluteLimitCone L) :
  IsLimitCone L := AbsoluteLimitCone_IsLimitCone A.

(* 相关说明。 （已译） *)
Definition p477_c7_bundled_colimit (L : Colimit K)
  (A : AbsoluteColimitCocone L) : IsColimitCocone L :=
  AbsoluteColimitCocone_IsColimitCocone A.

(* C8: the apex reading lands in Structure/Limit/Constant.v's
   [AbsoluteLimit] ... *)
Definition p477_c8_apex (N : Cone K) (A : AbsoluteLimitCone N) :
  AbsoluteLimit K vertex_obj[N] := AbsoluteLimitCone_apex A.

(* C9: ... and its colimit twin in [AbsoluteColimit]. *)
Definition p477_c9_coapex (N : Cocone K) (A : AbsoluteColimitCocone N) :
  AbsoluteColimit K vertex_obj[N] := AbsoluteColimitCocone_apex A.

End Cones.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ComposeUniverse.

Universes jo co ch do dh.
Constraint ch < dh.

Context (Ju : Category@{jo ch ch}) (Cu : Category@{co ch ch})
  (Du : Category@{do dh dh}) (Ku : Ju ⟶ Cu) (Fu : Cu ⟶ Du).

(* C10: a functor into a category with strictly larger hom-sets. *)
Definition p477_c10_functor_type : Type := Cu ⟶ Du.

(* R3 *)
Fail Definition p477_r3_compose : Ju ⟶ Du := Fu ◯ Ku.

End ComposeUniverse.

Section IdInstance.

Universes jo co ch do.
Constraint co < do.

Context (Ju : Category@{jo ch ch}) (Cu : Category@{co ch ch})
  (Ku : Ju ⟶ Cu) (N : Cone Ku) (Nc : Cocone Ku).

(* C11: "take F := Id" at the instance whose target is C's own level. *)
Definition p477_c11_id_instance
  (A : AbsoluteLimitCone@{jo co ch co _ _ _ _} N) : IsLimitCone N :=
  AbsoluteLimitCone_IsLimitCone A.

(* R4 *)
Fail Definition p477_r4_id_instance
  (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N) : IsLimitCone N :=
  AbsoluteLimitCone_IsLimitCone A.

(* C22: R4's statement is a theorem through the lift ... *)
Definition p477_c22_up_instance
  (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N) : IsLimitCone N :=
  AbsoluteLimitCone_IsLimitCone_up A.

(* 相关说明。 （已译） *)
Definition p477_c23_down_instance
  (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N) : IsLimitCone N :=
  AbsoluteLimitCone_IsLimitCone (AbsoluteLimitCone_down A).

(* 相关说明。 （已译） *)
Definition p477_c24_coup_instance
  (A : AbsoluteColimitCocone@{jo co ch do _ _ _ _} Nc) :
  IsColimitCocone Nc :=
  AbsoluteColimitCocone_IsColimitCocone_up A.

(* 相关说明。 （已译） *)
Definition p477_c25_codown_instance
  (A : AbsoluteColimitCocone@{jo co ch do _ _ _ _} Nc) :
  IsColimitCocone Nc :=
  AbsoluteColimitCocone_IsColimitCocone (AbsoluteColimitCocone_down A).

(* 相关说明。 （已译） *)
Definition p477_c12_preserves (HN : IsLimitCone N)
  (A : AbsoluteLimitCone@{jo co ch do _ _ _ _} N)
  (D : Category@{do ch ch}) (F : Cu ⟶ D) : PreservesLimitCone Ku F :=
  AbsoluteLimitCone_preserves HN A D F.

End IdInstance.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Cofork.

Context {C X : Category} (T : C ⟶ X) {x y : C} (f g : x ~> y)
  {q : C} (e : y ~> q) (H : e ∘ f ≈ e ∘ g).

(* C13: the image cocone's injection over ParX is T (e ∘ f) ... *)
Example p477_c13_inj_ParX :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParX = fmap[T] (e ∘ f)
  := eq_refl.

(* C14: ... and over ParY it is T e. *)
Example p477_c14_inj_ParY :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParY = fmap[T] e
  := eq_refl.

(* R5 *)
Fail Example p477_r5_inj_ParX_split :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParX
    = fmap[T] e ∘ fmap[T] f := eq_refl.

(* C15: the split form holds at ≈, by [fmap_comp]. *)
Definition p477_c15_inj_ParX_equiv :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParX
    ≈ fmap[T] e ∘ fmap[T] f := fmap_comp e f.

(* 相关说明。 （已译） *)
Example p477_c16_desc
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H)))
  {z : X} (h : T y ~{X}~> z) (Hh : h ∘ fmap[T] f ≈ h ∘ fmap[T] g) :
  unique_obj (coeq_desc (image_colimit_coequalizer T H HC) h Hh)
    = unique_obj (HC (parallel_cofork_cocone (T ◯ APair f g) h Hh))
  := eq_refl.

(* C32: [image_colimit_coequalizer] IS Structure/Coequalizer.v's general
   conversion at [T ◯ APair f g]. *)
Example p477_c32_image_is_general
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H))) :
  image_colimit_coequalizer T H HC
    = parallel_colimit_coequalizer (T ◯ APair f g) _ HC := eq_refl.

End Cofork.

Section CoforkUniverse.

Universes co ch xo xh.
Constraint ch < xh.

Context (Cu : Category@{co ch ch}) {x y : Cu} (f g : x ~> y)
  (S : SplitCoequalizer f g).

(* C17: a split fork is absolute over targets with strictly larger
   hom-sets. *)
Definition p477_c17_split_absolute :
  AbsoluteCoequalizer@{co ch xo xh _} f g (scoeq_obj S) (scoeq_e S) :=
  split_coequalizer_absolute S.

(* C18: Split.v's preservation reaches such a target. *)
Definition p477_c18_split_preserved (Xu : Category@{xo xh xh})
  (T : Cu ⟶ Xu) :
  IsCoequalizer (fmap[T] f) (fmap[T] g) (T (scoeq_obj S))
    (fmap[T] (scoeq_e S)) :=
  split_coequalizer_preserved T f g S.

(* R6 *)
Fail Definition p477_r6_id_instance
  (A : AbsoluteCoequalizer@{co ch co xh _} f g (scoeq_obj S) (scoeq_e S)) :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S) :=
  AbsoluteCoequalizer_IsCoequalizer A.

(* C26: R6's statement is a theorem through the lift ... *)
Definition p477_c26_up_instance
  (A : AbsoluteCoequalizer@{co ch co xh _} f g (scoeq_obj S) (scoeq_e S)) :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S) :=
  AbsoluteCoequalizer_IsCoequalizer_up A.

(* 相关说明。 （已译） *)
Definition p477_c27_down_instance
  (A : AbsoluteCoequalizer@{co ch co xh _} f g (scoeq_obj S) (scoeq_e S)) :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S) :=
  AbsoluteCoequalizer_IsCoequalizer (AbsoluteCoequalizer_down A).

(* C19: at C's own levels "automatically a coequalizer" holds of a split
   fork ... *)
Definition p477_c19_id_instance :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S) :=
  AbsoluteCoequalizer_IsCoequalizer (split_coequalizer_absolute S).

(* C20: ... as Mac Lane's Lemma, Split.v's own, has it directly. *)
Definition p477_c20_lemma : IsCoequalizer f g (scoeq_obj S) (scoeq_e S) :=
  split_coequalizer_is_coequalizer f g S.

(* C21: a split fork reaches Structure/Limit/Constant.v's apex-only
   [AbsoluteColimit] through the cone-level predicate. *)
Definition p477_c21_split_apex :
  AbsoluteColimit (APair f g) (scoeq_obj S) :=
  AbsoluteColimitCocone_apex (split_cofork_AbsoluteColimitCocone S).

End CoforkUniverse.

(* 相关说明。 （已译） *)
Definition p477_c48_split_op_limit {C : Category} {x y : C^op}
  {f g : x ~{C^op}~> y} (S : SplitCoequalizer f g) :
  @AbsoluteLimitCone (Parallel^op) C ((APair f g)^op)
    (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)) :=
  AbsoluteColimitCocone_op (split_cofork_AbsoluteColimitCocone S).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section ParallelDiagram.

Context {C : Category}.

(* 相关说明。 （已译） *)
Definition p477_c28_apair_colimit {x y : C} (f g : x ~> y) {q : C}
  {e : y ~> q} (E : IsCoequalizer f g q e) :
  IsColimitCocone (is_coequalizer_cocone f g E) :=
  parallel_coequalizer_colimit (APair f g) E.

(* 相关说明。 （已译） *)
Definition p477_c29_apair_coequalizer {x y : C} (f g : x ~> y)
  (L : Coequalizer (APair f g)) :
  IsCoequalizer f g (colimit_apex L)
    (colimit_inj (colimit_is_acolimit L) ParY) :=
  parallel_colimit_coequalizer (APair f g) L (colimit_colimitcocone L).

(* C30: any colimiting cocone over an image diagram [U ◯ APair f g] is an
   elementary coequalizer of the image pair. *)
Definition p477_c30_image_pair {D : Category} (U : C ⟶ D) {x y : C}
  (f g : x ~> y) (N : Cocone (U ◯ APair f g)) (HN : IsColimitCocone N) :
  IsCoequalizer (fmap[U] f) (fmap[U] g) vertex_obj[N] (cocone_inj N ParY) :=
  parallel_colimit_coequalizer (U ◯ APair f g) N HN.

(* C31: the converse Adjunction/Diagonal/Finite.v records as absent, at
   Adjunction/Diagonal/Limit.v's named type. *)
Definition p477_c31_has_colimits (HC : HasCoequalizers C) :
  HasColimitsOfShape Parallel C :=
  HasCoequalizers_HasColimitsOfShape HC.

End ParallelDiagram.

(* ------------------------------------------------------------------------ *)
(** ** The lift: Construction/Lift.v *)

Section LiftReadbacks.

Context (C X : Category) (T : C ⟶ X) {x y : C} (f : x ~{C}~> y).

(* C33: [Lift_in] is the identity on objects ... *)
Example p477_c33_in_fobj : fobj[Lift_in C] x = x := eq_refl.

(* C34: ... and on arrows. *)
Example p477_c34_in_fmap : fmap[Lift_in C] f = f := eq_refl.

(* C35: [Lift_after T] has T's object action ... *)
Example p477_c35_after_fobj : fobj[Lift_after T] x = T x := eq_refl.

(* C36: ... and its arrow action. *)
Example p477_c36_after_fmap : fmap[Lift_after T] f = fmap[T] f := eq_refl.

End LiftReadbacks.

Section LiftCompose.

Universes co ch xo xh yo yh.
Constraint xh < yh.

Context (Cl : Category@{co ch ch}) (Xl : Category@{xo xh xh})
  (Tl : Cl ⟶ Xl).

(* C37: [Lift_after] reads T into a lift with strictly larger hom-sets. *)
Definition p477_c37_after : Cl ⟶ LiftCat@{xo xh yo yh} Xl := Lift_after Tl.

(* R9 *)
Fail Definition p477_r9_compose : Cl ⟶ LiftCat@{xo xh yo yh} Xl :=
  Lift_in Xl ◯ Tl.

End LiftCompose.

Section LiftComposeObjects.

Universes co ch xo yo.
Constraint xo < yo.

Context (Cl : Category@{co ch ch}) (Xl : Category@{xo ch ch})
  (Tl : Cl ⟶ Xl).

(* C38: 对象 lifted alone 复合 formable. （已译） *)
Definition p477_c38_compose_objects : Cl ⟶ LiftCat@{xo ch yo ch} Xl :=
  Lift_in Xl ◯ Tl.

End LiftComposeObjects.

Section LiftBack.

Universes co ch xo xh.
Constraint ch < xh.

Context (Cb : Category@{co ch ch}).

(* C39: 函子 type 进入 lift formable ... （已译） *)
Definition p477_c39_in_type : Type := Cb ⟶ LiftCat@{co ch xo xh} Cb.

(* R10 *)
Fail Definition p477_r10_back_type : Type := LiftCat@{co ch xo xh} Cb ⟶ Cb.

End LiftBack.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition p477_c40_cone_leg@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} {F : J ⟶ C} (N : Cone F) (x : J) :
  vertex_obj[N] ~{C}~> F x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

Definition p477_c41_IsLimitCone@{jo jh co ch +} {J : Category@{jo jh jh}}
  {C : Category@{co ch ch}} {K : J ⟶ C} (N : Cone K) : Type :=
  ∀ M : Cone K, ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, p477_c40_cone_leg N x ∘ u ≈ p477_c40_cone_leg M x.

(* C42: Functor/Opposite.v's [Opposite_Functor], with its binders written
   out. *)
Definition p477_c42_op@{jo jh co ch +}
  {J : Category@{jo jh jh}} {C : Category@{co ch ch}} (F : J ⟶ C) :
  J^op ⟶ C^op :=
  @Build_Functor (J^op) (C^op) F
    (λ (x y : (J^op)%category) (f : x ~{J^op}~> y), @fmap J C F y x f)
    (λ (x y : (J^op)%category) (f g : x ~{J^op}~> y),
       @fmap_respects _ _ F y x f g)
    (λ x : (J^op)%category, fmap_id)
    (λ (x y z : (J^op)%category) (f : y ~{J^op}~> z) (g : x ~{J^op}~> y),
       @fmap_comp _ _ F _ _ _ g f).

Section ConeCap.

Universes jo jh co ch.
Constraint jh < ch.

Context (Jw : Category@{jo jh jh}) (Cw : Category@{co ch ch})
  (Kw : Jw ⟶ Cw).

(* C43: cones over a diagram whose shape has strictly smaller hom-sets ... *)
Definition p477_c43_cone_type : Type := Cone Kw.

(* R7 *)
Fail Definition p477_r7_islimitcone (N : Cone Kw) : Type := IsLimitCone N.

(* 相关说明。 （已译） *)
Definition p477_c44_islimitcone (N : Cone Kw) : Type :=
  p477_c41_IsLimitCone N.

(* R8 *)
Fail Definition p477_r8_op : Jw^op ⟶ Cw^op := Kw^op.

(* C45: opposite 函子 binders written out, cones over
 it, cocones over [Kw]. （已译） *)
Definition p477_c45_cocone_type : Type := Cone (p477_c42_op Kw).

End ConeCap.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section YonedaSmall.

Universes jo co ch.
Constraint co < ch.

Context (Jy : Category@{jo ch ch}) (Cy : Category@{co ch ch})
  (Ky : Jy ⟶ Cy) (Ny : Cocone Ky).

(* C46: an absolute colimit is preserved by the Yoneda embedding of a
   category whose objects lie strictly below its hom-sets ... *)
Definition p477_c46_yoneda_small (A : AbsoluteColimitCocone Ny) :
  IsColimitCocone (FCocone (Curried_CoHom Cy) Ny) :=
  A _ (Curried_CoHom Cy).

End YonedaSmall.

Section YonedaLarge.

Universes jo co ch.
Constraint ch < co.

Context (Jy : Category@{jo ch ch}) (Cy : Category@{co ch ch})
  (Ky : Jy ⟶ Cy) (Ny : Cocone Ky).

(* C47: ... while one whose 对象 lie strictly above, embedding
 formable ... （已译） *)
Definition p477_c47_yoneda_type : Type := Cy ⟶ [Cy^op, Sets].

(* R11 *)
Fail Definition p477_r11_yoneda_large (A : AbsoluteColimitCocone Ny) :
  IsColimitCocone (FCocone (Curried_CoHom Cy) Ny) :=
  A _ (Curried_CoHom Cy).

End YonedaLarge.

(* ------------------------------------------------------------------------ *)
(* * ** Guard: every 常值 #477 adds, name （已译） *)

Check @Category.Construction.Lift.LiftCat.
Check @Category.Construction.Lift.Lift_in.
Check @Category.Construction.Lift.Lift_in_fobj.
Check @Category.Construction.Lift.Lift_in_fmap.
Check @Category.Construction.Lift.Lift_after.
Check @Category.Construction.Lift.Lift_after_fobj.
Check @Category.Construction.Lift.Lift_after_fmap.
Check @Category.Structure.Coequalizer.parallel_cofork_legs.
Check @Category.Structure.Coequalizer.parallel_cofork_legs_coherence.
Check @Category.Structure.Coequalizer.parallel_cofork_cocone.
Check @Category.Structure.Coequalizer.parallel_coequalizer_colimit.
Check @Category.Structure.Coequalizer.parallel_colimit_coequalizer.
Check @Category.Structure.Coequalizer.HasCoequalizers_HasColimitsOfShape.
Check @Category.Structure.Limit.Preservation.cone_id_comp.
Check @Category.Structure.Limit.Preservation.FCocone_iso.
Check @Category.Structure.Limit.Preservation.cocone_assoc_inv.
Check @Category.Structure.Limit.Comparison.PreservesColimitCocone_of_cocone.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone.
Check @Category.Structure.Limit.Absolute.FCone_Id_apex.
Check @Category.Structure.Limit.Absolute.FCone_Id_leg.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_IsLimitCone.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_op.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_of_op.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_of_op_op.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_op_of_op.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_IsColimitCocone.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_IsLimitCone_up.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_IsColimitCocone_up.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_down.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_down.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_preserves.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_of_preserves.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_preserves.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_of_preserves.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_transport.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_transport.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_limitcone.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_colimitcocone.
Check @Category.Structure.Limit.Absolute.AbsoluteLimitCone_image.
Check @Category.Structure.Limit.Absolute.AbsoluteColimitCocone_image.
Check @Category.Structure.Limit.Absolute.empty_shape_cone.
Check @Category.Structure.Limit.Absolute.empty_shape_cocone.
Check @Category.Structure.Limit.Absolute.two_into_TwoY.
Check @Category.Structure.Limit.Absolute.two_out_of_TwoX.
Check @Category.Structure.Limit.Absolute.two_terminal_IsLimitCone.
Check @Category.Structure.Limit.Absolute.two_initial_IsColimitCocone.
Check @Category.Structure.Limit.Absolute.two_terminal_not_absolute.
Check @Category.Structure.Limit.Absolute.two_initial_not_absolute.
Check @Category.Structure.Coequalizer.Absolute.AbsoluteCoequalizer.
Check @Category.Structure.Coequalizer.Absolute.AbsoluteCoequalizer_IsCoequalizer.
Check @Category.Structure.Coequalizer.Absolute.split_coequalizer_absolute.
Check @Category.Structure.Coequalizer.Absolute.AbsoluteCoequalizer_IsCoequalizer_up.
Check @Category.Structure.Coequalizer.Absolute.AbsoluteCoequalizer_down.
Check @Category.Structure.Coequalizer.Absolute.image_cofork_inj_ParX.
Check @Category.Structure.Coequalizer.Absolute.image_cofork_inj_ParY.
Check @Category.Structure.Coequalizer.Absolute.image_coequalizer_colimit.
Check @Category.Structure.Coequalizer.Absolute.image_colimit_coequalizer.
Check @Category.Structure.Coequalizer.Absolute.image_colimit_coequalizer_desc.
Check @Category.Structure.Coequalizer.Absolute.AbsoluteCoequalizer_AbsoluteColimitCocone.
Check @Category.Structure.Coequalizer.Absolute.AbsoluteColimitCocone_AbsoluteCoequalizer.
Check @Category.Structure.Coequalizer.Absolute.split_cofork_AbsoluteColimitCocone.
Check @Category.Structure.Coequalizer.Absolute.split_coequalizer_PreservesColimitCocone.
Check @Category.Structure.Limit.Constant.AbsoluteLimitCone_apex.
Check @Category.Structure.Limit.Constant.AbsoluteColimitCocone_apex.
