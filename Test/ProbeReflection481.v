(*
   本文件为测试：ProbeReflection481。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Limit.Reflection.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p481_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane's definition, and Exercise 1 read off creation *)

Section Readbacks.

Context {J C D : Category} {K : J ⟶ C} {F : C ⟶ D}.

(* C1: Mac Lane's definition, per diagram, is #427's predicate: a cocone
   whose image cocone is colimiting is colimiting. *)
Example p481_c1_definition :
  ReflectsColimitCocone K F
    = (∀ N : Cocone K, IsColimitCocone (FCocone F N) → IsColimitCocone N)
  := eq_refl.

(* C2: Exercise 1 at cone level is the reflection field of the creation,
   the image cocone read over F^op ◯ K^op. *)
Example p481_c2_exercise1 (CR : CreatesColimit K F) :
  creates_reflects_colimits CR
    = fun N H => @creates_reflect (J^op) (C^op) (D^op) (K^op) (F^op) CR N
                   (islimitcone_op_comp H)
  := eq_refl.

(* R1 *)
Fail Definition p481_r1_op (H : ReflectsLimitCone (K^op) (F^op)) :
  ReflectsColimitCocone K F := H.

(* C3: the two predicates are one apart, through islimitcone_op_comp. *)
Definition p481_c3_op (H : ReflectsLimitCone (K^op) (F^op)) :
  ReflectsColimitCocone K F :=
  fun N HN => H N (islimitcone_op_comp HN).

(* C4: Riehl's Exercise 3.4.iii lifts every limiting cone downstairs to
   the given limit upstairs, on the nose. *)
Example p481_c4_lift (L : Limit K) (P : PreservesLimitCone K F)
  (R : ReflectsIsos F) (N : Cone (F ◯ K)) (HN : IsLimitCone N) :
  creates_lift (CreatesLimit := preserves_conservative_creates_limit L P R)
    N HN = @limit_cone _ _ _ L := eq_refl.

End Readbacks.

(* C5: Exercise 3 is the cone-level theorem at the walking parallel pair,
   read back through the bridges. *)
Example p481_c5_exercise3 {C D : Category} {F : C ⟶ D}
  (HC : HasCoequalizers C) (P : PreservesCoequalizers F)
  (R : ReflectsIsos F) :
  conservative_reflects_coequalizers HC P R
    = ReflectsColimitCocones_ReflectsCoequalizers
        (preserves_conservative_reflects_colimits_of_shape Parallel
           (HasCoequalizers_HasColimitsOfShape HC)
           (PreservesCoequalizers_PreservesColimitCocones P) R)
  := eq_refl.

(* C17: Exercise 1 over every diagram of parallel-pair shape is the
   per-pair theorem at the restriction of its hypothesis. *)
Example p481_c17_exercise1_restriction {C D : Category} {F : C ⟶ D}
  (CR : CreatesCoequalizers F) :
  creates_reflects_coequalizers CR
    = creates_reflects_coequalizers_of_pairs (fun x y f g => CR (APair f g))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** A class of shapes is the class of all diagrams of those shapes *)

(* C23: from the class of shapes S to the class of diagrams
   [fun J _ => S J] and back is the identity ... *)
Example p481_c23_over_class_over {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsLimitConesOver S F) :
  ReflectsLimitConesOfClass_Over (ReflectsLimitConesOver_OfClass H) = H
  := eq_refl.

(* C24: ... and so is the round trip from [fun J _ => S J]. *)
Example p481_c24_class_over_class {C D : Category} {S : Category → Type}
  {F : C ⟶ D} (H : ReflectsLimitConesOfClass (fun J _ => S J) F) :
  ReflectsLimitConesOver_OfClass (ReflectsLimitConesOfClass_Over H) = H
  := eq_refl.

(* C25: C23 on the colimit side. *)
Example p481_c25_colimit_over_class_over {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ReflectsColimitCoconesOver S F) :
  ReflectsColimitCoconesOfClass_Over (ReflectsColimitCoconesOver_OfClass H)
    = H
  := eq_refl.

(* C26: C24 on the colimit side. *)
Example p481_c26_colimit_class_over_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (H : ReflectsColimitCoconesOfClass (fun J _ => S J) F) :
  ReflectsColimitCoconesOver_OfClass (ReflectsColimitCoconesOfClass_Over H)
    = H
  := eq_refl.

(* C27: a conservative functor's reflection over a class of shapes is its
   reflection over the class of diagrams [fun J _ => S J], through the
   map. *)
Example p481_c27_reflects_over_is_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  preserves_conservative_reflects_limits_over S HL P R
    = ReflectsLimitConesOfClass_Over
        (preserves_conservative_reflects_limits_of_class (fun J _ => S J)
           (fun J K HJ => HL J HJ K) (fun J K HJ => P J HJ K) R)
  := eq_refl.

(* C28: C27 on the colimit side. *)
Example p481_c28_reflects_colimits_over_is_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Colimit K)
  (P : ∀ J : Category, S J → PreservesColimitCoconesOfShape J F)
  (R : ReflectsIsos F) :
  preserves_conservative_reflects_colimits_over S HL P R
    = ReflectsColimitCoconesOfClass_Over
        (preserves_conservative_reflects_colimits_of_class (fun J _ => S J)
           (fun J K HJ => HL J HJ K) (fun J K HJ => P J HJ K) R)
  := eq_refl.

(* C29: Riehl's Exercise 3.4.iii over a class of shapes is the exercise
   over the class of diagrams [fun J _ => S J], pointwise. *)
Example p481_c29_creates_over_is_class {C D : Category}
  {S : Category → Type} {F : C ⟶ D}
  (HL : ∀ J : Category, S J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver S F) (R : ReflectsIsos F) :
  preserves_conservative_creates_limits_over S HL P R
    = fun J HJ K =>
        preserves_conservative_creates_limits_of_class (fun J _ => S J)
          (fun J K HJ => HL J HJ K) (fun J K HJ => P J HJ K) R J K HJ
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Universes: the hom level of the target *)

(* C6: the elementary reflection of coequalizers, over a target whose hom
   level is strictly above C's. *)
Definition p481_c6_reflects_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ReflectsCoequalizers F.

(* C7: and the elementary preservation. *)
Definition p481_c7_preserves_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  PreservesCoequalizers F.

(* R2 *)
Fail Definition p481_r2_conservative_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  ReflectsIsos F.

(* C18: Structure/Limit/Preservation.v's [ReflectsIsos], its declaration
   copied with its binders written out ... *)
Class p481_c18_ReflectsIsos@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) := {
  p481_c18_reflects_iso {x y : C} (f : x ~> y) :
    IsIsomorphism (fmap[F] f) → IsIsomorphism f
}.

(* C19: ... is formable over the target R2 is refused at ... *)
Definition p481_c19_conservative_above@{co ch do dh + | ch < dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D) : Type :=
  p481_c18_ReflectsIsos F.

(* C20: ... and, at one hom level, gives the class itself. *)
Definition p481_c20_copy_is_class@{co ch do +}
  {C : Category@{co ch ch}} {D : Category@{do ch ch}} {F : C ⟶ D}
  (R : p481_c18_ReflectsIsos F) : ReflectsIsos F :=
  @Build_ReflectsIsos C D F
    (fun x y f I => @p481_c18_reflects_iso C D F R x y f I).

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the targets, by name *)

Check @Category.Structure.Coequalizer.parallel_cocone_coequalizer_colimit.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOfShape.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOver.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOfClass.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOver_OfClass.
Check @Category.Structure.Limit.Reflection.ReflectsLimitConesOfClass_Over.
Check @Category.Structure.Limit.Reflection.ReflectsAllLimits.
Check @Category.Structure.Limit.Reflection.ReflectsAllLimits_Over.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOfShape.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOver.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOfClass.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOver_OfClass.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCoconesOfClass_Over.
Check @Category.Structure.Limit.Reflection.ReflectsAllColimits.
Check @Category.Structure.Limit.Reflection.ReflectsAllColimits_Over.
Check @Category.Structure.Limit.Reflection.ReflectsIsos_op.
Check @Category.Structure.Limit.Reflection.creates_reflects_colimits.
Check @Category.Structure.Limit.Reflection.creates_reflects_all_limits.
Check @Category.Structure.Limit.Reflection.creates_reflects_all_colimits.
Check @Category.Structure.Limit.Reflection.MacLaneCreatesLimit.
Check @Category.Structure.Limit.Reflection.mlc_lift.
Check @Category.Structure.Limit.Reflection.mlc_limiting.
Check @Category.Structure.Limit.Reflection.mlc_unique.
Check @Category.Structure.Limit.Reflection.maclane_creates_reflects.
Check @Category.Structure.Limit.Reflection.maclane_CreatesLimit.
Check @Category.Structure.Limit.Reflection.iso_unique_lift_reflects.
Check @Category.Structure.Limit.Reflection.id_maclane_creates.
Check @Category.Structure.Limit.Reflection.MacLaneCreatesColimit.
Check @Category.Structure.Limit.Reflection.conservative_reflects_limit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limits_of_shape.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limits_over.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_limits_of_class.
Check @Category.Structure.Limit.Reflection.conservative_reflects_colimit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimits_of_shape.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimits_over.
Check @Category.Structure.Limit.Reflection.preserves_conservative_reflects_colimits_of_class.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_limit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_limits_over.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_limits_of_class.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_colimit.
Check @Category.Structure.Limit.Reflection.preserves_conservative_creates_colimits_of_class.
Check @Category.Structure.Limit.Reflection.ReflectsCoequalizers.
Check @Category.Structure.Limit.Reflection.PreservesCoequalizers.
Check @Category.Structure.Limit.Reflection.CreatesCoequalizers.
Check @Category.Structure.Limit.Reflection.ReflectsCoequalizers_ReflectsColimitCocones.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCocones_ReflectsCoequalizers_of_pairs.
Check @Category.Structure.Limit.Reflection.ReflectsColimitCocones_ReflectsCoequalizers.
Check @Category.Structure.Limit.Reflection.PreservesCoequalizers_PreservesColimitCocones.
Check @Category.Structure.Limit.Reflection.PreservesColimitCocones_PreservesCoequalizers_of_pairs.
Check @Category.Structure.Limit.Reflection.PreservesColimitCocones_PreservesCoequalizers.
Check @Category.Structure.Limit.Reflection.creates_reflects_coequalizers_of_pairs.
Check @Category.Structure.Limit.Reflection.maclane_creates_reflects_coequalizers.
Check @Category.Structure.Limit.Reflection.creates_reflects_coequalizers.
Check @Category.Structure.Limit.Reflection.conservative_reflects_coequalizers.

(* ------------------------------------------------------------------------ *)
(** ** Riehl's Lemma 3.4.5: full and faithful functors *)

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Limit.

Check @Category.Theory.Equivalence.Limit.ff_ReflectsLimitCone.
Check @Category.Theory.Equivalence.Limit.ff_reflects_colimit.
Check @Category.Theory.Equivalence.Limit.ff_ReflectsColimitCocone.

Section FullFaithful.

Context {C D : Category} {F : C ⟶ D}.
Context `{HF : @Full C D F} `{HfF : @Faithful C D F}.

(* C8: the limit half at every diagram, Riehl's "any limits". *)
Definition p481_c8_ff_all_limits : ReflectsAllLimits F :=
  fun J K => ff_ReflectsLimitCone K.

(* C9: and the colimit half. *)
Definition p481_c9_ff_all_colimits : ReflectsAllColimits F :=
  fun J K => ff_ReflectsColimitCocone K.

(* C10: the limit half is [ff_reflect_ump] with the legs by reflexivity. *)
Example p481_c10_ff_readback {J : Category} (K : J ⟶ C) :
  ff_ReflectsLimitCone K
    = fun N H => @ff_reflect_ump C D F HF HfF J K N (limitcone_isalimit H)
                   (fun x => reflexivity _)
  := eq_refl.

End FullFaithful.

(* ------------------------------------------------------------------------ *)
(** ** Left adjoints preserve coequalizers, in one line *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p481_c21_left_adjoint_preserves {C D : Category}
  {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) : PreservesCoequalizers F :=
  PreservesColimitCocones_PreservesCoequalizers
    (fun K => left_adjoint_PreservesColimitCocone A K).

(* ------------------------------------------------------------------------ *)
(** ** A class of shapes: all finite shapes *)

(* Required here, after every other command above: the import list of
   Structure/Limit/Finite.v and that module. *)
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Category.Structure.Limit.Finite.

(* C11: reflection of every finite limit, from reflection of all. *)
Definition p481_c11_finite {C D : Category} {F : C ⟶ D}
  (H : ReflectsAllLimits F) : ReflectsLimitConesOver FiniteCategory F :=
  ReflectsAllLimits_Over H.

(* C12: Riehl's Exercise 3.4.iii at the class of finite shapes. *)
Definition p481_c12_finite_creates {C D : Category} {F : C ⟶ D}
  (HL : ∀ J : Category, FiniteCategory J → ∀ K : J ⟶ C, Limit K)
  (P : PreservesLimitConesOver FiniteCategory F) (R : ReflectsIsos F) :
  ∀ J : Category, FiniteCategory J → CreatesLimitsOfShape J F :=
  preserves_conservative_creates_limits_over FiniteCategory HL P R.

(* ------------------------------------------------------------------------ *)
(** ** Exercise 3's conservativity is needed: the functor to the point *)

(* Required here, after every other command above: the import lists of
   Instance/One.v, Instance/Sets.v, Instance/Sets/Quotient.v and
   Instance/Sets/Coequalizer.v, and those modules. *)
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Coequalizer.

(* C13: in the point every fork is a coequalizer. *)
Definition p481_c13_point_coequalizer {x y : _1} (f g : x ~{_1}~> y)
  (q : _1) (e : y ~{_1}~> q) : IsCoequalizer f g q e.
Proof.
  unshelve econstructor.
  - destruct e, f, g; reflexivity.
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact ttt.
    + destruct h; reflexivity.
    + intros v _; destruct v; reflexivity.
Defined.

(* C14: so the functor from Sets to the point preserves coequalizers. *)
Definition p481_c14_erase_preserves : PreservesCoequalizers (Erase Sets) :=
  fun x y f g q e _ => p481_c13_point_coequalizer _ _ _ _.

(* The two-element setoid, and its map onto the singleton. *)
Definition p481_bool : SetoidObject :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition p481_collapse : p481_bool ~{Sets}~> unit_setoid_object.
Proof.
  exact (@Build_SetoidMorphism bool (eq_Setoid bool) poly_unit unit_setoid
           (fun _ => ttt) (fun _ _ _ => eq_refl)).
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem p481_c15_erase_not_reflects :
  ReflectsCoequalizers (Erase Sets) → False.
Proof.
  intro R.
  assert (E : IsCoequalizer (@id Sets p481_bool) id unit_setoid_object
                p481_collapse).
  { apply R.
    - reflexivity.
    - apply p481_c13_point_coequalizer. }
  destruct (coeq_desc E (@id Sets p481_bool) (reflexivity _)) as [u Hu _].
  pose proof (Hu true) as Ht.
  pose proof (Hu false) as Hf.
  simpl in Ht, Hf.
  rewrite Ht in Hf.
  discriminate.
Qed.

(* C16: Sets has coequalizers and the functor preserves them, so by
   Exercise 3 it is not conservative. *)
Definition p481_c16_erase_not_conservative :
  ReflectsIsos (Erase Sets) → False :=
  fun R => p481_c15_erase_not_reflects
             (conservative_reflects_coequalizers Sets_HasCoequalizers
                p481_c14_erase_preserves R).

(* C22: the three hypotheses of Exercise 3 hold together at the identity
   on Sets, which therefore reflects coequalizers. *)
Definition p481_c22_identity_reflects : ReflectsCoequalizers (@Id Sets) :=
  @conservative_reflects_coequalizers Sets Sets (@Id Sets)
    Sets_HasCoequalizers (fun x y f g q e E => E)
    (@Build_ReflectsIsos Sets Sets (@Id Sets) (fun x y f I => I)).
