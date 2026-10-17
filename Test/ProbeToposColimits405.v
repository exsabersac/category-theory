Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Terminal.
Require Import Category.Theory.Equivalence.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Structure.Topos.Colimits.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Adjunction.Right.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Topos.

Generalizable All Variables.
Open Scope category_scope.

(*
   本文件为测试：ProbeToposColimits405。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Fail Check p405_this_name_does_not_exist.

(* 相关说明。 （已译） *)

Section ProbeGeneral.

Context {C : Category}.
Context `{HT : @ElementaryTopos C}.

Example p405_op_op : (C^op)^op = C := eq_refl.

Example p405_powf_obj (a : C) : fobj[PowF] a = Pow a := eq_refl.

Example p405_powf_map {a b : C} (f : b ~{C}~> a) :
  fmap[PowF] f = curry (id ∘ eval ∘ second f) := eq_refl.

Definition p405_ok_handedness : Opposite_Functor PowF ⊣ PowF :=
  pow_adjunction.

Definition p405_powf_typed : C^op ⟶ C := PowF.

Check @pow_self_adjoint.
Check @pow_aor.
Check @pow_relations.
Check @pow_aor_is_relations.
Check @pow_monad.
Check @flip_flip.
Check @flip_comp.
Check @flip_pow_comp.
Check @pow_precompose.
Check @relations_iso_to_is_curry_char.
Check @relations_iso_from_is_reindex.
Check @topos_balanced.
Check @topos_diag.
Check @sing.
Check @sing_Monic.
Check @char_diag_swap.
Check @flip_sing.
Check @PowF_Faithful.
Check @PowF_ReflectsIsos.
Check @IsIso_of_op.
Check @op_IsIso_of.
Check @second_Monic.
Check @sub_push.
Check @sub_push_respects.
Check @sub_reindex_push.
Check @pow_mem.
Check @char_mem.
Check @char_sub_inj.
Check @eval_pow_square.
Check @mem_pow_square.
Check @ex_mono.
Check @pow_ex_mono.
Check @IsPullback_sym.
Check @second_pullback.
Check @first_second_pullback.
Check @bc_mono.
Check @coreflexive_equalizer_pullback.
Check @pow_bc.
Check @pow_fmap_comp.
Check @pow_split_coequalizer.
Check @pow_PreservesReflexiveCoequalizers.
Check @pow_equivalence.
Check @power_object_monadic.
Check @topos_HasEqualizers.
Check @topos_finitely_complete.
Check @op_HasCoequalizers.
Check @op_HasReflexiveCoequalizers.
Check @EM_Terminal.
Check @EM_HasPullbacks.
Check @EM_Pullback.
Check @em_pb_carrier.
Check @em_pb_p1.
Check @em_pb_p2.
Check @topos_Initial.
Check @topos_HasPullbacks_op.
Check @topos_Cocartesian.
Check @topos_HasCoequalizers.
Check @topos_HasPushouts.
Check @topos_has_finite_colimits.
Check @is_pullback_jointly_monic.
Check @pullback_transport_leg.
Check @IsPullback_transport.
Check @HasPullbacks_transport.
Check @Partial_r.
Check @InternalHomFunctor.
Check @Exp_Functor.
Check @Terminal_transport.
Check @crude_monadicity.
Check @Cartesian_of_HasPullbacks_Terminal.
Check @Terminal_Limit.
Check @Cartesian_Limit.
Check @relations_iso.
Check @SubObj.
Check @Ω.
Check @curry.
Check @flip.

(* The exponential 自函子 Structure/Cartesian/Closed/Adjunction.v
 covariant base exponent held FIXED, so 对象
 action (-)^Ω not Ω^(-). （已译） *)
Example p405_exp_functor_obj (a : C) :
  fobj[@Exp_Functor C _ _ Ω] a = exponent_obj Ω a := eq_refl.

(** ** (2) TYPING negatives *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition p405_partial_r_typing : C^op ⟶ C :=
  Partial_r (InternalHomFunctor C) Ω.

(* The 伴随 runs P^op ⊣ P not other way round, even though
 both ascriptions well formed TYPES. （已译） *)
Fail Definition p405_swapped_handedness : PowF ⊣ Opposite_Functor PowF :=
  pow_adjunction.

(** ** (3) CONVERSION negatives *)

(* The exponential 自函子's 对象 action not power 对象. （已译） *)
Fail Example p405_exp_is_pow (a : C) :
  fobj[@Exp_Functor C _ _ Ω] a = Pow a := eq_refl.

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p405_relations_strict {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f = pow_relations f := eq_refl.

Example p405_relations_equiv {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f ≈ pow_relations f := pow_aor_is_relations f.

End ProbeGeneral.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、topos、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniverseBoundary.

Universes uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).

Fail Check (Terminal_Limit Cu).

Fail Check (Cartesian_Limit Cu).

(* Controls at the very same declared levels. *)
Check (@Terminal_transport Cu Cu).
Check (@crude_monadicity Cu Cu).
Check (@Cartesian_of_HasPullbacks_Terminal Cu).
Check (@HasPullbacks_transport Cu Cu).
Check (@topos_has_finite_colimits Cu).
Check (@power_object_monadic Cu).
Check (@topos_finitely_complete Cu).
Check (Cu^op).
Check (@Terminal Cu).

End UniverseBoundary.

(*
   本节说明伴随、topos、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RelationsBoundary.

Universes vo vh.
Constraint vo < vh.

Context (Cv : Category@{vo vh vh}).
Context (Hv : @ElementaryTopos Cv).

Check (@Pow Cv Hv).
Check (@PowF Cv Hv).
Check (@pow_aor Cv Hv).
Check (@pow_self_adjoint Cv Hv).
Check (@pow_adjunction Cv Hv).
Check (@power_object_monadic Cv Hv).
Check (@topos_has_finite_colimits Cv Hv).
Check (@SubObj Cv).

Fail Check (@relations_iso Cv Hv).

Fail Check (@pow_relations Cv Hv).

End RelationsBoundary.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DonorBoundary.

Universes wo wh wp.
Constraint wh < wp.

Context (Cw : Category@{wo wh wp}) (x y z P : Cw)
  (f : x ~> z) (g : y ~> z) (p1 : P ~> x) (p2 : P ~> y).

(* Controls at the very same declared levels. *)
Check (x ~> y).
Check (id[x]).
Check @ElementaryTopos.
Check @IsPullback.
Check @HasPullbacks.

Fail Check (@ElementaryTopos Cw).

Fail Check (@IsPullback Cw x y z f g P p1 p2).

Fail Check (@HasPullbacks Cw).

End DonorBoundary.

(** ** (5) The FinSet sanity check *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition cartesian_unique_iso {D : Category}
        (P Q : @Cartesian D) (a b : D) :
  @product_obj D P a b ≅ @product_obj D Q a b := {|
  to   := @fork D Q _ a b (@exl D P a b) (@exr D P a b) ;
  from := @fork D P _ a b (@exl D Q a b) (@exr D Q a b)
|}.
Next Obligation.
  rewrite <- (@fork_exl_exr D Q a b).
  apply (@ump_products D Q _ a b _ _ _); split.
  - rewrite comp_assoc, (@exl_fork D Q _ a b _ _),
            (@exl_fork D P _ a b _ _).
    reflexivity.
  - rewrite comp_assoc, (@exr_fork D Q _ a b _ _),
            (@exr_fork D P _ a b _ _).
    reflexivity.
Qed.
Next Obligation.
  rewrite <- (@fork_exl_exr D P a b).
  apply (@ump_products D P _ a b _ _ _); split.
  - rewrite comp_assoc, (@exl_fork D P _ a b _ _),
            (@exl_fork D Q _ a b _ _).
    reflexivity.
  - rewrite comp_assoc, (@exr_fork D P _ a b _ _),
            (@exr_fork D Q _ a b _ _).
    reflexivity.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinSet_derived_HasCoequalizers : HasCoequalizers FinSet :=
  @topos_HasCoequalizers FinSet FinSet_Topos.

Definition FinSet_derived_finite_colimits :
  @Initial FinSet * @Cocartesian FinSet * @HasCoequalizers FinSet
    * @HasPushouts FinSet :=
  @topos_has_finite_colimits FinSet FinSet_Topos.

Check (@power_object_monadic FinSet FinSet_Topos : Monadic PowF).

(*
   本节说明单子、（余）极限、topos相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example p405_finset_initial_strict :
  @initial_obj FinSet (@topos_Initial FinSet FinSet_Topos)
    = @initial_obj FinSet FinSet_Initial := eq_refl.

Definition finset_derived_initial_iso :
  @initial_obj FinSet (@topos_Initial FinSet FinSet_Topos)
    ≅[FinSet] @initial_obj FinSet FinSet_Initial :=
  initial_unique (@topos_Initial FinSet FinSet_Topos) FinSet_Initial.

(* 相关说明。 （已译） *)
Definition finset_derived_coproduct_iso (m n : FinSet) :
  @Coprod FinSet (@topos_Cocartesian FinSet FinSet_Topos) m n
    ≅[FinSet^op] @Coprod FinSet FinSet_Cocartesian m n :=
  @cartesian_unique_iso (FinSet^op)
    (@topos_Cocartesian FinSet FinSet_Topos) FinSet_Cocartesian m n.

(* 相关说明。 （已译） *)
Definition finset_derived_pushout_iso {x y z : FinSet}
           (f : x ~> y) (g : x ~> z) :
  pushout_apex (@pushout FinSet (@topos_HasPushouts FinSet FinSet_Topos)
                  x y z f g)
    ≅[FinSet^op] pushout_apex (@pushout FinSet FinSet_HasPushouts x y z f g)
  := @pullback_unique (FinSet^op) y z x f g _ _.

Check @FinSet_Topos.
Check @FinSet_Initial.
Check @FinSet_Cocartesian.
Check @FinSet_HasPushouts.
Check @initial_unique.
Check @pullback_unique.
Check @ump_products.
Check @cartesian_unique_iso.
Check @finset_derived_initial_iso.
Check @finset_derived_coproduct_iso.
Check @finset_derived_pushout_iso.
Check @FinSet_derived_HasCoequalizers.
Check @FinSet_derived_finite_colimits.
