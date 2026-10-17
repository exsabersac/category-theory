(** * Watts' theorem through SAFT: Mac Lane's contravariant text form and
      Exercise 3's covariant form *)

(*
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 nLab:      https://ncatlab.org/nlab/show/cogenerator
 nLab:      https://ncatlab.org/nlab/show/injective+object

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Projective.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Character.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Instance.Mod.HomTensor.
Require Import Category.Instance.Mod.Cogenerator.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mod.Watts.Unconditional.

Generalizable All Variables.

(** ** 1. The forgetful functor is additive *)

Definition RMod_Forget_Ab_additive@{a c p o x b +} (R : RingObject@{a c p}) :
  @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c} (RMod_AbEnriched R)
    Ab_AbEnriched (RMod_Forget_Ab R).
Proof. constructor. intros x y f g m; simpl; reflexivity. Defined.

(** ** 2. Watts' theorem, the book's text form *)

(*
   本节说明 Watts 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition watts_theorem_sets@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* The book's first step, verbatim: T itself has a left adjoint. *)
Definition watts_theorem_adjoint@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { F : Ab@{a c} ⟶ (RMod@{o x c c c} R)^op & F ⊣ T } :=
  SAFT_wellpowered T (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    contT (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* The theorem: T ≅ hom_R(−, A) as Ab-valued functors.  The representation
   enters ONCE, ascribed, so that no second elaboration of it adds a
   universe equation (the header's UNIVERSES). *)
Definition watts_theorem@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  @watt_ab_repr ((RMod R)^op)
    (LocallyPropositional_op (RMod_LocallyPropositional R))
    (AbEnriched_op (RMod_AbEnriched R)) T AF
    (watts_theorem_sets T contT U
       : Representable@{ra rt pa o c} (Ab_Forget ◯ T)).

(* The representing object IS the SAFT representation's. *)
Example watts_theorem_obj@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = @repr_obj _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)) :=
  eq_refl.

(* ...and each component of the Ab-level isomorphism is the Sets-level
   representation's component, unchanged: additivity adds proofs, not
   data. *)
Example watts_theorem_to_at@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) (M : RMod@{o x c c c} R)
  (f : M ~{RMod@{o x c c c} R}~> projT1 (watts_theorem T AF contT U)) :
  cmon_map (transform[to (projT2 (watts_theorem T AF contT U))] M) f
    = transform[to (@represented _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)))] M f :=
  eq_refl.

(** ** 3. Exercise 3, the covariant form *)

(* SAFT at RMod R: complete, well-powered under [U], cogenerated by [G]. *)
Definition watts_ex3_sets@{a c p o x b g pk pa ra rt +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T) (RMod_Complete R)
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    G (RMod_WellPowered_untruncate U).

Definition watts_ex3@{a c p o x b g pk pa ra rt +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) T } :=
  watt_ab_repr (RMod_AbEnriched R) T AF
    (watts_ex3_sets T contT G U
       : Representable@{ra rt pa o c} (Ab_Forget ◯ T)).

(*
   本节说明 Watts 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition watts_ex3_QZ@{r o x b pk pa ra rt +}
  {R : RingObject@{r r r}} (T : RMod@{o x r r r} R ⟶ Ab@{b r})
  (AF : @AdditiveFunctor (RMod@{o x r r r} R) Ab@{b r}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o r b r pk r pa r}
             (RMod@{o x r r r} R) Ab@{b r} T)
  (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates)
  (U : Untruncate@{r}) :
  { A : RMod@{o x r r r} R &
    @Isomorphism (@Fun (RMod@{o x r r r} R) Ab@{b r})
      (HomAb (RMod_AbEnriched R) A) T } :=
  watts_ex3 T AF contT
    (snd (QZ_injective_cogenerator R HI HC)) U.

(* Only the cogenerating half of Exercise 2(b) is consumed: the
   cogenerator does not mention [HI]. *)
Example watts_ex3_QZ_cogenerator@{r o x +}
  {R : RingObject@{r r r}} (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates) :
  snd (QZ_injective_cogenerator R HI HC)
    = coext_cogenerator R (QZ_Cogenerator HC) := eq_refl.

(** ** 4. Witnesses *)

(* Exercise 3 at the forgetful functor, continuous by #449's creation. *)
Definition watts_ex3_forget@{a c p o x b g +}
  (R : RingObject@{a c p}) (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) } :=
  watts_ex3 (RMod_Forget_Ab R) (RMod_Forget_Ab_additive R)
    (Continuous_PreservesImageLimit (RMod_Forget_Ab_creates_continuous R)) G U.

(* Instance/Mod.v builds [RMod_Forget R] directly rather than as the
   composite; the two agree up to identity components. *)
Definition RMod_Forget_equiv@{a c p o x b +} (R : RingObject@{a c p}) :
  (RMod_Forget R : RMod@{o x a p c} R ⟶ Sets@{c x})
    ≈ (@Compose _ Ab@{b c} _ Ab_Forget (RMod_Forget_Ab R)
         : RMod@{o x a p c} R ⟶ Sets@{c x}).
Proof.
  exists (fun M => iso_id).
  intros M N f m; simpl. reflexivity.
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition watt_at_forget@{c o x b +} (R : RingObject@{c c c}) :
  @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
    (HomAb (RMod_AbEnriched R) (Ring_RMod R)) (RMod_Forget_Ab R) :=
  watt_ab_iso (RMod_AbEnriched R) (RMod_Forget_Ab R)
    (RMod_Forget_Ab_additive R)
    (Representable_transport (equiv_iso (RMod_Forget_equiv R))
       (rmod_representable R)).

(* The representing object is R itself, up to isomorphism: two
   representations of isomorphic functors. *)
Definition watts_ex3_forget_obj@{c o x b g +}
  (R : RingObject@{c c c}) (G : Cogenerator@{g o c} (RMod@{o x c c c} R))
  (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    ≅[RMod@{o x c c c} R] Ring_RMod R :=
  repr_induced_iso (rmod_representable R)
    (watts_ex3_sets (RMod_Forget_Ab R)
       (Continuous_PreservesImageLimit
          (RMod_Forget_Ab_creates_continuous R)) G U)
    (equiv_iso (RMod_Forget_equiv R)).

(* The text form's witness: M ↦ Hom_Ab(U M, A), contravariant in M.  The
   intermediate [Ab] is at RMod's object universe, where
   [coex_adjunction]'s left adjoint lands. *)
Definition HomAbForget@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) : (RMod@{o x c c c} R)^op ⟶ Ab@{b c} :=
  @CoHomAb Ab@{o c} _ Ab_AbEnriched A ◯ Opposite_Functor (RMod_Forget_Ab R).

Definition HomAbForget_additive@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{b c}
    (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}).
Proof.
  constructor. intros x y f g h m; simpl.
  apply (cmon_map_plus h).
Defined.

(* [RMod_Forget_Ab R] is a left adjoint, so its opposite is a right
   adjoint and continuous; [CoHomAb A] is continuous by
   Functor/Representable/Additive.v's [CoHomAb_continuous]. *)
Definition HomAbForget_continuous@{c o x b +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Definition watts_theorem_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  { A' : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
      (CoHomAb (RMod_AbEnriched R) A')
      (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) } :=
  watts_theorem (HomAbForget R A) (HomAbForget_additive R A)
    (Continuous_PreservesImageLimit (HomAbForget_continuous R A)) U.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coext_representable@{c o x b ra rt +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  Representable@{ra rt x o c}
    (@Compose _ Ab@{b c} _ Ab_Forget
       (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})).
Proof.
  unshelve econstructor.
  - exact (CoextObj R A).
  - apply equiv_iso.
    exists (fun M => iso_sym (@adj _ _ _ _ (coex_adjunction R) M A)).
    intros M N f g; simpl.
    intros a r.
    pose proof (rm_map_smul f r a) as H1.
    assert (H2 : cmon_map (rm_hom g) (cmon_map (rm_hom f) (rm_smul N r a))
                 ≈ cmon_map (rm_hom g) (rm_smul M r (cmon_map (rm_hom f) a)))
      by (apply proper_morphism; exact H1).
    specialize (H2 (rig_one (ring_rig R))).
    pose proof (rm_map_smul g r (cmon_map (rm_hom f) a) (rig_one (ring_rig R)))
      as H3.
    simpl in H2, H3.
    symmetry.
    etransitivity; [exact H2|].
    etransitivity; [exact H3|].
    apply proper_morphism. apply rig_mul_one_l.
Defined.

(* SAFT's representing object at the witness is the coextension, up to
   isomorphism in RMod R... *)
Definition watts_theorem_coext_obj@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  projT1 (watts_theorem_coext R A U
           : { A' : RMod@{o x c c c} R &
               @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
                 (CoHomAb (RMod_AbEnriched R) A')
                 (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) })
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (repr_unique_iso (coext_representable R A)
       (watts_theorem_sets (HomAbForget R A)
          (Continuous_PreservesImageLimit (HomAbForget_continuous R A)) U)).

(* ...and so Exercise 2(a)'s hom_ℤ(R, A), the module [HomZL R_R A]. *)
Definition watts_theorem_coext_obj_2a@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  projT1 (watts_theorem_coext R A U
           : { A' : RMod@{o x c c c} R &
               @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
                 (CoHomAb (RMod_AbEnriched R) A')
                 (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) })
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  iso_compose (iso_sym (homzl_coext_iso A)) (watts_theorem_coext_obj R A U).

(** ** 5. Mac Lane's last step: the representing object is F ℤ *)

(* ℤ is read as the free abelian group on one point, [FreeAb SetsOne]
   (Instance/Ab/Free.v).  [Ab_Forget] and [Ab_Forget ◯ Id[Ab]] agree up to
   identity components. *)
Definition Ab_Forget_Id_equiv@{a c x +} :
  (Ab_Forget : Ab@{a c} ⟶ Sets@{c x})
    ≈ (@Compose _ Ab@{a c} _ Ab_Forget Id[Ab@{a c}]
         : Ab@{a c} ⟶ Sets@{c x}).
Proof.
  exists (fun M => iso_id).
  intros M N f m; simpl. reflexivity.
Defined.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ab_hom_Z_iso@{a c +} :
  @Isomorphism (@Fun Ab@{a c} Ab@{a c})
    (HomAb Ab_AbEnriched (FreeAb SetsOne)) Id[Ab@{a c}] :=
  watt_ab_iso Ab_AbEnriched Id[Ab] Id_AdditiveFunctor
    (Representable_transport (equiv_iso Ab_Forget_Id_equiv)
       (representable_of_left_adjoint Ab_Forget free_ab_adjunction)).

(* C = F ℤ, up to isomorphism in RMod R, F being the left adjoint of
   [watts_theorem_adjoint]: FreeAb ⊣ Ab_Forget composed with F ⊣ T
   represents [Ab_Forget ◯ T] by F (FreeAb SetsOne), and two
   representations of one functor have isomorphic representing objects. *)
Definition watts_theorem_Fz@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    ≅[RMod@{o x c c c} R]
  fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (@repr_unique_iso ((RMod R)^op) (Ab_Forget ◯ T)
       (representable_of_left_adjoint (Ab_Forget ◯ T)
          (Adjunction_Compose free_ab_adjunction
             (projT2 (watts_theorem_adjoint T contT U))))
       (watts_theorem_sets T contT U
          : Representable@{ra rt pa o c} (Ab_Forget ◯ T))).

(** ** 6. What the unconditional theorem subsumes *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition watts_theorem_via_unconditional@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  watts_theorem_unconditional T AF (PreservesImageLimit_Continuous contT).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition watts_unconditional_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (repr_unique_iso (coext_representable R A)
       (RModop_continuous_representable _
          (continuous_compose (HomAbForget_continuous R A)
             Ab_Forget_creates_continuous))).

(* ...and so Exercise 2(a)'s hom_ℤ(R, A), the module [HomZL R_R A]. *)
Definition watts_unconditional_coext_2a@{c o x b +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  iso_compose (iso_sym (homzl_coext_iso A)) (watts_unconditional_coext R A).
