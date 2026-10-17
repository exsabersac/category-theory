Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(*
   本文件给出加性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Set Default Proof Using "All".

(*
   nLab: https://ncatlab.org/nlab/show/additive+functor
   https://ncatlab.org/nlab/show/adjoint+functor

   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdjunctionInjectivity.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Lemma adj_to_inj {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj f ≈ to adj g → f ≈ g.
Proof.
  intro H.
  rewrite <- (to_adj_comp_law f), <- (to_adj_comp_law g).
  now apply from_adj_respects.
Qed.

Lemma adj_from_inj {x : D} {y : C} (f g : x ~{D}~> U y) :
  from adj f ≈ from adj g → f ≈ g.
Proof.
  intro H.
  rewrite <- (from_adj_comp_law f), <- (from_adj_comp_law g).
  now apply to_adj_respects.
Qed.

End AdjunctionInjectivity.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdditiveTranspose.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(* * *** The forward transpose, given additive 右伴随

 ⌊f⌋ ≈ fmap[U] f ∘ η ([to_adj_unit]), so additivity ⌊−⌋ is
 additivity fmap[U] followed bilinearity 复合 in
 left 论元. （已译） *)

Section ForwardTranspose.

Context `{AU : @AdditiveFunctor C D AC AD U}.

Theorem to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) ≈ padd (to adj f) (to adj g).
Proof.
  rewrite !to_adj_unit.
  rewrite (@fmap_padd C D AC AD U AU _ _ f g).
  apply compose_padd_right.
Qed.

Theorem to_adj_pzero {x : D} {y : C} :
  to adj (@pzero C _ (F x) y) ≈ pzero.
Proof.
  rewrite to_adj_unit.
  rewrite (@fmap_pzero C D AC AD U AU (F x) y).
  apply compose_pzero_left.
Qed.

Theorem to_adj_abneg {x : D} {y : C} (f : F x ~{C}~> y) :
  to adj (abneg f) ≈ abneg (to adj f).
Proof.
  rewrite !to_adj_unit.
  rewrite (@fmap_abneg C D AC AD U AU _ _ f).
  apply compose_abneg_right.
Qed.

End ForwardTranspose.

(* * *** The inverse transpose, given additive 左伴随

 ⌈f⌉ ≈ ε ∘ fmap[F] f ([from_adj_counit]); 镜像 above,
 bilinearity used right 论元 instead. （已译） *)

Section BackwardTranspose.

Context `{AF : @AdditiveFunctor D C AD AC F}.

Theorem from_adj_padd {x : D} {y : C} (f g : x ~{D}~> U y) :
  from adj (padd f g) ≈ padd (from adj f) (from adj g).
Proof.
  rewrite !from_adj_counit.
  rewrite (@fmap_padd D C AD AC F AF _ _ f g).
  apply compose_padd_left.
Qed.

Theorem from_adj_pzero {x : D} {y : C} :
  from adj (@pzero D _ x (U y)) ≈ pzero.
Proof.
  rewrite from_adj_counit.
  rewrite (@fmap_pzero D C AD AC F AF x (U y)).
  apply compose_pzero_right.
Qed.

Theorem from_adj_abneg {x : D} {y : C} (f : x ~{D}~> U y) :
  from adj (abneg f) ≈ abneg (from adj f).
Proof.
  rewrite !from_adj_counit.
  rewrite (@fmap_abneg D C AD AC F AF _ _ f).
  apply compose_abneg_left.
Qed.

End BackwardTranspose.

End AdditiveTranspose.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section LeftAdjointAdditive.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.
Context `{AU : @AdditiveFunctor C D AC AD U}.

(* The transpose of fmap[F] h is η ∘ h.  Half of [fmap_from_adj_unit]
   read forwards, isolated because it is used three times below. *)
Lemma to_adj_fmap_left {x y : D} (h : x ~{D}~> y) :
  to adj (fmap[F] h) ≈ unit ∘ h.
Proof.
  rewrite (fmap_from_adj_unit h).
  apply from_adj_comp_law.
Qed.

Theorem left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g).
Proof.
  apply adj_to_inj.
  rewrite to_adj_fmap_left.
  rewrite to_adj_padd.
  rewrite !to_adj_fmap_left.
  apply compose_padd_left.
Qed.

(* Mac Lane's Theorem 3, as an inhabitant of the class rather than as
   an equation: it may be handed to [Compose_AdditiveFunctor], to
   [fmap_pzero]/[fmap_abneg], or to the backward-transpose section
   above.（标题）（已译） *)
#[export] Instance left_adjoint_additive :
  @AdditiveFunctor D C AD AC F := {|
  fmap_padd := @left_adjoint_fmap_padd
|}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary adj_from_padd {x : D} {y : C} (f g : x ~{D}~> U y) :
  from adj (padd f g) ≈ padd (from adj f) (from adj g).
Proof. exact (from_adj_padd f g). Qed.

Corollary adj_from_pzero {x : D} {y : C} :
  from adj (@pzero D _ x (U y)) ≈ pzero.
Proof. exact from_adj_pzero. Qed.

Corollary adj_from_abneg {x : D} {y : C} (f : x ~{D}~> U y) :
  from adj (abneg f) ≈ abneg (from adj f).
Proof. exact (from_adj_abneg f). Qed.

End LeftAdjointAdditive.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomGroups.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hom_ab {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  AbObject := {|
  ab_cmon :=
    {| cmon_setoid :=
         {| carrier := @hom C x y; is_setoid := @homset C x y |};
       cmon_zero := @pzero C _ x y;
       cmon_plus := @padd C _ x y;
       cmon_plus_respects := @padd_respects C _ x y;
       cmon_plus_assoc := @padd_assoc C _ x y;
       cmon_plus_comm := @padd_comm C _ x y;
       cmon_plus_zero_l := @padd_zero_left C _ x y;
       cmon_prop := locally_prop x y |};
  ab_neg := @abneg C AC x y;
  ab_neg_respects := @abneg_respects C AC x y;
  (* [padd_abneg] is stated as f + (−f) ≈ 0 while [ab_neg_left] wants
     (−f) + f ≈ 0; commutativity of the enrichment reconciles them. *)
  ab_neg_left := fun f =>
    Equivalence_Transitive _ _ _
      (@padd_comm C _ x y (@abneg C AC x y f) f)
      (@padd_abneg C AC x y f)
|}.

(*
   本节说明 Additive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example hom_ab_carrier {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  carrier (cmon_setoid (hom_ab AC x y)) = (x ~{C}~> y).
Proof. exact eq_refl. Qed.

Example hom_ab_plus {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  cmon_plus (hom_ab AC x y) = @padd C _ x y.
Proof. exact eq_refl. Qed.

Example hom_ab_zero {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  cmon_zero (hom_ab AC x y) = @pzero C _ x y.
Proof. exact eq_refl. Qed.

Example hom_ab_neg {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  ab_neg (hom_ab AC x y) = @abneg C AC x y.
Proof. exact eq_refl. Qed.

Context {C D : Category}.
(* Both ambients must be locally propositional; see [hom_ab] above. *)
Context {LPC : LocallyPropositional C}.
Context {LPD : LocallyPropositional D}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.
Context `{AU : @AdditiveFunctor C D AC AD U}.

(* 相关说明。 （已译） *)
Definition adj_to_ab (x : D) (y : C) :
  AbHom (hom_ab AC (F x) y) (hom_ab AD x (U y)).
Proof.
  unshelve econstructor.
  - exact (to (@adj C D F U A x y)).
  - exact (@to_adj_pzero C D AC AD F U A AU x y).
  - exact (@to_adj_padd C D AC AD F U A AU x y).
Defined.

(* And inverse transpose, additive Theorem 3 —
 no second 假设 F taken. （已译） *)
Definition adj_from_ab (x : D) (y : C) :
  AbHom (hom_ab AD x (U y)) (hom_ab AC (F x) y).
Proof.
  unshelve econstructor.
  - exact (from (@adj C D F U A x y)).
  - exact (@adj_from_pzero C D AC AD F U A AU x y).
  - exact (@adj_from_padd C D AC AD F U A AU x y).
Defined.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adj_hom_ab_iso (x : D) (y : C) :
  @Isomorphism Ab (hom_ab AC (F x) y) (hom_ab AD x (U y)).
Proof.
  unshelve econstructor.
  - exact (adj_to_ab x y).
  - exact (adj_from_ab x y).
  - intro f; apply from_adj_comp_law.
  - intro f; apply to_adj_comp_law.
Defined.

(* The two legs transposes nose, not merely equivalent
 them: group 同构 set 同构 its
 structure exhibited, nothing was rebuilt. （已译） *)
Example adj_hom_ab_iso_to (x : D) (y : C) (f : F x ~{C}~> y) :
  cmon_map (to (adj_hom_ab_iso x y)) f = to (@adj C D F U A x y) f.
Proof. exact eq_refl. Qed.

Example adj_hom_ab_iso_from (x : D) (y : C) (f : x ~{D}~> U y) :
  cmon_map (from (adj_hom_ab_iso x y)) f = from (@adj C D F U A x y) f.
Proof. exact eq_refl. Qed.

End HomGroups.

(*
   本节说明伴随、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Preadditive_op {C : Category} (P : @Preadditive C) :
  @Preadditive (C^op) := {|
  padd := fun x y => @padd C P y x;
  pzero := fun x y => @pzero C P y x;
  padd_respects := fun x y => @padd_respects C P y x;
  padd_assoc := fun x y => @padd_assoc C P y x;
  padd_comm := fun x y => @padd_comm C P y x;
  padd_zero_left := fun x y => @padd_zero_left C P y x;
  compose_padd_left := fun x y z h f g =>
    @compose_padd_right C P z y x f g h;
  compose_padd_right := fun x y z f g h =>
    @compose_padd_left C P z y x h f g;
  compose_pzero_left := fun x y z f => @compose_pzero_right C P z y x f;
  compose_pzero_right := fun x y z f => @compose_pzero_left C P z y x f
|}.

Program Definition AbEnriched_op {C : Category} (AC : AbEnriched C) :
  AbEnriched (C^op) := {|
  abenriched_preadditive := Preadditive_op (@abenriched_preadditive C AC);
  abneg := fun x y => @abneg C AC y x;
  abneg_respects := fun x y => @abneg_respects C AC y x;
  padd_abneg := fun x y => @padd_abneg C AC y x
|}.

(* The opposite enrichment original one read at swapped
 endpoints, definitionally — what makes transport of
 additivity below 证明-free. （已译） *)
Example padd_op_is_padd {C : Category} (P : @Preadditive C) (x y : C) :
  @padd (C^op) (Preadditive_op P) x y = @padd C P y x.
Proof. exact eq_refl. Qed.

Example abneg_op_is_abneg {C : Category} (AC : AbEnriched C) (x y : C) :
  @abneg (C^op) (AbEnriched_op AC) x y = @abneg C AC y x.
Proof. exact eq_refl. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AdditiveFunctor_op {C D : Category}
  {AC : AbEnriched C} {AD : AbEnriched D} (G : C ⟶ D)
  (AG : @AdditiveFunctor C D AC AD G) :
  @AdditiveFunctor (C^op) (D^op) (AbEnriched_op AC) (AbEnriched_op AD)
    (Opposite_Functor G).
Proof.
  constructor.
  intros x y f g.
  exact (@fmap_padd C D AC AD G AG _ _ f g).
Defined.

Definition AdditiveFunctor_unop {C D : Category}
  {AC : AbEnriched C} {AD : AbEnriched D} (G : C ⟶ D)
  (AG : @AdditiveFunctor (C^op) (D^op) (AbEnriched_op AC)
          (AbEnriched_op AD) (Opposite_Functor G)) :
  @AdditiveFunctor C D AC AD G.
Proof.
  constructor.
  intros x y f g.
  exact (@fmap_padd (C^op) (D^op) (AbEnriched_op AC) (AbEnriched_op AD)
           (Opposite_Functor G) AG _ _ f g).
Defined.

Section RightAdjointAdditive.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (AF : @AdditiveFunctor D C AD AC F).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition right_adjoint_additive : @AdditiveFunctor C D AC AD U :=
  AdditiveFunctor_unop U
    (@left_adjoint_additive (D^op) (C^op) (AbEnriched_op AD)
       (AbEnriched_op AC) (Opposite_Functor U) (Opposite_Functor F)
       (Opposite_Adjunction F U A) (AdditiveFunctor_op F AF)).

End RightAdjointAdditive.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoproductBiproduct.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.

Section Bridge.

Context {x y b : C}.
Context (i1 : x ~> b) (i2 : y ~> b) (p1 : b ~> x) (p2 : b ~> y).
Context (H11 : p1 ∘ i1 ≈ id) (H22 : p2 ∘ i2 ≈ id).
Context (H12 : p1 ∘ i2 ≈ zero_mor) (H21 : p2 ∘ i1 ≈ zero_mor).
Context (Hco : ∀ (z : C) (f : x ~> z) (g : y ~> z),
                 ∃! h : b ~> z, (h ∘ i1 ≈ f) ∧ (h ∘ i2 ≈ g)).

(* Two morphisms out of b that agree on both injections agree. *)
Lemma additive_coprod_ext {z : C} (u v : b ~> z) :
  u ∘ i1 ≈ v ∘ i1 → u ∘ i2 ≈ v ∘ i2 → u ≈ v.
Proof.
  intros Hl Hr.
  transitivity (unique_obj (Hco z (u ∘ i1) (u ∘ i2))).
  - symmetry.
    apply (uniqueness (Hco z (u ∘ i1) (u ∘ i2)) u).
    split; reflexivity.
  - apply (uniqueness (Hco z (u ∘ i1) (u ∘ i2)) v).
    split; [ now symmetry | now symmetry ].
Qed.

(* The 恒等 decomposition. Both sides restrict i1 along i1 and
 i2 along i2, so [additive_coprod_ext] identifies them. （已译） *)
Lemma coprod_id_decomp : padd (i1 ∘ p1) (i2 ∘ p2) ≈ id.
Proof.
  apply additive_coprod_ext.
  - rewrite compose_padd_right.
    rewrite <- !comp_assoc.
    rewrite H11, H21.
    rewrite id_right, zero_mor_left.
    rewrite <- pzero_zero_mor.
    now rewrite padd_zero_right, id_left.
  - rewrite compose_padd_right.
    rewrite <- !comp_assoc.
    rewrite H12, H22.
    rewrite id_right, zero_mor_left.
    rewrite <- pzero_zero_mor.
    now rewrite padd_zero_left, id_left.
Qed.

(* 相关说明。 （已译） *)
Definition coprod_is_product (z : C) (f : z ~> x) (g : z ~> y) :
  ∃! h : z ~> b, (p1 ∘ h ≈ f) ∧ (p2 ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := padd (i1 ∘ f) (i2 ∘ g) |}.
  - split.
    + rewrite compose_padd_left.
      rewrite !comp_assoc.
      rewrite H11, H12.
      rewrite id_left, zero_mor_right.
      rewrite <- pzero_zero_mor.
      apply padd_zero_right.
    + rewrite compose_padd_left.
      rewrite !comp_assoc.
      rewrite H21, H22.
      rewrite id_left, zero_mor_right.
      rewrite <- pzero_zero_mor.
      apply padd_zero_left.
  - intros v [Hl Hr].
    symmetry.
    transitivity (padd (i1 ∘ p1) (i2 ∘ p2) ∘ v).
    + now rewrite coprod_id_decomp, id_left.
    + rewrite compose_padd_right.
      rewrite <- !comp_assoc.
      now rewrite Hl, Hr.
Defined.

Definition biproduct_of_coproduct : Biproduct x y := {|
  biproduct_obj := b;
  bi_inl := i1;
  bi_inr := i2;
  bi_exl := p1;
  bi_exr := p2;
  bi_exl_inl := H11;
  bi_exr_inr := H22;
  bi_exl_inr := H12;
  bi_exr_inl := H21;
  bi_is_product := coprod_is_product;
  bi_is_coproduct := Hco
|}.

(* The bridge keeps data it was given: 对象 all four
 structure maps supplied ones nose, so consumer may
 read them back without comparison 态射. （已译） *)
Example bridge_inl_strict : bi_inl biproduct_of_coproduct = i1.
Proof. exact eq_refl. Qed.

End Bridge.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma padd_copair_diag {a c : C} (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B ≈ padd f g.
Proof.
  unfold bi_diag.
  rewrite bi_copair_pair.
  now rewrite !id_right.
Qed.

End CoproductBiproduct.

(*
   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section LeftAdjointBiproducts.

Context {C D : Category}.
Context `{ZC : @ZeroObject C}.
Context `{ZD : @ZeroObject D}.
Context `{PC : @Preadditive C}.
Context `{PD : @Preadditive D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(* Hom-sets out image D's 始对象 singletons: the
 transpose carries them isomorphically onto hom-sets out the
 始对象 itself, where [zero_unique] applies. （已译） *)
Lemma adj_image_initial_unique {z : C}
  (h k : F (@initial_obj D (@zero_initial D ZD)) ~{C}~> z) : h ≈ k.
Proof.
  apply adj_to_inj.
  apply (@zero_unique D (@zero_initial D ZD)).
Qed.

(*
   本节说明伴随、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma adj_fmap_pzero {a c : D} :
  fmap[F] (@pzero D PD a c) ≈ @pzero C PC (F a) (F c).
Proof.
  rewrite pzero_zero_mor.
  unfold zero_mor.
  rewrite <- comp_assoc.
  rewrite fmap_comp.
  rewrite (adj_image_initial_unique
             (fmap[F] (@zero D (@zero_initial D ZD) c)) pzero).
  apply compose_pzero_left.
Qed.

Corollary adj_fmap_zero_mor {a c : D} :
  fmap[F] (@zero_mor D ZD a c) ≈ @zero_mor C ZC (F a) (F c).
Proof.
  rewrite <- pzero_zero_mor.
  rewrite adj_fmap_pzero.
  apply pzero_zero_mor.
Qed.

Section ImageBiproduct.

Context {a a' : D}.
Context (B : Biproduct a a').

(* 相关说明。 （已译） *)
Definition adj_image_is_coproduct (z : C)
  (f : F a ~> z) (g : F a' ~> z) :
  ∃! h : F (biproduct_obj B) ~> z,
    (h ∘ fmap[F] (bi_inl B) ≈ f) ∧ (h ∘ fmap[F] (bi_inr B) ≈ g).
Proof.
  unshelve refine
    {| unique_obj :=
         from adj (bi_copair B (to adj f) (to adj g)) |}.
  - split.
    + apply adj_to_inj.
      rewrite to_adj_nat_l.
      rewrite from_adj_comp_law.
      apply bi_copair_inl.
    + apply adj_to_inj.
      rewrite to_adj_nat_l.
      rewrite from_adj_comp_law.
      apply bi_copair_inr.
  - intros v [Hl Hr].
    apply adj_to_inj.
    rewrite from_adj_comp_law.
    apply bi_copair_unique.
    + rewrite <- to_adj_nat_l.
      now apply to_adj_respects.
    + rewrite <- to_adj_nat_l.
      now apply to_adj_respects.
Defined.

(*
   本节说明 Additive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adj_image_biproduct : Biproduct (F a) (F a').
Proof.
  unshelve eapply biproduct_of_coproduct.
  - exact (fobj[F] (biproduct_obj B)).
  - exact (fmap[F] (bi_inl B)).
  - exact (fmap[F] (bi_inr B)).
  - exact (fmap[F] (bi_exl B)).
  - exact (fmap[F] (bi_exr B)).
  - rewrite <- fmap_comp, bi_exl_inl.
    apply fmap_id.
  - rewrite <- fmap_comp, bi_exr_inr.
    apply fmap_id.
  - rewrite <- fmap_comp, bi_exl_inr.
    apply adj_fmap_zero_mor.
  - rewrite <- fmap_comp, bi_exr_inl.
    apply adj_fmap_zero_mor.
  - exact adj_image_is_coproduct.
Defined.

(*
   本节说明 Additive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example image_biproduct_obj :
  biproduct_obj adj_image_biproduct = fobj[F] (biproduct_obj B).
Proof. exact eq_refl. Qed.

Example image_biproduct_inl :
  bi_inl adj_image_biproduct = fmap[F] (bi_inl B).
Proof. exact eq_refl. Qed.

Example image_biproduct_exl :
  bi_exl adj_image_biproduct = fmap[F] (bi_exl B).
Proof. exact eq_refl. Qed.

End ImageBiproduct.

End LeftAdjointBiproducts.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BiproductTransfer.

Context {C D : Category}.
Context `{ZC : @ZeroObject C}.
Context `{ZD : @ZeroObject D}.
Context `{PC : @Preadditive C}.
Context `{PD : @Preadditive D}.
Context {G : D ⟶ C}.

Theorem fmap_padd_of_preserved_coproduct {a c : D} (B : Biproduct a a)
  (Hz : ∀ u v : D, fmap[G] (@zero_mor D ZD u v) ≈ zero_mor)
  (Hco : ∀ (z : C) (u : G a ~> z) (v : G a ~> z),
     ∃! h : fobj[G] (biproduct_obj B) ~{C}~> z,
       (h ∘ fmap[G] (bi_inl B) ≈ u) ∧ (h ∘ fmap[G] (bi_inr B) ≈ v))
  (f g : a ~> c) :
  fmap[G] (padd f g) ≈ padd (fmap[G] f) (fmap[G] g).
Proof.
  assert (H11 : fmap[G] (bi_exl B) ∘ fmap[G] (bi_inl B) ≈ id)
    by (rewrite <- fmap_comp, bi_exl_inl; apply fmap_id).
  assert (H22 : fmap[G] (bi_exr B) ∘ fmap[G] (bi_inr B) ≈ id)
    by (rewrite <- fmap_comp, bi_exr_inr; apply fmap_id).
  assert (H12 : fmap[G] (bi_exl B) ∘ fmap[G] (bi_inr B) ≈ zero_mor)
    by (rewrite <- fmap_comp, bi_exl_inr; apply Hz).
  assert (H21 : fmap[G] (bi_exr B) ∘ fmap[G] (bi_inl B) ≈ zero_mor)
    by (rewrite <- fmap_comp, bi_exr_inl; apply Hz).
  (*
   本节说明 Additive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  pose (GB := biproduct_of_coproduct
                (fmap[G] (bi_inl B)) (fmap[G] (bi_inr B))
                (fmap[G] (bi_exl B)) (fmap[G] (bi_exr B))
                H11 H22 H12 H21 Hco).
  assert (Ecop : fmap[G] (bi_copair B f g)
                   ≈ bi_copair GB (fmap[G] f) (fmap[G] g)).
  { symmetry.
    apply (bi_copair_unique GB (fmap[G] f) (fmap[G] g)
             (fmap[G] (bi_copair B f g))).
    - transitivity (fmap[G] (bi_copair B f g ∘ bi_inl B)).
      + rewrite fmap_comp; reflexivity.
      + now rewrite bi_copair_inl.
    - transitivity (fmap[G] (bi_copair B f g ∘ bi_inr B)).
      + rewrite fmap_comp; reflexivity.
      + now rewrite bi_copair_inr. }
  assert (Ediag : fmap[G] (bi_diag B) ≈ bi_diag GB).
  { unfold bi_diag.
    symmetry.
    apply (bi_pair_unique GB id id (fmap[G] (bi_pair B id id))).
    - transitivity (fmap[G] (bi_exl B ∘ bi_pair B id id)).
      + rewrite fmap_comp; reflexivity.
      + rewrite bi_exl_pair; apply fmap_id.
    - transitivity (fmap[G] (bi_exr B ∘ bi_pair B id id)).
      + rewrite fmap_comp; reflexivity.
      + rewrite bi_exr_pair; apply fmap_id. }
  rewrite <- (padd_copair_diag B f g).
  rewrite fmap_comp.
  rewrite Ecop, Ediag.
  apply (padd_copair_diag GB (fmap[G] f) (fmap[G] g)).
Qed.

End BiproductTransfer.

(* * *** Riehl's 推论 at one pair 对象

 No additivity assumed F U: source
 carries biproduct domain itself. （已译） *)

Section LeftAdjointPadd.

Context {C D : Category}.
Context `{ZC : @ZeroObject C}.
Context `{ZD : @ZeroObject D}.
Context `{PC : @Preadditive C}.
Context `{PD : @Preadditive D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Theorem left_adjoint_fmap_padd_biproduct {a c : D} (B : Biproduct a a)
  (f g : a ~> c) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g).
Proof.
  apply (fmap_padd_of_preserved_coproduct B).
  - intros u v; apply adj_fmap_zero_mor.
  - apply (adj_image_is_coproduct B).
Qed.

End LeftAdjointPadd.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition left_adjoint_additive_of_biproducts
  {C D : Category} {AC : AbEnriched C} {AD : AbEnriched D}
  `{ZC : @ZeroObject C} `{ZD : @ZeroObject D}
  {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  (HB : @HasBiproducts D ZD) :
  @AdditiveFunctor D C AD AC F.
Proof.
  constructor.
  intros a c f g.
  exact (@left_adjoint_fmap_padd_biproduct C D ZC ZD
           (@abenriched_preadditive C AC) (@abenriched_preadditive D AD)
           F U A a c (@biproduct D ZD HB a a) f g).
Defined.
