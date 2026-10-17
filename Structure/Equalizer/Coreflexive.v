Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/equalizer

   本文件给出等化子结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Coreflexive pairs *)

(* 相关说明。 （已译） *)
Record CoreflexivePair {C : Category} {x y : C} (f g : x ~> y) := {
  corefl_retract   : y ~> x;                    (* the common retraction *)
  corefl_retract_f : corefl_retract ∘ f ≈ id;   (* it retracts f *)
  corefl_retract_g : corefl_retract ∘ g ≈ id    (* and g *)
}.

Arguments corefl_retract   {_ _ _ _ _} _.
Arguments corefl_retract_f {_ _ _ _ _} _.
Arguments corefl_retract_g {_ _ _ _ _} _.

(* A category has coreflexive equalizers when every coreflexive pair
   carries an elementary equalizer (Structure/Equalizer/Fork.v's
   [IsEqualizer]).  Compare [HasEqualizers], which asks the same of every
   parallel pair, and Structure/Coequalizer/Reflexive.v's
   [HasReflexiveCoequalizers], the dual. *)
Class HasCoreflexiveEqualizers (C : Category) := {
  coreflexive_eq {x y : C} (f g : x ~> y) :
    CoreflexivePair f g → ∃ (q : C) (e : q ~> x), IsEqualizer f g q e
}.

Lemma common_retraction_coreflexive {C : Category} {x y : C} (f g : x ~> y)
  (r : y ~> x) (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id) : CoreflexivePair f g.
Proof.
  exact {| corefl_retract   := r
         ; corefl_retract_f := Hf
         ; corefl_retract_g := Hg |}.
Defined.

(* Every category with equalizers has coreflexive ones. *)
#[export] Instance HasEqualizers_HasCoreflexiveEqualizers
  {C : Category} `{H : @HasEqualizers C} : HasCoreflexiveEqualizers C := {|
  coreflexive_eq := fun x y f g _ => @equalizer C H x y f g
|}.

(* Two equations with no quantification over the ambient category, so
   arbitrary functors preserve coreflexivity — as they do reflexivity
   (Structure/Coequalizer/Reflexive.v's [functor_preserves_reflexive]). *)
Theorem functor_preserves_coreflexive {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  CoreflexivePair f g → CoreflexivePair (fmap[F] f) (fmap[F] g).
Proof.
  intros R.
  unshelve refine {| corefl_retract := fmap[F] (corefl_retract R) |}.
  - rewrite <- fmap_comp, (corefl_retract_f R); apply fmap_id.
  - rewrite <- fmap_comp, (corefl_retract_g R); apply fmap_id.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明 Coreflexive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CoreflexivePair_of_op {C : Category} {x y : C} {f g : x ~> y}
  (R : @ReflexivePair (C^op) y x f g) : CoreflexivePair f g :=
  @Build_CoreflexivePair C x y f g
    (refl_section R) (refl_section_f R) (refl_section_g R).

Definition op_ReflexivePair_of_Coreflexive {C : Category} {x y : C}
  {f g : x ~> y} (R : CoreflexivePair f g) : @ReflexivePair (C^op) y x f g :=
  @Build_ReflexivePair (C^op) y x f g
    (corefl_retract R) (corefl_retract_f R) (corefl_retract_g R).

Example corefl_op_round {C : Category} {x y : C} {f g : x ~> y}
  (R : CoreflexivePair f g) :
  CoreflexivePair_of_op (op_ReflexivePair_of_Coreflexive R) = R := eq_refl.

Example op_corefl_round {C : Category} {x y : C} {f g : x ~> y}
  (R : @ReflexivePair (C^op) y x f g) :
  op_ReflexivePair_of_Coreflexive (CoreflexivePair_of_op R) = R := eq_refl.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HasCoreflexiveEqualizers_of_op {C : Category}
  (H : HasReflexiveCoequalizers (C^op)) : HasCoreflexiveEqualizers C.
Proof.
  constructor; intros x y f g R.
  destruct (@reflexive_coeq (C^op) H y x f g
              (op_ReflexivePair_of_Coreflexive R)) as [q [e Eq]].
  exists q, e.
  exact (IsEqualizer_op_of_IsCoequalizer Eq).
Defined.

Definition op_HasReflexiveCoequalizers_of_Coreflexive {C : Category}
  (H : HasCoreflexiveEqualizers C) : HasReflexiveCoequalizers (C^op).
Proof.
  constructor; intros x y f g R.
  destruct (@coreflexive_eq C H y x f g (CoreflexivePair_of_op R))
    as [q [e Eq]].
  exists q, e.
  exact (@IsCoequalizer_of_IsEqualizer_op (C^op) x y f g q e Eq).
Defined.

(* 相关说明。 （已译） *)

Section Manes.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).

(* The 恒等箭头 at x index FULL arrow family of
 Structure/Limit/FromProducts.v, codomain x nose. （已译） *)
Example id_index_cod (x : J) : aix_cod (mk_arrow (@id J x)) = x := eq_refl.
Example id_index_dom (x : J) : aix_dom (mk_arrow (@id J x)) = x := eq_refl.
Example id_index_arr (x : J) : aix_arr (mk_arrow (@id J x)) = @id J x := eq_refl.

(* Mac Lane's candidate retraction: map 进入 对象 product whose
 component at x arrow product's projection at 恒等 x. （已译） *)
Definition pe_retract : pe_arrow_product HP F ~> pe_obj_product HP F :=
  unique_obj (iprod_desc (pe_obj_product_ump HP F)
    (fun x : J => pe_arrow_proj HP F (mk_arrow (@id J x)))).

Lemma pe_retract_proj (x : J) :
  pe_obj_proj HP F x ∘ pe_retract ≈ pe_arrow_proj HP F (mk_arrow (@id J x)).
Proof.
  exact (unique_property (iprod_desc (pe_obj_product_ump HP F)
    (fun x : J => pe_arrow_proj HP F (mk_arrow (@id J x)))) x).
Qed.

Lemma pe_retract_s : pe_retract ∘ pe_s HP F ≈ id.
Proof.
  apply (pe_iprod_ext (pe_obj_product_ump HP F)); intro x.
  rewrite comp_assoc, pe_retract_proj.
  rewrite (pe_s_proj HP F (mk_arrow (@id J x))).
  rewrite id_right.
  reflexivity.
Qed.

Lemma pe_retract_t : pe_retract ∘ pe_t HP F ≈ id.
Proof.
  apply (pe_iprod_ext (pe_obj_product_ump HP F)); intro x.
  rewrite comp_assoc, pe_retract_proj.
  rewrite (pe_t_proj HP F (mk_arrow (@id J x))).
  simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

(* Mac Lane's hint, as a proved lemma. *)
Definition pe_coreflexive : CoreflexivePair (pe_s HP F) (pe_t HP F) :=
  common_retraction_coreflexive _ _ pe_retract pe_retract_s pe_retract_t.

(** ** Manes' criterion *)

Context (HE : HasCoreflexiveEqualizers C).

Definition mc_equalizer :=
  coreflexive_eq (pe_s HP F) (pe_t HP F) pe_coreflexive.

Definition mc_apex : C := `1 mc_equalizer.

Definition mc_incl : mc_apex ~> pe_obj_product HP F := `1 (`2 mc_equalizer).

Definition mc_IsEqualizer : IsEqualizer (pe_s HP F) (pe_t HP F) mc_apex mc_incl
  := `2 (`2 mc_equalizer).

(* The limit FromProducts.v's construction fed coreflexive
 equalizer place arbitrary one; core 所消耗 the
 elementary [IsEqualizer], never class. （已译） *)
Definition mc_cone : Cone F :=
  pe_cone F (pe_obj_proj HP F) (pe_obj_product_ump HP F) ArrowIx_Generates
    (pe_arrow_proj HP F) (pe_arrow_product_ump HP F)
    (pe_s HP F) (pe_t HP F) (pe_s_proj HP F) (pe_t_proj HP F)
    mc_incl mc_IsEqualizer.

Definition mc_limiting : IsLimitCone mc_cone :=
  pe_limiting F (pe_obj_proj HP F) (pe_obj_product_ump HP F) ArrowIx_Generates
    (pe_arrow_proj HP F) (pe_arrow_product_ump HP F)
    (pe_s HP F) (pe_t HP F) (pe_s_proj HP F) (pe_t_proj HP F)
    mc_incl mc_IsEqualizer.

Definition mc_limit : Limit F := limitcone_limit mc_cone mc_limiting.

Example mc_limit_apex :
  vertex_obj[@limit_cone _ _ _ mc_limit] = mc_apex := eq_refl.

Example mc_limit_leg (x : J) :
  cone_leg (@limit_cone _ _ _ mc_limit) x = pe_obj_proj HP F x ∘ mc_incl
  := eq_refl.

End Manes.

(* Mac Lane §V.2 Exercise 1(a): small products and coreflexive equalizers
   give completeness. *)
Definition Complete_from_coreflexive_equalizers {C : Category}
  (HP : HasIndexedProducts C) (HE : HasCoreflexiveEqualizers C) : @Complete C :=
  fun J F => mc_limit HP F HE.

(* 相关说明。 （已译） *)

(* Part (b) about REFLEXIVE pairs (a common right inverse), not the
 coreflexive pairs part (a); any cartesian 范畴 section is
 exactly factorization diagonal [id △ id] through [f △ g]. （已译） *)
Section CartesianHalf.

Context {C : Category} `{@Cartesian C}.
Context {x y : C} (f g : x ~> y).

Lemma fork_diagonal_of_reflexive (s : y ~> x) (Hf : f ∘ s ≈ id)
  (Hg : g ∘ s ≈ id) : (f △ g) ∘ s ≈ id △ id.
Proof.
  rewrite <- fork_comp.
  rewrite Hf, Hg.
  reflexivity.
Qed.

Lemma reflexive_of_fork_diagonal (s : y ~> x) (Hd : (f △ g) ∘ s ≈ id △ id) :
  (f ∘ s ≈ id) * (g ∘ s ≈ id).
Proof.
  split.
  - rewrite <- (exl_fork f g), <- comp_assoc, Hd.
    apply exl_fork.
  - rewrite <- (exr_fork f g), <- comp_assoc, Hd.
    apply exr_fork.
Qed.

Definition ReflexivePair_of_diagonal_factors :
  (∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id) → ReflexivePair f g :=
  fun sd => let (s, Hd) := sd in
    let (Hf, Hg) := reflexive_of_fork_diagonal s Hd in
    common_section_reflexive f g s Hf Hg.

Definition diagonal_factors_of_ReflexivePair (R : ReflexivePair f g) :
  ∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id :=
  (refl_section R;
     fork_diagonal_of_reflexive (refl_section R)
       (refl_section_f R) (refl_section_g R)).

Definition ReflexivePair_iff_diagonal_factors :
  ReflexivePair f g ↔ (∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id) :=
  (diagonal_factors_of_ReflexivePair, ReflexivePair_of_diagonal_factors).

End CartesianHalf.

(** ** Exercise 1(b) in Sets *)

Section SetsHalf.

Context {X Y : SetoidObject}.
Context (f g : X ~{Sets}~> Y).

(* 相关说明。 （已译） *)
Definition diagonal_in_image : Type :=
  ∀ b : Y, ∃ a : X, (f a ≈ b) * (g a ≈ b).

(* 相关说明。 （已译） *)
Definition diagonal_in_image_of_reflexive (R : ReflexivePair f g) :
  diagonal_in_image :=
  fun b => (refl_section R b; (refl_section_f R b, refl_section_g R b)).

(* The converse needs the chosen witnesses to respect ≈, which the
   statement of [diagonal_in_image] does not supply: [∃] is [sigT], so a
   choice function is present, but a Sets morphism also needs
   [proper_morphism]. *)
Definition diagonal_section (D : diagonal_in_image)
  (Hproper : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) : Y ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun b => `1 (D b) |}.
  repeat intro; now apply Hproper.
Defined.

Definition reflexive_of_diagonal_in_image (D : diagonal_in_image)
  (Hproper : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) :
  ReflexivePair f g.
Proof.
  unshelve refine (common_section_reflexive f g (diagonal_section D Hproper) _ _).
  - intro b; exact (fst (`2 (D b))).
  - intro b; exact (snd (`2 (D b))).
Defined.

(* The 态射-level reading through Instance/Sets/Image.v: diagonal
 factors through mono leg (epi, mono) factorization the
 induced map. Unconditional direction. （已译） *)
Definition diagonal_through_image (R : ReflexivePair f g) :
  ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
    Sets_Image_mono (f △ g) ∘ d ≈ id △ id.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun b =>
        ((f △ g) (refl_section R b); (refl_section R b; _)) |}.
    + reflexivity.
    + repeat intro.
      simpl.
      split; apply proper_morphism; now apply proper_morphism.
  - intro b; simpl.
    split; [exact (refl_section_f R b) | exact (refl_section_g R b)].
Defined.

(*
   本节说明 Coreflexive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition diagonal_in_image_of_through_image
  (d : Y ~{Sets}~> Sets_Image (f △ g))
  (Hd : Sets_Image_mono (f △ g) ∘ d ≈ id △ id) : diagonal_in_image.
Proof.
  intro b.
  exists (`1 (`2 (d b))).
  destruct (`2 (d b)) as [a Ha]; simpl in *.
  destruct (Hd b) as [H1 H2]; simpl in *.
  destruct Ha as [Ha1 Ha2]; simpl in *.
  split; [now rewrite Ha1 | now rewrite Ha2].
Defined.

Definition through_image_of_diagonal_in_image (D : diagonal_in_image) :
  ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
    Sets_Image_mono (f △ g) ∘ d ≈ id △ id.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun b => ((b, b); (`1 (D b); _)) |}.
    + split; simpl; [exact (fst (`2 (D b))) | exact (snd (`2 (D b)))].
    + repeat intro; simpl; split; assumption.
  - intro b; simpl; split; reflexivity.
Defined.

(*
   本节说明 Coreflexive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition diagonal_in_image_iff_through_image :
  diagonal_in_image
    ↔ (∃ d : Y ~{Sets}~> Sets_Image (f △ g),
         Sets_Image_mono (f △ g) ∘ d ≈ id △ id) :=
  (through_image_of_diagonal_in_image,
   fun dd : ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
              Sets_Image_mono (f △ g) ∘ d ≈ id △ id =>
     diagonal_in_image_of_through_image (`1 dd) (`2 dd)).

End SetsHalf.

(** ** Non-vacuity, and its limit *)

(* [Sets] has coreflexive equalizers — but the only route in the tree is
   through the STRONGER [HasEqualizers Sets], so Manes' criterion is
   instantiated here only where Theorem 1's hypothesis already holds. *)
Definition Sets_HasCoreflexiveEqualizers : HasCoreflexiveEqualizers Sets :=
  @HasEqualizers_HasCoreflexiveEqualizers Sets
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks).

Definition Sets_Complete_via_Manes : @Complete Sets :=
  Complete_from_coreflexive_equalizers
    Sets_HasIndexedProducts Sets_HasCoreflexiveEqualizers.
