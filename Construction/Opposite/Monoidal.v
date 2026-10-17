Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Comonoid.Hom.

Generalizable All Variables.

(* * * Monoidal structure opposite 范畴 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/monoidal+category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section OppositeMonoidal.

Context {C : Category}.

#[local] Obligation Tactic := intros.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Opposite_Tensor `{M : @Monoidal C} :
  C^op ∏ C^op ⟶ C^op := {|
  fobj := fun p => (fst p ⨂[M] snd p)%object;
  fmap := fun x y f => (fst f ⨂[M] snd f)
|}.
Next Obligation.
  (* fmap respects ≈, componentwise. *)
  intros f g e; destruct e as [e1 e2]; simpl.
  apply bimap_respects; assumption.
Qed.
Next Obligation.
  simpl.
  apply bimap_id_id.
Qed.
Next Obligation.
  simpl.
  apply bimap_comp.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Monoidal_op `{M : @Monoidal C} : @Monoidal (C^op) := {|
  I            := @I C M;
  tensor       := Opposite_Tensor;
  unit_left    := fun x => Isomorphism_Opposite (@unit_left C M x);
  unit_right   := fun x => Isomorphism_Opposite (@unit_right C M x);
  tensor_assoc := fun x y z => Isomorphism_Opposite (@tensor_assoc C M x y z)
|}.
Next Obligation.
  (* to_unit_left_natural in C^op = from_unit_left_natural in C *)
  simpl; symmetry; apply from_unit_left_natural.
Qed.
Next Obligation.
  (* from_unit_left_natural in C^op = to_unit_left_natural in C *)
  simpl; symmetry; apply to_unit_left_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply from_unit_right_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply to_unit_right_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply from_tensor_assoc_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply to_tensor_assoc_natural.
Qed.
Next Obligation.
  (* Triangle C^op: ρ⁻¹ ⨂ id ≈ α⁻¹ ∘ (id ⨂ λ⁻¹) C, triangle
 恒等 C solved inverse unitors. （已译） *)
  simpl.
  assert (X : (@unit_right C M x)⁻¹ ⨂ to (@unit_left C M y)
                ≈ (@tensor_assoc C M x I y)⁻¹).
  { symmetry.
    rewrite <- (bimap_id_right_left
                  ((@unit_right C M x)⁻¹) (to (@unit_left C M y))).
    rewrite inverse_triangle_identity.
    rewrite comp_assoc.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    cat. }
  rewrite <- X.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  cat.
Qed.
Next Obligation.
  (* Pentagon in C^op = the inverse pentagon of C. *)
  simpl.
  rewrite comp_assoc.
  apply inverse_pentagon_identity.
Qed.

(* A braiding C transports C^op: braid at (x, y) C^op the
 braid at (y, x) C. Naturality dualizes 自然性, two
 hexagon identities exchange roles. （已译） *)
Program Definition Braided_op `{B : @BraidedMonoidal C} :
  @BraidedMonoidal (C^op) := {|
  braided_is_monoidal := Monoidal_op;
  braid := fun x y => @braid C B y x
|}.
Next Obligation.
  (* braid_natural in C^op = braid_natural in C, sides exchanged. *)
  intros; simpl.
  symmetry.
  rewrite !comp_assoc.
  exact (@braid_natural C B w z h y x g).
Qed.
Next Obligation.
  (* hexagon_identity in C^op = hexagon_identity_sym in C. *)
  simpl.
  rewrite !comp_assoc.
  exact (@hexagon_identity_sym C B y z x).
Qed.
Next Obligation.
  (* hexagon_identity_sym in C^op = hexagon_identity in C. *)
  simpl.
  rewrite !comp_assoc.
  exact (@hexagon_identity C B z x y).
Qed.

(* 相关说明。 （已译） *)
Program Definition Symmetric_op `{S : @SymmetricMonoidal C} :
  @SymmetricMonoidal (C^op) := {|
  symmetric_is_braided := Braided_op
|}.
Next Obligation.
  simpl.
  apply braid_invol.
Qed.

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Comonoid_to_op_Monoid `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid C M x) : @Monoid (C^op) Monoidal_op x := {|
  mu  := delta[Cm];
  eta := epsilon[Cm]
|}.
Next Obligation.
  (* mu_assoc in C^op unfolds to delta_coassoc in C. *)
  simpl.
  rewrite comp_assoc.
  apply delta_coassoc.
Qed.
Next Obligation.
  simpl.
  apply delta_counit_left.
Qed.
Next Obligation.
  simpl.
  apply delta_counit_right.
Qed.

Program Definition Monoid_to_op_Comonoid `{M : @Monoidal C} {x : C}
  (Mn : @Monoid C M x) : @Comonoid (C^op) Monoidal_op x := {|
  delta   := mu[Mn];
  epsilon := eta[Mn]
|}.
Next Obligation.
  (* delta_coassoc in C^op unfolds to mu_assoc in C. *)
  simpl.
  rewrite comp_assoc.
  apply mu_assoc.
Qed.
Next Obligation.
  simpl.
  apply mu_unit_left.
Qed.
Next Obligation.
  simpl.
  apply mu_unit_right.
Qed.

Program Definition op_Monoid_to_Comonoid `{M : @Monoidal C} {x : C}
  (Mn : @Monoid (C^op) Monoidal_op x) : @Comonoid C M x := {|
  delta   := mu[Mn];
  epsilon := eta[Mn]
|}.
Next Obligation.
  spose (@mu_assoc (C^op) Monoidal_op x Mn) as X.
  rewrite <- comp_assoc.
  apply X.
Qed.
Next Obligation.
  spose (@mu_unit_left (C^op) Monoidal_op x Mn) as X.
  apply X.
Qed.
Next Obligation.
  spose (@mu_unit_right (C^op) Monoidal_op x Mn) as X.
  apply X.
Qed.

Program Definition op_Comonoid_to_Monoid `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid (C^op) Monoidal_op x) : @Monoid C M x := {|
  mu  := delta[Cm];
  eta := epsilon[Cm]
|}.
Next Obligation.
  spose (@delta_coassoc (C^op) Monoidal_op x Cm) as X.
  rewrite <- comp_assoc.
  apply X.
Qed.
Next Obligation.
  spose (@delta_counit_left (C^op) Monoidal_op x Cm) as X.
  apply X.
Qed.
Next Obligation.
  spose (@delta_counit_right (C^op) Monoidal_op x Cm) as X.
  apply X.
Qed.

(* 相关说明。 （已译） *)

Lemma Comonoid_op_roundtrip `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid C M x) :
  delta[op_Monoid_to_Comonoid (Comonoid_to_op_Monoid Cm)] ≈ delta[Cm]
    ∧ epsilon[op_Monoid_to_Comonoid (Comonoid_to_op_Monoid Cm)] ≈ epsilon[Cm].
Proof. split; reflexivity. Qed.

Lemma Monoid_op_roundtrip `{M : @Monoidal C} {x : C}
  (Mn : @Monoid C M x) :
  mu[op_Comonoid_to_Monoid (Monoid_to_op_Comonoid Mn)] ≈ mu[Mn]
    ∧ eta[op_Comonoid_to_Monoid (Monoid_to_op_Comonoid Mn)] ≈ eta[Mn].
Proof. split; reflexivity. Qed.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ComonoidHom_to_op_MonoidHom `{M : @Monoidal C} {x y : C}
      {Cx : @Comonoid C M x} {Cy : @Comonoid C M y} {f : x ~{C}~> y} :
  ComonoidHom Cx Cy f →
  MonoidHom (Comonoid_to_op_Monoid Cy) (Comonoid_to_op_Monoid Cx) f.
Proof.
  intros F; destruct F as [Fd Fe].
  split; simpl.
  - apply Fd.
  - apply Fe.
Qed.

Lemma op_MonoidHom_to_ComonoidHom `{M : @Monoidal C} {x y : C}
      {Mx : @Monoid (C^op) Monoidal_op x} {My : @Monoid (C^op) Monoidal_op y}
      {f : x ~{C^op}~> y} :
  MonoidHom Mx My f →
  ComonoidHom (op_Monoid_to_Comonoid My) (op_Monoid_to_Comonoid Mx) f.
Proof.
  intros F; destruct F as [Fm Fe].
  split; simpl.
  - apply Fm.
  - apply Fe.
Qed.

#[local] Obligation Tactic := cat_simpl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Mon_op_to_Comon_op `{M : @Monoidal C} :
  @Mon (C^op) Monoidal_op ⟶ (@Comon C M)^op := {|
  fobj := fun X => (`1 X; op_Monoid_to_Comonoid `2 X);
  fmap := fun X Y f => (`1 f; op_MonoidHom_to_ComonoidHom `2 f)
|}.

Program Definition Comon_op_to_Mon_op `{M : @Monoidal C} :
  (@Comon C M)^op ⟶ @Mon (C^op) Monoidal_op := {|
  fobj := fun X => (`1 X; Comonoid_to_op_Monoid `2 X);
  fmap := fun X Y f => (`1 f; ComonoidHom_to_op_MonoidHom `2 f)
|}.

End OppositeMonoidal.
