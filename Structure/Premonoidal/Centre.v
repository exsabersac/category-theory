Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.
Require Import Category.Structure.Premonoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
    nLab: https://ncatlab.org/nlab/show/premonoidal+category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PremonoidalCentre.

Context {C : Category}.
Context `{B : @Binoidal C}.
Context `{P : @Premonoidal C B}.

(* Section-local 对象-level tensor, exactly in
 Structure/Premonoidal.v: unscoped notation makes ⊗ mean OBJECT
 tensor everywhere inside section, while 态射-level interleaved
 tensoring always written [composite_ff']. （已译） *)
Local Notation "x ⊗ y" := (tensor x y)
  (at level 30, right associativity).

(*
   本节说明 Centre 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem composite_ff'_central {x x' y y'} {f : x ~> y} {f' : x' ~> y'} :
  central f → central f' → central (composite_ff' f f').
Proof using B C P.
  intros cf cf' a b h.
  split.
  - (* Square 1, on (x ⊗ x') ⊗ a ~~> (y ⊗ y') ⊗ b. *)
    destruct (cf (x' ⊗ a) (x' ⊗ b) (fmap[inj_right x'] h)) as [cfh _].
    destruct (cf' a b h) as [cf'h _].
    apply (iso_to_monic (@premon_assoc C B P y y' b)).
    unfold composite_ff'.
    rewrite !fmap_comp.
    rewrite !comp_assoc.
    transitivity
      ((((y ⋊ (y' ⋊ h)) ∘ (y ⋊ (f' ⋉ a))) ∘ (f ⋉ (x' ⊗ a)))
         ∘ to (@premon_assoc C B P x x' a)).
    { (* 相关说明。 （已译） *)
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ to (@premon_assoc C B P y x' b))
            ∘ ((f ⋉ x') ⋉ b)) ∘ ((x ⊗ x') ⋊ h)).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_middle. }
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ (f ⋉ (x' ⊗ b)))
            ∘ to (@premon_assoc C B P x x' b)) ∘ ((x ⊗ x') ⋊ h)).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_left. }
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ (f ⋉ (x' ⊗ b))) ∘ (x ⋊ (x' ⋊ h)))
           ∘ to (@premon_assoc C B P x x' a)).
      { rewrite <- !comp_assoc.
        do 2 (apply compose_respects; [reflexivity|]).
        symmetry; apply premon_assoc_natural_right. }
      transitivity
        ((((y ⋊ (f' ⋉ b)) ∘ (y ⋊ (x' ⋊ h))) ∘ (f ⋉ (x' ⊗ a)))
           ∘ to (@premon_assoc C B P x x' a)).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        apply cfh. }
      do 2 (apply compose_respects; [|reflexivity]).
      rewrite <- !fmap_comp.
      now rewrite cf'h. }
    { (* Right side: the same three naturality squares, no swaps. *)
      symmetry.
      transitivity
        ((((y ⋊ (y' ⋊ h)) ∘ to (@premon_assoc C B P y y' a))
            ∘ ((y ⋊ f') ⋉ a)) ∘ ((f ⋉ x') ⋉ a)).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_right. }
      transitivity
        ((((y ⋊ (y' ⋊ h)) ∘ (y ⋊ (f' ⋉ a)))
            ∘ to (@premon_assoc C B P y x' a)) ∘ ((f ⋉ x') ⋉ a)).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_middle. }
      rewrite <- !comp_assoc.
      do 2 (apply compose_respects; [reflexivity|]).
      symmetry; apply premon_assoc_natural_left. }
  - (* Square 2, on a ⊗ (x ⊗ x') ~~> b ⊗ (y ⊗ y'). *)
    destruct (cf a b h) as [_ cf2].
    destruct (cf' (a ⊗ y) (b ⊗ y) (fmap[inj_left y] h)) as [_ cf'2].
    apply (iso_from_monic (@premon_assoc C B P b y y')).
    unfold composite_ff'.
    rewrite !fmap_comp.
    rewrite !comp_assoc.
    transitivity
      (((((b ⊗ y) ⋊ f') ∘ ((b ⋊ f) ⋉ x')) ∘ ((h ⋉ x) ⋉ x'))
         ∘ from (@premon_assoc C B P a x x')).
    { (* 相关说明。 （已译） *)
      transitivity
        (((((h ⋉ y) ⋉ y') ∘ from (@premon_assoc C B P a y y'))
            ∘ (a ⋊ (y ⋊ f'))) ∘ (a ⋊ (f ⋉ x'))).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_left_from. }
      transitivity
        (((((h ⋉ y) ⋉ y') ∘ ((a ⊗ y) ⋊ f'))
            ∘ from (@premon_assoc C B P a y x')) ∘ (a ⋊ (f ⋉ x'))).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_right_from. }
      transitivity
        (((((h ⋉ y) ⋉ y') ∘ ((a ⊗ y) ⋊ f')) ∘ ((a ⋊ f) ⋉ x'))
           ∘ from (@premon_assoc C B P a x x')).
      { rewrite <- !comp_assoc.
        do 2 (apply compose_respects; [reflexivity|]).
        symmetry; apply premon_assoc_natural_middle_from. }
      transitivity
        (((((b ⊗ y) ⋊ f') ∘ ((h ⋉ y) ⋉ x')) ∘ ((a ⋊ f) ⋉ x'))
           ∘ from (@premon_assoc C B P a x x')).
      { do 2 (apply compose_respects; [|reflexivity]).
        apply cf'2. }
      apply compose_respects; [|reflexivity].
      rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      transitivity (((h ⋉ y) ∘ (a ⋊ f)) ⋉ x').
      { symmetry.
        exact (@fmap_comp C C (@inj_left C B x') (a ⊗ x) (a ⊗ y) (b ⊗ y)
                 (fmap[@inj_left C B y] h) (fmap[@inj_right C B a] f)). }
      transitivity (((b ⋊ f) ∘ (h ⋉ x)) ⋉ x').
      { now rewrite cf2. }
      exact (@fmap_comp C C (@inj_left C B x') (a ⊗ x) (b ⊗ x) (b ⊗ y)
               (fmap[@inj_right C B b] f) (fmap[@inj_left C B x] h)). }
    { (* 相关说明。 （已译） *)
      symmetry.
      transitivity
        (((((b ⊗ y) ⋊ f') ∘ from (@premon_assoc C B P b y x'))
            ∘ (b ⋊ (f ⋉ x'))) ∘ (h ⋉ (x ⊗ x'))).
      { do 2 (apply compose_respects; [|reflexivity]).
        symmetry; apply premon_assoc_natural_right_from. }
      transitivity
        (((((b ⊗ y) ⋊ f') ∘ ((b ⋊ f) ⋉ x'))
            ∘ from (@premon_assoc C B P b x x')) ∘ (h ⋉ (x ⊗ x'))).
      { apply compose_respects; [|reflexivity].
        rewrite <- !comp_assoc.
        apply compose_respects; [reflexivity|].
        symmetry; apply premon_assoc_natural_middle_from. }
      rewrite <- !comp_assoc.
      do 2 (apply compose_respects; [reflexivity|]).
      symmetry; apply premon_assoc_natural_left_from. }
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Centre_lift_iso {p q : @Centre C B} (i : `1 p ≅[C] `1 q)
           (ci : central (to i)) : p ≅[@Centre C B] q :=
  @Build_Isomorphism (@Centre C B) p q
    (to i; ci)
    (from i; central_iso_from i ci)
    (iso_to_from i)
    (iso_from_to i).

(* 相关说明。 （已译） *)

Definition Centre_Tensor_obj (p : @Centre C B ∏ @Centre C B) :
  @Centre C B := (`1 (fst p) ⊗ `1 (snd p); ttt).

Definition Centre_Tensor_fmap (p q : @Centre C B ∏ @Centre C B)
           (fg : p ~{@Centre C B ∏ @Centre C B}~> q) :
  Centre_Tensor_obj p ~{@Centre C B}~> Centre_Tensor_obj q :=
  (composite_ff' (`1 (fst fg)) (`1 (snd fg));
   composite_ff'_central (`2 (fst fg)) (`2 (snd fg))).

Lemma Centre_Tensor_respects (p q : @Centre C B ∏ @Centre C B) :
  Proper (equiv ==> equiv) (Centre_Tensor_fmap p q).
Proof.
  intros fg hk [e1 e2]; simpl.
  apply composite_ff'_respects; assumption.
Qed.

Lemma Centre_Tensor_id (p : @Centre C B ∏ @Centre C B) :
  Centre_Tensor_fmap p p (@id (@Centre C B ∏ @Centre C B) p) ≈ id.
Proof.
  simpl.
  rewrite composite_id_left.
  exact (@fmap_id C C (@inj_right C B (`1 (fst p))) (`1 (snd p))).
Qed.

(* Joint functoriality: centre one-sided interchange
 [composite_ff'_comp_l] receives 中心性 假设 the
 hom witness first component. （已译） *)
Lemma Centre_Tensor_comp (p q r : @Centre C B ∏ @Centre C B)
      (fg : q ~{@Centre C B ∏ @Centre C B}~> r)
      (hk : p ~{@Centre C B ∏ @Centre C B}~> q) :
  Centre_Tensor_fmap p r (fg ∘ hk)
    ≈ Centre_Tensor_fmap q r fg ∘ Centre_Tensor_fmap p q hk.
Proof.
  simpl.
  apply composite_ff'_comp_l.
  exact (`2 (fst fg)).
Qed.

Definition Centre_Tensor : (@Centre C B ∏ @Centre C B) ⟶ @Centre C B := {|
  fobj := Centre_Tensor_obj;
  fmap := Centre_Tensor_fmap;
  fmap_respects := Centre_Tensor_respects;
  fmap_id := Centre_Tensor_id;
  fmap_comp := Centre_Tensor_comp
|}.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Centre_Monoidal : @Monoidal (@Centre C B) :=
  @Build_Monoidal (@Centre C B)
    (@premon_I C B P; ttt)
    Centre_Tensor
    (fun p =>
       @Centre_lift_iso (Centre_Tensor_obj ((@premon_I C B P; ttt), p)) p
         (@premon_unit_left C B P (`1 p))
         (@premon_unit_left_central C B P (`1 p)))
    (fun p =>
       @Centre_lift_iso (Centre_Tensor_obj (p, (@premon_I C B P; ttt))) p
         (@premon_unit_right C B P (`1 p))
         (@premon_unit_right_central C B P (`1 p)))
    (fun p q r =>
       @Centre_lift_iso
         (Centre_Tensor_obj (Centre_Tensor_obj (p, q), r))
         (Centre_Tensor_obj (p, Centre_Tensor_obj (q, r)))
         (@premon_assoc C B P (`1 p) (`1 q) (`1 r))
         (@premon_assoc_central C B P (`1 p) (`1 q) (`1 r)))
    (fun p q g => premon_unit_left_natural_ff' (`1 g))
    (fun p q g => premon_unit_left_natural_from_ff' (`1 g))
    (fun p q g => premon_unit_right_natural_ff' (`1 g))
    (fun p q g => premon_unit_right_natural_from_ff' (`1 g))
    (fun p q r s t u g h i =>
       premon_joint_assoc_natural (`1 g) (`1 h) (`1 i))
    (fun p q r s t u g h i =>
       premon_joint_assoc_natural_from (`1 g) (`1 h) (`1 i))
    (fun p q => @premon_triangle_ff' C B P (`1 p) (`1 q))
    (fun p q r s =>
       @premon_pentagon_ff' C B P (`1 p) (`1 q) (`1 r) (`1 s)).

End PremonoidalCentre.
