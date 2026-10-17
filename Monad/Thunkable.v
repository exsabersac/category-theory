Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Structure.Binoidal.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Premonoidal.
Require Import Category.Monad.Kleisli.Commutative.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    nLab: https://ncatlab.org/nlab/show/strong+monad
    Reference: Führmann, "Direct models of the computational
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Thunkable.

Context {C : Category}.
Context `{SM : @SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{SMon : @StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(* * ** Tier 1: thunkability over bare strong 单子. （已译） *)
(* ------------------------------------------------------------------ *)

(*
   本节说明 Thunkable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition thunkable {x y : C} (f : x ~> M y) : Type :=
  fmap[M] ret[M] ∘ f ≈ ret[M] ∘ f.

(* Thunkability is a property of the ≈-class of a morphism. *)
Lemma thunkable_respects {x y : C} {f g : x ~> M y} :
  f ≈ g → thunkable f → thunkable g.
Proof.
  unfold thunkable.
  intros E tf.
  now rewrite <- E.
Qed.

(* The Kleisli 恒等 thunkable: both sides unit 自然性
 square [fmap_ret] instantiated at unit itself. （已译） *)
Lemma thunkable_id {x : C} : thunkable (ret[M] : x ~{C}~> M x).
Proof.
  unfold thunkable.
  symmetry.
  apply fmap_ret.
Qed.

(* Every pure 态射 thunkable: push outer unit across f with
 [fmap_ret]. （已译） *)
Lemma pure_thunkable {x y : C} (f : x ~{C}~> y) : thunkable (kpure f).
Proof.
  unfold thunkable, kpure.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  now rewrite comp_assoc.
Qed.

(*
   本节说明函子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma thunkable_comp {x y z : C} {f : y ~> M z} {g : x ~> M y} :
  thunkable f → thunkable g → thunkable (join[M] ∘ fmap[M] f ∘ g).
Proof.
  intros tf tg.
  unfold thunkable in *.
  transitivity (fmap[M] f ∘ g).
  - (* fmap ret ∘ (join ∘ fmap f ∘ g) ≈ fmap f ∘ g *)
    rewrite !comp_assoc.
    rewrite <- join_fmap_fmap.
    rewrite <- (comp_assoc join[M]).
    rewrite <- fmap_comp.
    rewrite tf.
    rewrite fmap_comp.
    rewrite comp_assoc.
    rewrite join_fmap_ret.
    now rewrite id_left.
  - (* fmap f ∘ g ≈ ret ∘ (join ∘ fmap f ∘ g) *)
    symmetry.
    rewrite !comp_assoc.
    rewrite fmap_ret.
    rewrite <- (comp_assoc (fmap[M] join[M])).
    rewrite fmap_ret.
    rewrite <- !comp_assoc.
    rewrite <- tg.
    rewrite (comp_assoc (fmap[M] (fmap[M] f))).
    rewrite <- fmap_comp.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- fmap_ret.
    rewrite comp_assoc.
    rewrite join_ret.
    now rewrite id_left.
Qed.

(* Thunkable 态射 absorb pure postcomposition: fmap u ∘ f again
 thunkable. The unit walks across u [fmap_ret], meets [tf], and
 walks back out across fmap u. （已译） *)
Lemma thunkable_fmap_post {x y z : C} (u : y ~{C}~> z) {f : x ~> M y} :
  thunkable f → thunkable (fmap[M] u ∘ f).
Proof.
  intro tf.
  unfold thunkable in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite fmap_ret.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite tf.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  now rewrite <- comp_assoc.
Qed.

(*
   本节说明单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem thunkable_central {x y : C} (f : x ~> M y) :
  thunkable f → @central Kleisli Kleisli_Binoidal x y f.
Proof.
  intros tf.
  apply kleisli_central_iff; intros c d g.
  split.
  - rewrite <- (dstr_reassoc_left f g).
    rewrite <- (dstr_reassoc_left' f g).
    now rewrite tf.
  - rewrite <- (dstr'_reassoc_right g f).
    rewrite <- (dstr'_reassoc_right' g f).
    now rewrite tf.
Qed.

(*
   本节说明幺半结构、单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)
(* * ** The wide subcategory Thunk thunkable 态射. （已译） *)
(* ------------------------------------------------------------------ *)

(*
   本节说明Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition ThunkableSub : Subcategory Kleisli := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => thunkable f;
  scomp := fun _ _ _ _ _ _ _ _ tf tg => thunkable_comp tf tg;
  sid   := fun _ _ => thunkable_id
|}.

Definition Thunk : Category := Sub Kleisli ThunkableSub.

Lemma Thunk_wide : Wide Kleisli ThunkableSub.
Proof. intro x; exact ttt. Qed.

(* The 含入 Thunk ⟶ Kl(M) generic faithful
 [Incl Kleisli ThunkableSub] Construction/Subcategory.v. （已译） *)

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)
(* ------------------------------------------------------------------ *)

Section ThunkableCD.

Context `{CD : @CopyDiscard C _}.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Hypothesis copy_nat : ∀ (x y : C) (u : x ~{C}~> y),
  copy[y] ∘ u ≈ (u ⨂ u) ∘ copy[x].

Hypothesis discard_nat : ∀ (x y : C) (u : x ~{C}~> y),
  discard[y] ∘ u ≈ discard[x].

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma thunkable_slide {a b c : C} (f : a ~> M b) (tf : thunkable f)
      (G : M b ~{C}~> M c) (g : b ~{C}~> c)
      (algG : G ∘ ret[M] ≈ ret[M] ∘ g) :
  G ∘ f ≈ fmap[M] g ∘ f.
Proof.
  assert (E : ret[M] ∘ (fmap[M] g ∘ f) ≈ ret[M] ∘ (G ∘ f)).
  { transitivity (fmap[M] G ∘ (fmap[M] ret[M] ∘ f)).
    - rewrite <- (thunkable_fmap_post g tf).
      rewrite !comp_assoc.
      rewrite <- !fmap_comp.
      rewrite algG.
      reflexivity.
    - rewrite tf.
      rewrite comp_assoc.
      rewrite <- fmap_ret.
      now rewrite <- comp_assoc. }
  rewrite <- (id_left (G ∘ f)).
  rewrite <- (@join_ret C M _ c).
  rewrite <- comp_assoc.
  rewrite <- E.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(*
   本节说明Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition copyable {x y : C} (f : x ~> M y) : Type :=
  dstr ∘ (f ⨂ f) ∘ copy[x] ≈ fmap[M] copy[y] ∘ f.

Definition discardable {x y : C} (f : x ~> M y) : Type :=
  fmap[M] discard[y] ∘ f ≈ ret[M] ∘ discard[x].

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem thunkable_copyable {x y : C} (f : x ~> M y) :
  thunkable f → copyable f.
Proof using C CD M SM SMon copy_nat.
  intro tf.
  unfold copyable.
  rewrite <- comp_assoc.
  rewrite <- (copy_nat x (M y) f).
  rewrite comp_assoc.
  apply (thunkable_slide f tf (dstr ∘ copy[M y]) copy[y]).
  rewrite <- comp_assoc.
  rewrite (copy_nat y (M y) ret[M]).
  rewrite comp_assoc.
  rewrite dstr_ret_ret.
  reflexivity.
Qed.

(*
   本节说明 Thunkable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem thunkable_discardable {x y : C} (f : x ~> M y) :
  thunkable f → discardable f.
Proof using C CD M SM SMon discard_nat.
  intro tf.
  unfold discardable.
  assert (algG : (ret[M] ∘ discard[M y]) ∘ ret[M] ≈ ret[M] ∘ discard[y]).
  { rewrite <- comp_assoc.
    now rewrite (discard_nat y (M y) ret[M]). }
  rewrite <- (thunkable_slide f tf (ret[M] ∘ discard[M y]) discard[y] algG).
  rewrite <- comp_assoc.
  now rewrite (discard_nat x (M y) f).
Qed.

(* Pure 态射 copyable discardable, through
 [pure_thunkable]. （已译） *)
Corollary pure_copyable {x y : C} (f : x ~{C}~> y) : copyable (kpure f).
Proof using C CD M SM SMon copy_nat.
  apply thunkable_copyable, pure_thunkable.
Qed.

Corollary pure_discardable {x y : C} (f : x ~{C}~> y) :
  discardable (kpure f).
Proof using C CD M SM SMon discard_nat.
  apply thunkable_discardable, pure_thunkable.
Qed.

(* ------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)
(* ------------------------------------------------------------------ *)

Section ThunkableDeterministic.

(*
   本节说明单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Hypothesis comm : commutative_sm (M:=M).

(* 相关说明。 （已译） *)
Lemma kl_copyable_eq {x y : C} (f : x ~{Kleisli}~> y) :
  (@compose Kleisli _ _ _ (kpure copy[y]) f
     ≈ @compose Kleisli _ _ _
         (f ⨂[Kleisli_Monoidal comm] f) (kpure copy[x]))
  ↔ copyable f.
Proof.
  split; intro E.
  - unfold copyable.
    rewrite kl_pure_post in E.
    rewrite kl_pure_pre in E.
    rewrite (kleisli_bimap_dstr comm f f) in E.
    symmetry; exact E.
  - rewrite kl_pure_post.
    rewrite kl_pure_pre.
    rewrite (kleisli_bimap_dstr comm f f).
    symmetry; exact E.
Qed.

(* 相关说明。 （已译） *)
Lemma kl_discardable_eq {x y : C} (f : x ~{Kleisli}~> y) :
  (@compose Kleisli _ _ _ (kpure discard[y]) f ≈ kpure discard[x])
  ↔ discardable f.
Proof.
  split; intro E.
  - unfold discardable.
    rewrite kl_pure_post in E.
    exact E.
  - rewrite kl_pure_post.
    exact E.
Qed.

(*
   本节说明Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem thunkable_deterministic {x y : C} (f : x ~{Kleisli}~> y) :
  thunkable f →
  @deterministic Kleisli (Kleisli_Symmetric comm)
    (Kleisli_CopyDiscard comm (CD:=CD)) x y f.
Proof using C CD M SM SMon comm copy_nat discard_nat.
  intro tf.
  split.
  - exact (snd (kl_copyable_eq f) (thunkable_copyable f tf)).
  - exact (snd (kl_discardable_eq f) (thunkable_discardable f tf)).
Qed.

(* The two squares pure image, standalone transfers: pure
 函子 carries base squares Kl(M) through [kl_pure_comp] and
 [kl_pure_tensor]. （已译） *)
Lemma pure_hom_delta {x y : C} (f : x ~{C}~> y)
      (Fd : copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]) :
  @compose Kleisli _ _ _ (kpure copy[y]) (kpure f)
    ≈ @compose Kleisli _ _ _
        ((kpure f) ⨂[Kleisli_Monoidal comm] (kpure f)) (kpure copy[x]).
Proof.
  rewrite (kl_pure_tensor comm f f).
  rewrite !kl_pure_comp.
  apply kl_pure_eqv.
  exact Fd.
Qed.

Lemma pure_hom_epsilon {x y : C} (f : x ~{C}~> y)
      (Fe : discard[y] ∘ f ≈ discard[x]) :
  @compose Kleisli _ _ _ (kpure discard[y]) (kpure f) ≈ kpure discard[x].
Proof.
  rewrite kl_pure_comp.
  apply kl_pure_eqv.
  exact Fe.
Qed.

(* Determinism transports along the pure functor: a base-deterministic
   morphism has a deterministic pure image in Kl(M). *)
Theorem pure_deterministic {x y : C} (f : x ~{C}~> y) :
  @deterministic C SM CD x y f →
  @deterministic Kleisli (Kleisli_Symmetric comm)
    (Kleisli_CopyDiscard comm (CD:=CD)) x y (kpure f).
Proof.
  intros [Fd Fe].
  split.
  - exact (pure_hom_delta f Fd).
  - exact (pure_hom_epsilon f Fe).
Qed.

End ThunkableDeterministic.

End ThunkableCD.

End Thunkable.
