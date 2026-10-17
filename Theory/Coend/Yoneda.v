Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coend.
Require Import Category.Instance.Sets.End.

Generalizable All Variables.

(** Element-level readings 函子 laws [Sets]-valued 函子,
 pinning 函子 so [apply] discharges applied goals directly. （已译） *)
Local Lemma fmap_id_app {D : Category} (G : D ⟶ Sets) {x : D} (z : G x) :
  fmap[G] (@id D x) z ≈ z.
Proof. exact (@fmap_id D Sets G x z). Qed.

Local Lemma fmap_comp_app {D : Category} (G : D ⟶ Sets) {x y z : D}
  (g : y ~{D}~> z) (f : x ~{D}~> y) (w : G x) :
  fmap[G] (g ∘ f) w ≈ fmap[G] g (fmap[G] f w).
Proof. exact (@fmap_comp D Sets G x y z g f w). Qed.

(* * * The ninja-Yoneda 引理 [Sets], both variances （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/co-Yoneda+lemma
   nLab: https://ncatlab.org/nlab/show/end#yoneda_reduction

   本文件给出 Yoneda 相关结果。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Yoneda.

Context {C : Category}.
Context (F : C ⟶ Sets).
Context (c : C).

(* 相关说明。 （已译） *)

(** The integrand [YoI (x, y) = C(x, c) × F y]: contravariant in [x] via
    hom-precomposition, covariant in [y] via [fmap[F]]. *)
Program Definition YoI : C^op ∏ C ⟶ Sets := {|
  fobj := fun p =>
    {| carrier   := (fst p ~{C}~> c) * F (snd p)
     ; is_setoid := @prod_setoid _ _ (@homset C (fst p) c) (is_setoid (F (snd p))) |};
  fmap := fun p q u =>
    {| morphism := fun ga => (fst ga ∘ fst u, fmap[F] (snd u) (snd ga)) |}
|}.
Next Obligation.
  unfold Proper, respectful; intros [g a] [g' a'] [Hg Ha]; split; simpl.
  - now rewrite Hg.
  - now rewrite Ha.
Qed.
Next Obligation.
  unfold Proper, respectful; intros u u' [Hu1 Hu2] [g a]; split; simpl.
  - now rewrite Hu1.
  - exact (@fmap_respects _ _ F _ _ (snd u) (snd u') Hu2 a).
Qed.
Next Obligation.
  split.
  - apply id_right.
  - apply fmap_id_app.
Qed.
Next Obligation.
  split.
  - apply comp_assoc.
  - apply fmap_comp_app.
Qed.

(** The coend leg at [x]: [(g, a) ↦ fmap[F] g a]. *)
Program Definition coy_leg (x : C) : SetoidMorphism (YoI (x, x)) (F c) := {|
  morphism := fun ga => fmap[F] (fst ga) (snd ga)
|}.
Next Obligation.
  unfold Proper, respectful; intros [g a] [g' a'] [Hg Ha]; simpl.
  transitivity (fmap[F] g a').
  - exact (proper_morphism (fmap[F] g) a a' Ha).
  - exact (@fmap_respects _ _ F _ _ g g' Hg a').
Qed.

(** Co-dinaturality legs: cowedge condition, holding by
 [fmap_comp] plus [fmap_id] 恒等 laws. （已译） *)
Lemma coy_cowedge : Cowedge_cond YoI (F c) coy_leg.
Proof.
  intros x y f [g a]; simpl.
  transitivity (fmap[F] (g ∘ f) a).
  - apply proper_morphism.
    apply fmap_id_app.
  - transitivity (fmap[F] g (fmap[F] f a)).
    + apply fmap_comp_app.
    + symmetry.
      exact (@fmap_respects _ _ F _ _ (g ∘ id) g (id_right g) (fmap[F] f a)).
Qed.

(** Forward map: the coend mediator. *)
Definition coy_to : SetoidMorphism (coend_apex_setoid YoI) (F c) :=
  coend_mediator YoI coy_leg coy_cowedge.

(** Inverse map: [b ↦ ci c (id, b)]. *)
Program Definition coy_from : SetoidMorphism (F c) (coend_apex_setoid YoI) := {|
  morphism := fun b => ci YoI c (id, b)
|}.
Next Obligation.
  proper.
  apply ce_point; split; simpl.
  - reflexivity.
  - assumption.
Qed.

(** The co-Yoneda 同构 coend apex. （已译） *)
Program Definition coyoneda_iso :
  @Isomorphism Sets (coend_apex_setoid YoI) (F c) := {|
  to   := coy_to;
  from := coy_from
|}.
Next Obligation.
  apply fmap_id_app.
Qed.
Next Obligation.
  destruct x as [x0 [g a]].
  (* coend glue: ci c (id, fmap[F] g a) ≈ ci x0 (g, a), oriented via ce_sym *)
  apply ce_sym.
  apply (ce_trans YoI (ci YoI x0 (g, a))
                      (ci YoI x0 (id ∘ g, fmap[F] id a))
                      (ci YoI c (id, fmap[F] g a))).
  - apply ce_point; split.
    + now rewrite id_left.
    + symmetry; apply fmap_id_app.
  - apply (ce_trans YoI (ci YoI x0 (id ∘ g, fmap[F] id a))
                        (ci YoI c (id ∘ id, fmap[F] g a))
                        (ci YoI c (id, fmap[F] g a))).
    + exact (ce_glue YoI x0 c g (id, a)).
    + apply ce_point; split.
      * now rewrite id_right.
      * reflexivity.
Qed.

(** 本节：The primary Form-1 deliverable, stated over packaged coend. （已译） *)
Definition coyoneda_reduction : coend_obj (SetsCoend YoI) ≅[Sets] F c :=
  coyoneda_iso.

(** ** Form 2: Yoneda via the end *)

(** [C(c, x)] as a [SetoidObject], the exponent's domain. *)
Let homc (x : C) : SetoidObject :=
  {| carrier := c ~{C}~> x; is_setoid := @homset C c x |}.

(** 本节：The integrand [YoE (x, y) = [C(c, x), F y]]: contravariant [x] by
 hom-precomposition exponent's domain, covariant [y] via
 [fmap[F]]. （已译） *)
Program Definition YoE : C^op ∏ C ⟶ Sets := {|
  fobj := fun p =>
    {| carrier   := SetoidMorphism (homc (fst p)) (F (snd p))
     ; is_setoid := @SetoidMorphism_Setoid (homc (fst p)) (F (snd p)) |};
  fmap := fun p q u =>
    {| morphism := fun phi =>
         {| morphism := fun k =>
              fmap[F] (snd u) (phi ((fst u : fst q ~{C}~> fst p) ∘ k)) |} |}
|}.
Next Obligation.
  unfold Proper, respectful; intros k k' Hk.
  apply proper_morphism; apply proper_morphism; now rewrite Hk.
Qed.
Next Obligation.
  unfold Proper, respectful; intros phi phi' Hphi k; simpl.
  apply proper_morphism; apply Hphi.
Qed.
Next Obligation.
  unfold Proper, respectful; intros [u1 u2] [u1' u2'] [Hu1 Hu2] phi k; simpl.
  transitivity (fmap[F] u2 (phi (u1' ∘ k))).
  - apply proper_morphism; apply proper_morphism; now rewrite Hu1.
  - exact (@fmap_respects _ _ F _ _ u2 u2' Hu2 (phi (u1' ∘ k))).
Qed.
Next Obligation.
  transitivity (fmap[F] id (x0 x1)).
  - apply proper_morphism; apply proper_morphism; now rewrite id_left.
  - apply fmap_id_app.
Qed.
Next Obligation.
  transitivity (fmap[F] h2 (fmap[F] h0 (x0 (h ∘ h1 ∘ x1)))).
  - apply fmap_comp_app.
  - apply proper_morphism; apply proper_morphism; apply proper_morphism.
    now rewrite comp_assoc.
Qed.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(** Forward map: evaluate family at [c] 恒等, [s ↦ (s c) id]. （已译） *)
Program Definition ye_to : SetoidMorphism (Sets_End_obj YoE) (F c) := {|
  morphism := fun s => `1 s c id
|}.
Next Obligation.
  unfold Proper, respectful; intros s t Hst.
  exact (Hst c id).
Qed.

(** 本节：The component at [x] inverse's natural family: [k ↦ fmap[F] k b],
 image [b : F c] under Yoneda embedding [C(c,-) ⟹ F]. （已译） *)
Program Definition ye_from_fam (b : F c) (x : C) :
  SetoidMorphism (homc x) (F x) := {|
  morphism := fun k => fmap[F] k b
|}.
Next Obligation.
  unfold Proper, respectful; intros b x k k' Hk.
  exact (@fmap_respects _ _ F _ _ k k' Hk b).
Qed.

(** The inverse's image assembled compatible family; wedge law is
 自然性 [k ↦ fmap[F] k b], holding [fmap_comp] [fmap_id]. （已译） *)
Program Definition ye_from_family (b : F c) : end_family YoE :=
  (fun x => ye_from_fam b x; _).
Next Obligation.
  intros b x y f k.
  change (fmap[F] f (fmap[F] (id ∘ k) b) ≈ fmap[F] id (fmap[F] (f ∘ k) b)).
  transitivity (fmap[F] (f ∘ k) b).
  - transitivity (fmap[F] f (fmap[F] k b)).
    + apply proper_morphism.
      exact (@fmap_respects _ _ F _ _ (id ∘ k) k (id_left k) b).
    + symmetry; exact (fmap_comp_app F f k b).
  - symmetry; exact (fmap_id_app F (fmap[F] (f ∘ k) b)).
Qed.

(** Inverse map: [b ↦ (fun x k => fmap[F] k b)]. *)
Program Definition ye_from : SetoidMorphism (F c) (Sets_End_obj YoE) := {|
  morphism := ye_from_family
|}.
Next Obligation.
  unfold Proper, respectful; intros b b' Hbb' x k.
  exact (proper_morphism (fmap[F] k) b b' Hbb').
Qed.

(** The Yoneda 同构 end apex. （已译） *)
Program Definition yoneda_iso :
  @Isomorphism Sets (Sets_End_obj YoE) (F c) := {|
  to   := ye_to;
  from := ye_from
|}.
Next Obligation.
  intro b.
  change (fmap[F] id b ≈ b).
  apply fmap_id_app.
Qed.
Next Obligation.
  intros s x k.
  change (fmap[F] k (`1 s c id) ≈ `1 s x k).
  transitivity (fmap[F] k (`1 s c (id ∘ id))).
  - apply proper_morphism; apply proper_morphism; now rewrite id_left.
  - transitivity (fmap[F] id (`1 s x (k ∘ id))).
    + exact (`2 s c x k id).
    + transitivity (fmap[F] id (`1 s x k)).
      * apply proper_morphism; apply proper_morphism; now rewrite id_right.
      * apply fmap_id_app.
Qed.

(** The primary Form-2 deliverable, stated over concrete end 对象;
 [Sets_End YoE : End YoE] carries setoid apex. （已译） *)
Definition yoneda_reduction : Sets_End_obj YoE ≅[Sets] F c :=
  yoneda_iso.

End Yoneda.
