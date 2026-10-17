Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Multicategory.
Require Import Category.Construction.ColouredPROP.

From Coq Require Import Lists.List.
From Coq Require Import Eqdep_dec.
Import ListNotations.

Generalizable All Variables.

(* * * The representable multicategory symmetric 幺半范畴 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/representable+multicategory

   本文件给出可表性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The tensor fold *)

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_list {C : Category} `{M : @Monoidal C} (xs : list C) : C :=
  fold_right (fun a acc => (a ⨂ acc)%object) I xs.

Section RepresentableKit.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context {A : Type}.
Context (ob : A → C).

(** The tensor fold over abstract colour type, through 对象
 realization [ob]. （已译） *)
Definition tfold : list A → C :=
  fold_right (fun a acc => (ob a ⨂ acc)%object) I.

(* * ** The concatenation 同构, both directions （已译） *)

Fixpoint tfold_app_to (Γ Δ : list A) :
  tfold (Γ ++ Δ) ~{C}~> (tfold Γ ⨂ tfold Δ)%object :=
  match Γ with
  | [] => unit_left⁻¹
  | a :: Γ' => tensor_assoc⁻¹ ∘ (id[ob a] ⨂ tfold_app_to Γ' Δ)
  end.

Fixpoint tfold_app_from (Γ Δ : list A) :
  (tfold Γ ⨂ tfold Δ)%object ~{C}~> tfold (Γ ++ Δ) :=
  match Γ with
  | [] => unit_left
  | a :: Γ' => (id[ob a] ⨂ tfold_app_from Γ' Δ) ∘ tensor_assoc
  end.

Lemma tfold_app_from_to (Γ Δ : list A) :
  tfold_app_from Γ Δ ∘ tfold_app_to Γ Δ ≈ id.
Proof.
  induction Γ as [| a Γ IH]; simpl.
  - apply iso_to_from.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc tensor_assoc).
    rewrite iso_to_from, id_left.
    rewrite <- bimap_comp.
    rewrite id_left, IH.
    apply bimap_id_id.
Qed.

Lemma tfold_app_to_from (Γ Δ : list A) :
  tfold_app_to Γ Δ ∘ tfold_app_from Γ Δ ≈ id.
Proof.
  induction Γ as [| a Γ IH]; simpl.
  - apply iso_from_to.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc (id[ob a] ⨂ tfold_app_to Γ Δ)).
    rewrite <- bimap_comp.
    rewrite id_left, IH.
    rewrite bimap_id_id, id_left.
    apply iso_from_to.
Qed.

(** The two directions packaged as an isomorphism. *)
Program Definition tfold_app (Γ Δ : list A) :
  tfold (Γ ++ Δ) ≅ (tfold Γ ⨂ tfold Δ)%object := {|
  to := tfold_app_to Γ Δ;
  from := tfold_app_from Γ Δ
|}.
Next Obligation. apply tfold_app_to_from. Qed.
Next Obligation. apply tfold_app_from_to. Qed.

(*
   本节说明多元范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition tcast {Γ Δ : list A} (e : Γ = Δ) : tfold Γ ~{C}~> tfold Δ :=
  match e with eq_refl => id end.

Lemma tcast_trans {Γ Δ Λ : list A} (e : Γ = Δ) (e' : Δ = Λ) :
  tcast e' ∘ tcast e ≈ tcast (eq_trans e e').
Proof. destruct e, e'; simpl; apply id_left. Qed.

Lemma tcast_cons (x : A) {Γ Δ : list A} (e : Γ = Δ) :
  tcast (f_equal (cons x) e) ≈ id[ob x] ⨂ tcast e.
Proof. destruct e; simpl; symmetry; apply bimap_id_id. Qed.

Context (luip : ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q).

Lemma tcast_irr {Γ Δ : list A} (p q : Γ = Δ) : tcast p ≈ tcast q.
Proof using luip. rewrite (luip _ _ p q); reflexivity. Qed.

Lemma tcast_loop {Γ : list A} (e : Γ = Γ) : tcast e ≈ id.
Proof using luip. rewrite (luip _ _ e eq_refl); reflexivity. Qed.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint msplice (Γ1 : list A) {Γ2 Δ : list A} {b : A}
  (g : tfold Δ ~{C}~> ob b) :
  tfold (Γ1 ++ Δ ++ Γ2) ~{C}~> tfold (Γ1 ++ b :: Γ2) :=
  match Γ1 with
  | [] => (g ⨂ id[tfold Γ2]) ∘ tfold_app_to Δ Γ2
  | a :: Γ1' => id[ob a] ⨂ msplice Γ1' g
  end.

(*
   本节说明多元范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Folding empty suffix away: right unitor against the
 concatenation map cast along [Δ ++ [] = Δ], any 证明 of
 boundary equation. （已译） *)
Lemma tfold_nil_r (Δ : list A) (e : Δ ++ [] = Δ) :
  unit_right ∘ tfold_app_to Δ [] ≈ tcast e.
Proof using luip.
  induction Δ as [| a Δ IH]; simpl.
  - rewrite tcast_loop.
    rewrite <- unit_identity.
    apply iso_to_from.
  - rewrite (luip _ _ e (f_equal (cons a) (app_nil_r Δ))).
    rewrite tcast_cons.
    rewrite comp_assoc.
    rewrite <- triangle_identity_right.
    rewrite <- bimap_comp.
    rewrite id_left.
    now rewrite (IH (app_nil_r Δ)).
Qed.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma msplice_mid (Γ1 : list A) {Γ2 : list A} (b : A) :
  msplice Γ1 (Γ2:=Γ2) (Δ:=[b]) (b:=b) (to (@unit_right C _ (ob b))) ≈ id.
Proof.
  induction Γ1 as [| a Γ1 IH]; simpl.
  - rewrite comp_assoc.
    rewrite <- inverse_triangle_identity.
    rewrite <- bimap_comp.
    rewrite id_left, iso_to_from.
    apply bimap_id_id.
  - rewrite IH.
    apply bimap_id_id.
Qed.

(*
   本节说明多元范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma tfold_app_assoc (x y z : list A) (e : x ++ y ++ z = (x ++ y) ++ z) :
  (tfold_app_to x y ⨂ id[tfold z]) ∘ tfold_app_to (x ++ y) z ∘ tcast e
    ≈ tensor_assoc⁻¹ ∘ (id[tfold x] ⨂ tfold_app_to y z)
        ∘ tfold_app_to x (y ++ z).
Proof using luip.
  revert e; induction x as [| a x IH]; intros e; simpl.
  - (* 相关说明。 （已译） *)
    rewrite tcast_loop, id_right.
    rewrite <- comp_assoc.
    rewrite from_unit_left_natural.
    rewrite comp_assoc.
    rewrite <- triangle_inverse_left.
    rewrite comp_assoc.
    rewrite iso_from_to, id_left.
    reflexivity.
  - (* Cons step: slide head 对象 out every factor apply
 inverse pentagon 恒等. （已译） *)
    rewrite (luip _ _ e (f_equal (cons a) (app_assoc x y z))).
    rewrite tcast_cons.
    rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    rewrite from_assoc_nat_cons.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    rewrite (IH (app_assoc x y z)).
    rewrite from_assoc_nat_id2_cons.
    rewrite <- 2!bimap_id_fuse.
    rewrite !comp_assoc.
    now rewrite inverse_pentagon_identity.
Qed.

(** [tfold_app_assoc], re-bracketed for right-nested rewriting. *)
Lemma tfold_app_assoc_cons (x y z : list A)
  (e : x ++ y ++ z = (x ++ y) ++ z) :
  (tfold_app_to x y ⨂ id[tfold z]) ∘ (tfold_app_to (x ++ y) z ∘ tcast e)
    ≈ tensor_assoc⁻¹
        ∘ ((id[tfold x] ⨂ tfold_app_to y z) ∘ tfold_app_to x (y ++ z)).
Proof using luip.
  rewrite !comp_assoc.
  apply tfold_app_assoc.
Qed.

(** Peeling shared head colour off boundary cast, ARBITRARY
 证明 between cons-shaped endpoints: tail equation recovered
 transparently [f_equal tl]. （已译） *)
Lemma tcast_cons_any (x : A) {Γ Δ : list A} (e : x :: Γ = x :: Δ) :
  tcast e ≈ id[ob x] ⨂ tcast (f_equal (@tl A) e).
Proof using luip.
  transitivity (tcast (f_equal (cons x) (f_equal (@tl A) e))).
  - apply tcast_irr.
  - apply tcast_cons.
Qed.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Nested shape: folding [Γ2] off context whose remaining prefix
 contains slot. The spliced 论元 [h] rides inside left
 tensor factor. （已译） *)
Lemma msplice_fold {Δ1 Δ2 Γ2 Θ : list A} {a : A}
  (h : tfold Θ ~{C}~> ob a)
  (u : Δ1 ++ a :: Δ2 ++ Γ2 = (Δ1 ++ a :: Δ2) ++ Γ2)
  (v : Δ1 ++ Θ ++ Δ2 ++ Γ2 = (Δ1 ++ Θ ++ Δ2) ++ Γ2) :
  tfold_app_to (Δ1 ++ a :: Δ2) Γ2 ∘ tcast u ∘ msplice Δ1 (Γ2:=Δ2 ++ Γ2) h
    ≈ (msplice Δ1 (Γ2:=Δ2) h ⨂ id[tfold Γ2])
        ∘ tfold_app_to (Δ1 ++ Θ ++ Δ2) Γ2 ∘ tcast v.
Proof using luip.
  revert u v; induction Δ1 as [| d Δ1 IH]; intros u v; simpl.
  - (* 相关说明。 （已译） *)
    rewrite tcast_loop, id_right.
    rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    rewrite (tfold_app_assoc_cons Θ Δ2 Γ2 v).
    rewrite from_assoc_nat_cons.
    rewrite bimap_id_id.
    rewrite bimap_fuse_cons.
    rewrite id_left, id_right.
    reflexivity.
  - (* Cons step: every factor [id ⨂ -]; fuse, apply induction
 假设, unfuse. （已译） *)
    rewrite (tcast_cons_any d u), (tcast_cons_any d v).
    rewrite <- !comp_assoc.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    rewrite (IH (f_equal (@tl A) u) (f_equal (@tl A) v)).
    rewrite from_assoc_nat_cons.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    reflexivity.
Qed.

(** Disjoint shape: folding prefix [Δ] off context whose slot lies
 beyond it. The spliced 论元 [h] rides inside right tensor
 factor. （已译） *)
Lemma mfold_msplice {Δ Γ2 Γ3 Θ : list A} {b : A}
  (h : tfold Θ ~{C}~> ob b)
  (u : (Δ ++ Γ2) ++ b :: Γ3 = Δ ++ Γ2 ++ b :: Γ3)
  (v : (Δ ++ Γ2) ++ Θ ++ Γ3 = Δ ++ Γ2 ++ Θ ++ Γ3) :
  tfold_app_to Δ (Γ2 ++ b :: Γ3) ∘ tcast u ∘ msplice (Δ ++ Γ2) (Γ2:=Γ3) h
    ≈ (id[tfold Δ] ⨂ msplice Γ2 (Γ2:=Γ3) h)
        ∘ tfold_app_to Δ (Γ2 ++ Θ ++ Γ3) ∘ tcast v.
Proof using luip.
  revert u v; induction Δ as [| d Δ IH]; intros u v; simpl.
  - rewrite !tcast_loop, !id_right.
    now rewrite from_unit_left_natural.
  - rewrite (tcast_cons_any d u), (tcast_cons_any d v).
    rewrite <- !comp_assoc.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    rewrite (IH (f_equal (@tl A) u) (f_equal (@tl A) v)).
    rewrite from_assoc_nat_id2_cons.
    rewrite bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    reflexivity.
Qed.

(** Splicing respects setoid 论元. （已译） *)
Lemma msplice_respects (Γ1 : list A) {Γ2 Δ : list A} {b : A}
  (g g' : tfold Δ ~{C}~> ob b) :
  g ≈ g' → msplice Γ1 (Γ2:=Γ2) g ≈ msplice Γ1 (Γ2:=Γ2) g'.
Proof.
  intros Hg.
  induction Γ1 as [| a Γ1 IH]; simpl.
  - now rewrite Hg.
  - now rewrite IH.
Qed.

(*
   本节说明多元范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：Nested shape: second slot lies INSIDE context spliced by
 first. （已译） *)
Lemma msplice_nested {Γ1 Γ2 Δ1 Δ2 Θ : list A} {a b : A}
  (g : tfold (Δ1 ++ a :: Δ2) ~{C}~> ob b) (h : tfold Θ ~{C}~> ob a)
  (u : (Γ1 ++ Δ1) ++ a :: Δ2 ++ Γ2 = Γ1 ++ (Δ1 ++ a :: Δ2) ++ Γ2)
  (v : (Γ1 ++ Δ1) ++ Θ ++ Δ2 ++ Γ2 = Γ1 ++ (Δ1 ++ Θ ++ Δ2) ++ Γ2) :
  msplice Γ1 (Γ2:=Γ2) g ∘ tcast u ∘ msplice (Γ1 ++ Δ1) (Γ2:=Δ2 ++ Γ2) h
    ≈ msplice Γ1 (Γ2:=Γ2) (g ∘ msplice Δ1 (Γ2:=Δ2) h) ∘ tcast v.
Proof using luip.
  revert u v; induction Γ1 as [| a' Γ1 IH]; intros u v; simpl.
  - rewrite bimap_comp_id_right.
    rewrite <- !comp_assoc.
    comp_left.
    rewrite !comp_assoc.
    apply msplice_fold.
  - rewrite (tcast_cons_any a' u), (tcast_cons_any a' v).
    rewrite <- !comp_assoc.
    rewrite bimap_id_fuse_cons.
    rewrite !bimap_id_fuse.
    now rewrite IH.
Qed.

(** [mfold_msplice], re-bracketed for right-nested rewriting. *)
Lemma mfold_msplice_cons {Δ Γ2 Γ3 Θ : list A} {b : A}
  (h : tfold Θ ~{C}~> ob b)
  (u : (Δ ++ Γ2) ++ b :: Γ3 = Δ ++ Γ2 ++ b :: Γ3)
  (v : (Δ ++ Γ2) ++ Θ ++ Γ3 = Δ ++ Γ2 ++ Θ ++ Γ3) :
  tfold_app_to Δ (Γ2 ++ b :: Γ3)
      ∘ (tcast u ∘ msplice (Δ ++ Γ2) (Γ2:=Γ3) h)
    ≈ (id[tfold Δ] ⨂ msplice Γ2 (Γ2:=Γ3) h)
        ∘ (tfold_app_to Δ (Γ2 ++ Θ ++ Γ3) ∘ tcast v).
Proof using luip.
  rewrite !comp_assoc.
  apply mfold_msplice.
Qed.

(** 本节：Disjoint shape: two slots lie same outer context, the
 [a]-slot before [b]-slot. （已译） *)
Lemma msplice_disjoint {Γ1 Γ2 Γ3 Δ Θ : list A} {a b : A}
  (g : tfold Δ ~{C}~> ob a) (h : tfold Θ ~{C}~> ob b)
  (u : (Γ1 ++ Δ ++ Γ2) ++ b :: Γ3 = Γ1 ++ Δ ++ Γ2 ++ b :: Γ3)
  (v : (Γ1 ++ a :: Γ2) ++ b :: Γ3 = Γ1 ++ a :: Γ2 ++ b :: Γ3)
  (w : Γ1 ++ a :: Γ2 ++ Θ ++ Γ3 = (Γ1 ++ a :: Γ2) ++ Θ ++ Γ3)
  (s : (Γ1 ++ Δ ++ Γ2) ++ Θ ++ Γ3 = Γ1 ++ Δ ++ Γ2 ++ Θ ++ Γ3) :
  msplice Γ1 (Γ2:=Γ2 ++ b :: Γ3) g ∘ tcast u
      ∘ msplice (Γ1 ++ Δ ++ Γ2) (Γ2:=Γ3) h
    ≈ tcast v ∘ msplice (Γ1 ++ a :: Γ2) (Γ2:=Γ3) h ∘ tcast w
        ∘ msplice Γ1 (Γ2:=Γ2 ++ Θ ++ Γ3) g ∘ tcast s.
Proof using luip.
  revert u v w s; induction Γ1 as [| a' Γ1 IH]; intros u v w s; simpl.
  - rewrite !tcast_loop, id_left, id_right.
    rewrite <- !comp_assoc.
    rewrite (mfold_msplice_cons (Δ:=Δ) (Γ2:=Γ2) (Γ3:=Γ3) h u s).
    rewrite !bimap_fuse_cons.
    rewrite !id_left, !id_right.
    reflexivity.
  - rewrite (tcast_cons_any a' u), (tcast_cons_any a' v),
      (tcast_cons_any a' w), (tcast_cons_any a' s).
    rewrite <- !comp_assoc.
    rewrite !bimap_id_fuse_cons.
    rewrite !bimap_id_fuse.
    now rewrite IH.
Qed.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma msplice_block (Γ1 : list A) {Γ2 Δ : list A} {b : A}
  (g : tfold Δ ~{C}~> ob b) :
  msplice Γ1 (Γ2:=Γ2) g
    ≈ tfold_app_from Γ1 (b :: Γ2)
        ∘ (id[tfold Γ1] ⨂ ((g ⨂ id[tfold Γ2]) ∘ tfold_app_to Δ Γ2))
        ∘ tfold_app_to Γ1 (Δ ++ Γ2).
Proof.
  induction Γ1 as [| a Γ1 IH]; simpl.
  - rewrite <- comp_assoc.
    rewrite from_unit_left_natural.
    rewrite comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
  - rewrite IH.
    rewrite <- !comp_assoc.
    rewrite to_assoc_nat_id2_cons.
    rewrite (comp_assoc tensor_assoc).
    rewrite iso_to_from, id_left.
    rewrite !bimap_id_fuse_cons.
    rewrite bimap_id_fuse.
    now rewrite !comp_assoc.
Qed.

End RepresentableKit.

(** The concatenation 同构 at 恒等 realization: form
 stated [tensor_list] itself. （已译） *)
Definition tensor_list_app {C : Category} `{M : @Monoidal C}
  (xs ys : list C) :
  tensor_list (xs ++ ys) ≅ (tensor_list xs ⨂ tensor_list ys)%object :=
  tfold_app (fun x => x) xs ys.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SwapFold.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** The inverse pentagon identity against a continuation. *)
Lemma inverse_pentagon_cons {x y z w t : C}
  (k : t ~> (x ⨂ (y ⨂ (z ⨂ w)))%object) :
  (tensor_assoc⁻¹ ⨂ id[w])
      ∘ (tensor_assoc⁻¹ ∘ ((id[x] ⨂ tensor_assoc⁻¹) ∘ k))
    ≈ tensor_assoc⁻¹ ∘ (tensor_assoc⁻¹ ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  apply inverse_pentagon_identity.
Qed.

Lemma swap_fold_coherence {x y L G Z : C}
  (m : (x ⨂ y)%object ~> (y ⨂ x)%object) (w : Z ~> (L ⨂ G)%object) :
  tensor_assoc⁻¹ ∘ (id[y] ⨂ (tensor_assoc⁻¹ ∘ (id[x] ⨂ w)))
      ∘ tensor_assoc ∘ (m ⨂ id[Z]) ∘ tensor_assoc⁻¹
    ≈ ((tensor_assoc ∘ (m ⨂ id[L]) ∘ tensor_assoc⁻¹) ⨂ id[G])
        ∘ (tensor_assoc⁻¹ ∘ (id[x] ⨂ (tensor_assoc⁻¹ ∘ (id[y] ⨂ w)))).
Proof.
  assert (Hsplit : m ⨂ w
    ≈ (m ⨂ id[(L ⨂ G)%object]) ∘ (id[(x ⨂ y)%object] ⨂ w))
    by (rewrite <- bimap_comp; now rewrite id_right, id_left).
  assert (Hslide : (id[(x ⨂ y)%object] ⨂ w) ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ (id[x] ⨂ (id[y] ⨂ w))).
  { pose proof (from_tensor_assoc_natural (id[x]) (id[y]) w) as X.
    rewrite bimap_id_id in X.
    exact X. }
  (* Split the compound tensor factors on both sides. *)
  rewrite <- !bimap_id_fuse.
  rewrite !bimap_comp_id_right.
  rewrite <- !comp_assoc.
  (* 相关说明。 （已译） *)
  rewrite (to_assoc_nat_cons (id[y]) (id[x]) w).
  rewrite bimap_id_id.
  rewrite bimap_fuse_cons.
  rewrite id_left, id_right.
  rewrite Hsplit.
  rewrite <- !comp_assoc.
  rewrite Hslide.
  (* 相关说明。 （已译） *)
  rewrite inverse_pentagon_cons.
  rewrite (from_assoc_nat_cons m (id[L]) (id[G])).
  rewrite bimap_id_id.
  rewrite <- pentagon_from_solved_cons.
  reflexivity.
Qed.

End SwapFold.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Realization.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).

Fixpoint perm_arrow {Γ Δ : list A} (p : tperm Γ Δ) :
  tfold ob Δ ~{C}~> tfold ob Γ :=
  match p with
  | tperm_nil => id
  | tperm_skip x q => id[ob x] ⨂ perm_arrow q
  | tperm_swap x y Γ' =>
      tensor_assoc ∘ (braid ⨂ id[tfold ob Γ']) ∘ tensor_assoc⁻¹
  | tperm_trans q r => perm_arrow q ∘ perm_arrow r
  end.

(** The canonical reflexivity permutation acts trivially. *)
Lemma perm_arrow_refl (Γ : list A) :
  perm_arrow (tperm_refl Γ) ≈ id.
Proof.
  induction Γ as [| x Γ IH]; simpl.
  - reflexivity.
  - rewrite IH; apply bimap_id_id.
Qed.

(** The skip constructor realizes 恒等 tensor factor
 (definitional; named rewriting). （已译） *)
Lemma perm_arrow_skip (x : A) {Γ Δ : list A} (q : tperm Γ Δ) :
  perm_arrow (tperm_skip x q) ≈ id[ob x] ⨂ perm_arrow q.
Proof. reflexivity. Qed.

(** 本节：Right padding fold coordinates: realization of
 [tperm_app_l p Λ] [perm_arrow p] left tensor factor. （已译） *)
Lemma perm_arrow_app_l {Γ Δ : list A} (p : tperm Γ Δ) (Λ : list A) :
  tfold_app_to ob Γ Λ ∘ perm_arrow (tperm_app_l p Λ)
    ≈ (perm_arrow p ⨂ id[tfold ob Λ]) ∘ tfold_app_to ob Δ Λ.
Proof.
  induction p as [| x Γ' Δ' q IH | x y Γ' | Γ' Δ' Λ' q IH1 r IH2]; simpl.
  - rewrite perm_arrow_refl, id_right.
    now rewrite bimap_id_id, id_left.
  - rewrite <- !comp_assoc.
    rewrite bimap_id_fuse.
    rewrite IH.
    rewrite <- bimap_id_fuse.
    now rewrite from_assoc_nat_cons.
  - rewrite !comp_assoc.
    rewrite swap_fold_coherence.
    now rewrite !comp_assoc.
  - rewrite comp_assoc.
    rewrite IH1.
    rewrite <- comp_assoc.
    rewrite IH2.
    rewrite comp_assoc.
    now rewrite bimap_fuse_id_right.
Qed.

(** 本节：Left padding fold coordinates: realization of
 [tperm_app_r Γ p] [perm_arrow p] right tensor factor. （已译） *)
Lemma perm_arrow_app_r (Γ : list A) {Δ Λ : list A} (p : tperm Δ Λ) :
  tfold_app_to ob Γ Δ ∘ perm_arrow (tperm_app_r Γ p)
    ≈ (id[tfold ob Γ] ⨂ perm_arrow p) ∘ tfold_app_to ob Γ Λ.
Proof.
  induction Γ as [| x Γ IH]; simpl.
  - now rewrite from_unit_left_natural.
  - rewrite <- !comp_assoc.
    rewrite bimap_id_fuse.
    rewrite IH.
    rewrite <- bimap_id_fuse.
    now rewrite from_assoc_nat_id2_cons.
Qed.

End Realization.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Equivariance.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).

(** 本节：Cons forms padding lemmas, rewriting inside right-nested
 chains. （已译） *)
Lemma perm_arrow_app_l_cons {Γ Δ : list A} (p : tperm Γ Δ) (Λ : list A)
  {z : C} (k : z ~> tfold ob (Δ ++ Λ)) :
  tfold_app_to ob Γ Λ ∘ (perm_arrow ob (tperm_app_l p Λ) ∘ k)
    ≈ (perm_arrow ob p ⨂ id[tfold ob Λ]) ∘ (tfold_app_to ob Δ Λ ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  apply perm_arrow_app_l.
Qed.

(** Parallel 复合 across [++], fold coordinates: the
 realization [tperm_app p q] tensor two
 realizations. （已译） *)
Lemma perm_arrow_app {Γ Γ' Δ Δ' : list A} (p : tperm Γ Γ') (q : tperm Δ Δ') :
  tfold_app_to ob Γ Δ ∘ perm_arrow ob (tperm_app p q)
    ≈ (perm_arrow ob p ⨂ perm_arrow ob q) ∘ tfold_app_to ob Γ' Δ'.
Proof.
  unfold tperm_app; simpl.
  rewrite perm_arrow_app_l_cons.
  rewrite perm_arrow_app_r.
  rewrite bimap_fuse_cons.
  now rewrite id_left, id_right.
Qed.

(** [perm_arrow_app] transposed across the concatenation isomorphism,
    against a continuation. *)
Lemma perm_arrow_app_from {Γ Γ' Δ Δ' : list A}
  (p : tperm Γ Γ') (q : tperm Δ Δ')
  {z : C} (k : z ~> (tfold ob Γ' ⨂ tfold ob Δ')%object) :
  perm_arrow ob (tperm_app p q) ∘ (tfold_app_from ob Γ' Δ' ∘ k)
    ≈ tfold_app_from ob Γ Δ ∘ ((perm_arrow ob p ⨂ perm_arrow ob q) ∘ k).
Proof.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- (id_left (perm_arrow ob (tperm_app p q))).
  rewrite <- (tfold_app_from_to ob Γ Δ).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tfold_app_to ob Γ Δ)).
  rewrite perm_arrow_app.
  rewrite <- !comp_assoc.
  rewrite tfold_app_to_from.
  now rewrite id_right.
Qed.

End Equivariance.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section EquivarianceCore.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).

Lemma msplice_equivariant {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list A} {b : A}
  (p : tperm Γ1 Γ1') (q : tperm Δ Δ') (r : tperm Γ2 Γ2')
  (g : tfold ob Δ ~{C}~> ob b) :
  msplice ob Γ1 (Γ2:=Γ2) g ∘ perm_arrow ob (perm_block3 p q r)
    ≈ perm_arrow ob (perm_block_slot b p r)
        ∘ msplice ob Γ1' (Γ2:=Γ2') (g ∘ perm_arrow ob q).
Proof.
  assert (Harg :
    ((g ⨂ id[tfold ob Γ2]) ∘ tfold_app_to ob Δ Γ2)
        ∘ perm_arrow ob (tperm_app q r)
      ≈ ((g ∘ perm_arrow ob q) ⨂ perm_arrow ob r)
          ∘ tfold_app_to ob Δ' Γ2').
  { rewrite <- comp_assoc.
    rewrite perm_arrow_app.
    rewrite bimap_fuse_cons.
    now rewrite id_left. }
  unfold perm_block3, perm_block_slot.
  rewrite (msplice_block ob Γ1 g).
  rewrite (msplice_block ob Γ1' (g ∘ perm_arrow ob q)).
  rewrite <- !comp_assoc.
  (* Left side: pull block realization across fold, then fold
 论元 block [Harg]. （已译） *)
  rewrite perm_arrow_app.
  rewrite bimap_fuse_cons.
  rewrite id_left.
  rewrite Harg.
  (* 相关说明。 （已译） *)
  rewrite perm_arrow_app_from.
  rewrite bimap_fuse_cons.
  rewrite id_right.
  rewrite perm_arrow_skip.
  rewrite (bimap_fuse_cons (id[ob b]) (perm_arrow ob r)
             (g ∘ perm_arrow ob q) (id[tfold ob Γ2'])
             (tfold_app_to ob Δ' Γ2')).
  now rewrite id_left, id_right.
Qed.

End EquivarianceCore.

(* 相关说明。 （已译） *)

Section Assembly.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context {A : Type}.
Context (ob : A → C).
Context (luip : ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q).

(** The boundary cast on multimorphisms: hom-side transport along a
    list equality. *)
Definition mhcast {Γ Γ' : list A} {c : A} (e : Γ = Γ')
  (f : tfold ob Γ ~{C}~> ob c) : tfold ob Γ' ~{C}~> ob c :=
  match e in _ = Γ0 return tfold ob Γ0 ~{C}~> ob c with
  | eq_refl => f
  end.

(** 本节：The hom-side transport precomposition boundary cast. （已译） *)
Lemma mhcast_tcast {Γ Γ' : list A} {c : A} (e : Γ = Γ')
  (f : tfold ob Γ ~{C}~> ob c) :
  mhcast e f ≈ f ∘ tcast ob (eq_sym e).
Proof.
  destruct e; simpl.
  now rewrite id_right.
Qed.

#[local] Obligation Tactic := intros.

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Fold_Multicategory : Multicategory := {|
  mobj := A;
  mhom := fun Γ c => tfold ob Γ ~{C}~> ob c;
  mhomset := fun Γ c => @homset C (tfold ob Γ) (ob c);
  mcast := fun Γ Γ' c e => mhcast e;
  mid := fun a => to (@unit_right C _ (ob a));
  mcomp := fun Γ1 Γ2 Δ b c f g => f ∘ msplice ob Γ1 (Γ2:=Γ2) g;
  msym := fun Γ Δ c p f => f ∘ perm_arrow ob p
|}.
Next Obligation.
  (* mcast_respects *)
  destruct e; repeat intro; assumption.
Qed.
Next Obligation.
  (* mcast_id *)
  rewrite (luip _ _ e eq_refl); reflexivity.
Qed.
Next Obligation.
  (* mcast_trans *)
  destruct e, e'; reflexivity.
Qed.
Next Obligation.
  (* mcomp_respects *)
  repeat intro.
  apply compose_respects; [ assumption |].
  now apply msplice_respects.
Qed.
Next Obligation.
  (* mcomp_id_left *)
  rewrite mhcast_tcast; simpl.
  rewrite comp_assoc.
  rewrite <- to_unit_right_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc unit_right (tfold_app_to ob Δ [])).
  rewrite (tfold_nil_r ob luip Δ (app_nil_r Δ)).
  rewrite tcast_trans.
  rewrite (tcast_loop ob luip).
  now rewrite id_right.
Qed.
Next Obligation.
  (* mcomp_id_right *)
  rewrite mhcast_tcast.
  rewrite msplice_mid.
  rewrite (tcast_loop ob luip).
  now rewrite !id_right.
Qed.
Next Obligation.
  (* mcomp_assoc_nested *)
  cbv beta.
  rewrite !mhcast_tcast.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite !comp_assoc.
  apply (msplice_nested ob luip g h (eq_sym e1) (eq_sym e2)).
Qed.
Next Obligation.
  (* mcomp_assoc_disjoint *)
  cbv beta.
  rewrite !mhcast_tcast.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite !comp_assoc.
  apply (msplice_disjoint ob luip g h
           (eq_sym d1) (eq_sym d2) (eq_sym d3) (eq_sym d4)).
Qed.
Next Obligation.
  (* msym_respects *)
  repeat intro.
  now apply compose_respects.
Qed.
Next Obligation.
  (* msym_id *)
  cbv beta.
  rewrite perm_arrow_refl.
  now rewrite id_right.
Qed.
Next Obligation.
  (* msym_compose *)
  cbv beta; simpl.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  (* mcomp_equivariant *)
  cbv beta.
  rewrite <- !comp_assoc.
  comp_left.
  apply msplice_equivariant.
Qed.

End Assembly.

(*
   本节说明幺半结构、幺半群、多元范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RepresentableMulticategory (C : Category)
  `{S : @SymmetricMonoidal C}
  (luip : ∀ (Γ Δ : list C) (p q : Γ = Δ), p = q) : Multicategory :=
  Fold_Multicategory (fun x : C => x) luip.

(*
   本节说明幺半结构、幺半群、多元范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Uniqueness of list equality proofs from an element decider. *)
Definition list_uip_of_dec {A : Type}
  (dec : ∀ x y : A, {x = y} + {x ≠ y}) :
  ∀ (Γ Δ : list A) (p q : Γ = Δ), p = q :=
  UIP_dec (list_eq_dec dec).

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cprop_tfold {Colour : Type} (Q : ColouredPROP Colour)
  (Γ : list Colour) :
  tfold (@wire Colour Q) Γ = cprop_of_list Γ.
Proof.
  induction Γ as [| c Γ IH]; simpl.
  - rewrite <- (cprop_monoidal_coherence Q).
    apply cprop_unit_nil.
  - rewrite IH.
    rewrite <- (cprop_monoidal_coherence Q).
    apply (cprop_tensor_app [c] Γ).
Qed.

(** The multicategory coloured PROP: multimorphisms
 [mhom Γ c ≡ tfold wire Γ ~{Q}~> wire c], where [tfold wire Γ] is
 对象 [cprop_of_list Γ] [cprop_tfold]. （已译） *)
Definition ColouredPROP_Multicategory {Colour : Type}
  (Q : ColouredPROP Colour)
  (Cdec : ∀ x y : Colour, {x = y} + {x ≠ y}) : Multicategory :=
  @Fold_Multicategory (cprop_cat Q) (cprop_symmetric Q) Colour
    (@wire Colour Q) (list_uip_of_dec Cdec).
