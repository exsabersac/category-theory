Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Construction.Funny.Hom.
Require Import Category.Instance.Cat.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(*
   本文件给出闭结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Currying

    [FunnyCurry F a] is [F ∘ (a, −)], i.e. [F ◯ FunnyR a]; its action on
    [f : a ~> a'] is the family of images of the generating steps
    [lstep f], one component per [b : B].  Everything is definitional on
    objects: [FunnyCurry F a b ≡ F (a, b)]. *)

Program Definition FunnyCurry {A B E : Category} (F : (A □ B) ⟶ E) :
  A ⟶ ⟦B, E⟧ := {|
  fobj := fun a => F ◯ FunnyR a;
  fmap := fun a a' f => fun b => @fmap (A □ B) E F (a, b) (a', b) (lstep f)
|}.
Next Obligation.
  proper.
  apply fmap_respects.
  apply feq_consL; [ assumption | apply feq_refl ].
Qed.
Next Obligation.
  etransitivity.
  - apply fmap_respects.
    exact (feq_idL fnil).
  - exact (@fmap_id (A □ B) E F (x, b)).
Qed.
Next Obligation.
  etransitivity.
  - apply fmap_respects.
    apply feq_sym, feq_fuseL.
  - exact (@fmap_comp (A □ B) E F (x, b) (y, b) (z, b) (lstep f) (lstep g)).
Qed.

Example FunnyCurry_obj {A B E : Category} (F : (A □ B) ⟶ E) (a : A) (b : B) :
  FunnyCurry F a b = F (a, b) := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition FunnyUncurry_sep {A B E : Category} (G : A ⟶ ⟦B, E⟧) :
  SepFunctorial (fun (a : A) (b : B) => G a b) := {|
  sf_lmap := fun a a' f b => fmap[G] f b;
  sf_rmap := fun a b b' g => fmap[G a] g
|}.
Next Obligation.
  proper.
  exact (@fmap_respects A (⟦B, E⟧) G c c' x y X d).
Qed.
(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation. exact (@fmap_id A (⟦B, E⟧) G c d). Qed.
Next Obligation. exact (@fmap_comp A (⟦B, E⟧) G c c' c'' f' f d). Qed.
Next Obligation. exact (@fmap_comp B E (G c) d d' d'' g' g). Qed.

Definition FunnyUncurry {A B E : Category} (G : A ⟶ ⟦B, E⟧) :
  (A □ B) ⟶ E := FunnyUP (FunnyUncurry_sep G).

Example FunnyUncurry_obj {A B E : Category} (G : A ⟶ ⟦B, E⟧)
  (a : A) (b : B) :
  FunnyUncurry G (a, b) = G a b := eq_refl.

Lemma FunnyUncurry_lstep {A B E : Category} (G : A ⟶ ⟦B, E⟧)
  {a a' : A} (f : a ~{A}~> a') (b : B) :
  @fmap (A □ B) E (FunnyUncurry G) (a, b) (a', b) (lstep f) ≈ fmap[G] f b.
Proof. exact (FunnyUP_lstep (FunnyUncurry_sep G) f). Qed.

Lemma FunnyUncurry_rstep {A B E : Category} (G : A ⟶ ⟦B, E⟧)
  (a : A) {b b' : B} (g : b ~{B}~> b') :
  @fmap (A □ B) E (FunnyUncurry G) (a, b) (a, b') (rstep g) ≈ fmap[G a] g.
Proof. exact (FunnyUP_rstep (FunnyUncurry_sep G) g). Qed.

(** ** Evaluation *)

Definition FunnyEval {B E : Category} : ((⟦B, E⟧) □ B) ⟶ E :=
  FunnyUncurry Id[⟦B, E⟧].

Example FunnyEval_obj {B E : Category} (P : B ⟶ E) (b : B) :
  FunnyEval (P, b) = P b := eq_refl.

Lemma FunnyEval_lstep {B E : Category} {P Q : B ⟶ E}
  (τ : P ~{⟦B, E⟧}~> Q) (b : B) :
  @fmap ((⟦B, E⟧) □ B) E FunnyEval (P, b) (Q, b) (lstep τ) ≈ τ b.
Proof. exact (FunnyUP_lstep (FunnyUncurry_sep Id[⟦B, E⟧]) τ). Qed.

Lemma FunnyEval_rstep {B E : Category} (P : B ⟶ E) {b b' : B}
  (g : b ~{B}~> b') :
  @fmap ((⟦B, E⟧) □ B) E FunnyEval (P, b) (P, b') (rstep g) ≈ fmap[P] g.
Proof. exact (FunnyUP_rstep (FunnyUncurry_sep Id[⟦B, E⟧]) g). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem funny_uncurry_curry {A B E : Category} (F : (A □ B) ⟶ E) :
  @equiv _ (@Functor_StrictEq_Setoid (A □ B) E)
    (FunnyUncurry (FunnyCurry F)) F.
Proof.
  apply (Funny_strict_eq (FunnyUncurry (FunnyCurry F)) F
           (fun _ _ => eq_refl)).
  - intros a a' f b.
    exact (id_left (@fmap (A □ B) E F (a, b) (a', b) (lstep f))).
  - intros a b b' g.
    exact (id_left (@fmap (A □ B) E F (a, b) (a, b') (rstep g))).
Qed.

Theorem funny_curry_uncurry {A B E : Category} (G : A ⟶ ⟦B, E⟧) (a : A) :
  @equiv _ (@Functor_StrictEq_Setoid B E)
    (FunnyCurry (FunnyUncurry G) a) (G a).
Proof.
  apply (Functor_StrictEq_intro (FunnyCurry (FunnyUncurry G) a) (G a)
           (fun _ => eq_refl)).
  intros b b' g.
  exact (id_left (fmap[G a] g)).
Qed.

Theorem funny_curry_uncurry_fmap {A B E : Category} (G : A ⟶ ⟦B, E⟧)
  {a a' : A} (f : a ~{A}~> a') :
  ∀ b : B, fmap[FunnyCurry (FunnyUncurry G)] f b ≈ fmap[G] f b.
Proof.
  intro b.
  exact (id_left (fmap[G] f b)).
Qed.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem funny_curry_beta {A B E : Category} (F : (A □ B) ⟶ E) :
  @equiv _ (@Functor_StrictEq_Setoid (A □ B) E)
    (FunnyEval ◯ FunnyBimap (FunnyCurry F) Id[B]) F.
Proof.
  apply (Funny_strict_eq (FunnyEval ◯ FunnyBimap (FunnyCurry F) Id[B]) F
           (fun _ _ => eq_refl)).
  - intros a a' f b.
    exact (id_left (@fmap (A □ B) E F (a, b) (a', b) (lstep f))).
  - intros a b b' g.
    exact (id_left (@fmap (A □ B) E F (a, b) (a, b') (rstep g))).
Qed.

Theorem funny_curry_unique {A B E : Category} (F : (A □ B) ⟶ E)
  (H : A ⟶ ⟦B, E⟧)
  (pf : @equiv _ (@Functor_StrictEq_Setoid (A □ B) E)
          (FunnyEval ◯ FunnyBimap H Id[B]) F) :
  ∀ a : A, @equiv _ (@Functor_StrictEq_Setoid B E) (H a) (FunnyCurry F a).
Proof.
  intro a.
  destruct pf as [eo em].
  apply (Functor_StrictEq_intro (H a) (FunnyCurry F a)
           (fun b => eo (a, b))).
  intros b b' g.
  etransitivity; [| exact (em (a, b) (a, b') (rstep g)) ].
  apply transport_cod_respects.
  symmetry.
  exact (id_left (fmap[H a] g)).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem funny_curry_unique_lstep {A B E : Category} (F : (A □ B) ⟶ E)
  (H : A ⟶ ⟦B, E⟧)
  (pf : @equiv _ (@Functor_StrictEq_Setoid (A □ B) E)
          (FunnyEval ◯ FunnyBimap H Id[B]) F)
  {a a' : A} (f : a ~{A}~> a') (b : B) :
  transport (fun z => H a b ~{E}~> z) (`1 pf (a', b)) (fmap[H] f b)
    ≈ transport_r (fun z => z ~{E}~> F (a', b)) (`1 pf (a, b))
        (@fmap (A □ B) E F (a, b) (a', b) (lstep f)).
Proof.
  destruct pf as [eo em]; simpl.
  etransitivity; [| exact (em (a, b) (a', b) (lstep f)) ].
  apply transport_cod_respects.
  symmetry.
  exact (id_left (fmap[H] f b)).
Qed.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition FunnyCurryF {A B E : Category} :
  (⟦A □ B, E⟧) ⟶ (⟦A, ⟦B, E⟧⟧) := {|
  fobj := FunnyCurry;
  fmap := fun F F' τ => fun a b => τ (a, b)
|}.

Program Definition FunnyUncurryF {A B E : Category} :
  (⟦A, ⟦B, E⟧⟧) ⟶ (⟦A □ B, E⟧) := {|
  fobj := FunnyUncurry;
  fmap := fun G G' σ => fun x => σ (fst x) (snd x)
|}.

(* The unit: [FunnyCurry (FunnyUncurry G) a b ≡ G a b] definitionally, so
   identity components form an isomorphism in ⟦A, ⟦B, E⟧⟧. *)

Lemma funny_curry_uncurry_iso_law {A B E : Category} (G : A ⟶ ⟦B, E⟧)
  (a : A) (b : B) :
  @id E (G a b) ∘ @id E (G a b) ≈ @id E (G a b).
Proof. cat. Qed.

Program Definition funny_curry_uncurry_iso {A B E : Category}
  (G : A ⟶ ⟦B, E⟧) :
  FunnyCurry (FunnyUncurry G) ≅[⟦A, ⟦B, E⟧⟧] G := {|
  to := fun a b => id;
  from := fun a b => id;
  iso_to_from := funny_curry_uncurry_iso_law G;
  iso_from_to := funny_curry_uncurry_iso_law G
|}.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition funny_pair_eta_to {A B E : Category} (F : (A □ B) ⟶ E)
  (x : A □ B) : F (fst x, snd x) ~{E}~> F x :=
  match x as p return (F (fst p, snd p) ~{E}~> F p) with
  | (a, b) => id
  end.

Definition funny_pair_eta_from {A B E : Category} (F : (A □ B) ⟶ E)
  (x : A □ B) : F x ~{E}~> F (fst x, snd x) :=
  match x as p return (F p ~{E}~> F (fst p, snd p)) with
  | (a, b) => id
  end.

Lemma funny_pair_eta_to_from {A B E : Category} (F : (A □ B) ⟶ E) :
  ∀ x : A □ B, funny_pair_eta_to F x ∘ funny_pair_eta_from F x ≈ id.
Proof. intros [a b]; simpl; cat. Qed.

Lemma funny_pair_eta_from_to {A B E : Category} (F : (A □ B) ⟶ E) :
  ∀ x : A □ B, funny_pair_eta_from F x ∘ funny_pair_eta_to F x ≈ id.
Proof. intros [a b]; simpl; cat. Qed.

Program Definition funny_uncurry_curry_iso {A B E : Category}
  (F : (A □ B) ⟶ E) :
  FunnyUncurry (FunnyCurry F) ≅[⟦A □ B, E⟧] F := {|
  to := funny_pair_eta_to F;
  from := funny_pair_eta_from F;
  iso_to_from := funny_pair_eta_to_from F;
  iso_from_to := funny_pair_eta_from_to F
|}.

Lemma Funny_exp_to_from {A B E : Category} :
  @equiv _ (@Functor_Setoid (⟦A, ⟦B, E⟧⟧) (⟦A, ⟦B, E⟧⟧))
    (@FunnyCurryF A B E ◯ @FunnyUncurryF A B E) Id.
Proof.
  exists funny_curry_uncurry_iso.
  intros G G' σ a b; simpl; cat.
Qed.

Lemma Funny_exp_from_to {A B E : Category} :
  @equiv _ (@Functor_Setoid (⟦A □ B, E⟧) (⟦A □ B, E⟧))
    (@FunnyUncurryF A B E ◯ @FunnyCurryF A B E) Id.
Proof.
  exists funny_uncurry_curry_iso.
  intros F F' τ [a b]; simpl; cat.
Qed.

Program Definition Funny_exponential_law {A B E : Category} :
  (⟦A □ B, E⟧) ≅[Cat] (⟦A, ⟦B, E⟧⟧) := {|
  to := FunnyCurryF;
  from := FunnyUncurryF;
  iso_to_from := Funny_exp_to_from;
  iso_from_to := Funny_exp_from_to
|}.
