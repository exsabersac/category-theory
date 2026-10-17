Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The store (costate) comonad *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   本文件给出 store 共态相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/store+comonad
   Paper: O'Connor, "Functor is to Lens as Applicative is to Biplate:

   本节说明余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、余单子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The plan-prescribed action on raw types: apply f to every observation,
    keep the focus. *)
Definition coq_store_map {s x y : Type} (f : x → y) (p : (s → x) * s) :
  (s → y) * s :=
  match p with (h, s0) => ((λ σ, f (h σ)), s0) end.

(** The counit on raw types: observe at the current focus. *)
Definition coq_store_extract {s x : Type} (p : (s → x) * s) : x :=
  match p with (h, s0) => h s0 end.

(** The comultiplication on raw types: refocus at every position. *)
Definition coq_store_duplicate {s x : Type} (p : (s → x) * s) :
  (s → (s → x) * s) * s :=
  match p with (h, s0) => ((λ σ, (h, σ)), s0) end.

(** Both functor equations hold pointwise; eta for functions is part of
    Coq's definitional equality, so destructuring the pair suffices. *)

Lemma coq_store_map_id {s x : Type} (p : (s → x) * s) :
  coq_store_map (λ v : x, v) p = p.
Proof. now destruct p. Qed.

Lemma coq_store_map_comp {s x y z : Type} (f : y → z) (g : x → y)
  (p : (s → x) * s) :
  coq_store_map (λ v, f (g v)) p = coq_store_map f (coq_store_map g p).
Proof. now destruct p. Qed.

(** So do all five comonad equations, stated in the op-read orientation of
    Theory/Monad.v's monad laws (cf. Instance/Coq/Comonad/Env.v). *)

Lemma coq_store_extract_natural {s x y : Type} (f : x → y)
  (p : (s → x) * s) :
  f (coq_store_extract p) = coq_store_extract (coq_store_map f p).
Proof. now destruct p. Qed.

Lemma coq_store_duplicate_coassoc {s x : Type} (p : (s → x) * s) :
  coq_store_map coq_store_duplicate (coq_store_duplicate p)
    = coq_store_duplicate (coq_store_duplicate p).
Proof. now destruct p. Qed.

Lemma coq_store_fmap_extract_duplicate {s x : Type} (p : (s → x) * s) :
  coq_store_map coq_store_extract (coq_store_duplicate p) = p.
Proof. now destruct p. Qed.

Lemma coq_store_extract_duplicate {s x : Type} (p : (s → x) * s) :
  coq_store_extract (coq_store_duplicate p) = p.
Proof. now destruct p. Qed.

Lemma coq_store_duplicate_natural {s x y : Type} (f : x → y)
  (p : (s → x) * s) :
  coq_store_map (coq_store_map f) (coq_store_duplicate p)
    = coq_store_duplicate (coq_store_map f p).
Proof. now destruct p. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma coq_store_map_proper_entails_funext {s y : Type} (s0 : s)
  (respects : ∀ f g : s → y,
      (∀ v, f v = g v) →
      ∀ p : (s → s) * s, coq_store_map f p = coq_store_map g p) :
  ∀ f g : s → y, (∀ v, f v = g v) → f = g.
Proof.
  intros f g Hfg.
  exact (f_equal fst (respects f g Hfg ((λ σ, σ), s0))).
Qed.

(** ** The store setoid on [Sets] *)

(*
   本节说明 Store 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition store_equiv {s x : SetoidObject} :
  crelation (SetoidMorphism s x * carrier s) :=
  λ p q, ((∀ σ : carrier s, fst p σ ≈ fst q σ) * (snd p ≈ snd q))%type.

Arguments store_equiv {s x} _ _ /.

#[local] Obligation Tactic := idtac.

Program Definition store_obj (s x : SetoidObject) : SetoidObject := {|
  carrier := SetoidMorphism s x * carrier s;
  is_setoid := {| equiv := store_equiv; setoid_equiv := _ |}
|}.
Next Obligation.
  intros s x; constructor.
  - intros p; split.
    + intros σ; reflexivity.
    + reflexivity.
  - intros p q [Hh Hs]; split.
    + intros σ; symmetry; apply Hh.
    + now symmetry.
  - intros p q r [Hh Hs] [Hg Ht]; split.
    + intros σ; etransitivity.
      * apply Hh.
      * apply Hg.
    + etransitivity.
      * exact Hs.
      * exact Ht.
Qed.

(** ** The functorial action *)

(* Post-composition under the observation map: f is applied to every
   observation, the focus is kept. *)
Program Definition store_map {s x y : SetoidObject} (f : SetoidMorphism x y) :
  SetoidMorphism (store_obj s x) (store_obj s y) := {|
  morphism := λ p, (setoid_morphism_compose f (fst p), snd p)
|}.
Next Obligation.
  intros s x y f p q [Hh Hs]; split.
  - intros σ; simpl.
    apply proper_morphism, Hh.
  - exact Hs.
Qed.

(** [store_map] respects ≈ pointwise — the field whose COQ counterpart is
    the funext-entailing obligation above; here it is immediate. *)
Lemma store_map_respects {s x y : SetoidObject} (f g : SetoidMorphism x y) :
  (∀ v : carrier x, f v ≈ g v) →
  ∀ p : SetoidMorphism s x * carrier s,
    store_equiv (store_map f p) (store_map g p).
Proof.
  intros Hfg p; split.
  - intros σ; simpl.
    apply Hfg.
  - reflexivity.
Qed.

Lemma store_map_id {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map setoid_morphism_id p) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

Lemma store_map_comp {s x y z : SetoidObject}
  (f : SetoidMorphism y z) (g : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map (setoid_morphism_compose f g) p)
              (store_map f (store_map g p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** The store endofunctor (s ⇒ −) × s on [Sets]. *)
Definition StoreF (s : SetoidObject) : Sets ⟶ Sets := @Build_Functor Sets Sets
  (λ x : SetoidObject, store_obj s x)
  (λ (x y : SetoidObject) (f : SetoidMorphism x y), @store_map s x y f)
  (λ x y : SetoidObject, @store_map_respects s x y)
  (λ x : SetoidObject, @store_map_id s x)
  (λ (x y z : SetoidObject) (f : SetoidMorphism y z) (g : SetoidMorphism x y),
     @store_map_comp s x y z f g).

(** ** The comonad structure *)

(** The counit ε: observe at the current focus. *)
Program Definition store_extract {s x : SetoidObject} :
  SetoidMorphism (store_obj s x) x := {|
  morphism := λ p, fst p (snd p)
|}.
Next Obligation.
  intros s x p q [Hh Hs]; simpl.
  etransitivity.
  - apply Hh.
  - now apply proper_morphism.
Qed.

(* Refocusing: pair the observation map with every position — the
   observation component of [duplicate]. *)
Program Definition store_seek {s x : SetoidObject} (h : SetoidMorphism s x) :
  SetoidMorphism s (store_obj s x) := {|
  morphism := λ σ, (h, σ)
|}.
Next Obligation.
  intros s x h σ τ Hστ; split.
  - intros ρ; reflexivity.
  - exact Hστ.
Qed.

(** The comultiplication δ: a store of stores, refocused at every position. *)
Program Definition store_duplicate {s x : SetoidObject} :
  SetoidMorphism (store_obj s x) (store_obj s (store_obj s x)) := {|
  morphism := λ p, (store_seek (fst p), snd p)
|}.
Next Obligation.
  intros s x p q [Hh Hs]; split.
  - intros σ; split.
    + intros τ; apply Hh.
    + reflexivity.
  - exact Hs.
Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. *)
Lemma store_extract_natural {s x y : SetoidObject} (f : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  f (store_extract p) ≈ store_extract (store_map f p).
Proof. reflexivity. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. *)
Lemma store_duplicate_coassoc {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map store_duplicate (store_duplicate p))
              (store_duplicate (store_duplicate p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. *)
Lemma store_fmap_extract_duplicate {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map store_extract (store_duplicate p)) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. *)
Lemma store_extract_duplicate {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_extract (store_duplicate p)) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. *)
Lemma store_duplicate_natural {s x y : SetoidObject} (f : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map (store_map f) (store_duplicate p))
              (store_duplicate (store_map f p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Store_Comonad (s : SetoidObject) :
  @Comonad Sets (StoreF s) :=
  @Build_Monad (Sets^op) ((StoreF s)^op)
    (λ x : SetoidObject, @store_extract s x)          (* ret  = ε *)
    (λ x : SetoidObject, @store_duplicate s x)        (* join = δ *)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @store_extract_natural s y x f)
    (λ x : SetoidObject, @store_duplicate_coassoc s x)
    (λ x : SetoidObject, @store_fmap_extract_duplicate s x)
    (λ x : SetoidObject, @store_extract_duplicate s x)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @store_duplicate_natural s y x f).

(*
   本节说明余单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Store_extract_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 : carrier s) :
  extract[StoreF s] (h, s0) = h s0.
Proof. reflexivity. Qed.

Lemma Store_duplicate_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 : carrier s) :
  duplicate[StoreF s] (h, s0) = (store_seek h, s0).
Proof. reflexivity. Qed.

Lemma Store_seek_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 σ : carrier s) :
  fst (duplicate[StoreF s] (h, s0)) σ = (h, σ).
Proof. reflexivity. Qed.

Lemma Store_extend_spec {s x y : SetoidObject}
  (f : SetoidMorphism (store_obj s x) y) (h : SetoidMorphism s x)
  (s0 σ : carrier s) :
  fst (extend[StoreF s] f (h, s0)) σ = f (h, σ).
Proof. reflexivity. Qed.

Lemma Store_extend_pos_spec {s x y : SetoidObject}
  (f : SetoidMorphism (store_obj s x) y) (h : SetoidMorphism s x)
  (s0 : carrier s) :
  snd (extend[StoreF s] f (h, s0)) = s0.
Proof. reflexivity. Qed.
