Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * The traced (cowriter, exponent) 余单子 （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   本文件给出带迹范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Paper:   Eilenberg, Moore, "Adjoint functors and triples", Illinois

   本节说明伴随、函子、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Traced.

(** The section-context 幺半群: ordinary Coq data — bare type together
 unit, multiplication, three 幺半群 equations Leibniz
 laws. （已译） *)

Context (m : Type).
Context (mempty : m).
Context (mappend : m → m → m).

Hypothesis mempty_left  : ∀ w : m, mappend mempty w = w.
Hypothesis mempty_right : ∀ w : m, mappend w mempty = w.
Hypothesis mappend_assoc :
  ∀ u v w : m, mappend u (mappend v w) = mappend (mappend u v) w.

(*
   本节说明函子、余单子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：The plan-prescribed action raw types: post-compose observation. （已译） *)
Definition coq_traced_map {x y : Type} (f : x → y) (h : m → x) : m → y :=
  λ w, f (h w).

(** 本节：The counit raw types: evaluate at neutral trace. （已译） *)
Definition coq_traced_extract {x : Type} (h : m → x) : x := h mempty.

(** The comultiplication on raw types: evaluate under every translation. *)
Definition coq_traced_duplicate {x : Type} (h : m → x) : m → m → x :=
  λ w w', h (mappend w w').

(** 本节：Four equations definitional at function level: beta and
 eta functions part Coq's conversion. （已译） *)

Lemma coq_traced_map_id {x : Type} (h : m → x) :
  coq_traced_map (λ v : x, v) h = h.
Proof. reflexivity. Qed.

Lemma coq_traced_map_comp {x y z : Type} (f : y → z) (g : x → y)
  (h : m → x) :
  coq_traced_map (λ v, f (g v)) h = coq_traced_map f (coq_traced_map g h).
Proof. reflexivity. Qed.

(** 本节：Naturality counit — op-read [fmap_ret]. （已译） *)
Lemma coq_traced_extract_natural {x y : Type} (f : x → y) (h : m → x) :
  f (coq_traced_extract h) = coq_traced_extract (coq_traced_map f h).
Proof. reflexivity. Qed.

(** 本节：Naturality comultiplication — op-read [join_fmap_fmap]. （已译） *)
Lemma coq_traced_duplicate_natural {x y : Type} (f : x → y) (h : m → x) :
  coq_traced_map (coq_traced_map f) (coq_traced_duplicate h)
    = coq_traced_duplicate (coq_traced_map f h).
Proof. reflexivity. Qed.

(** The remaining three equations consult 幺半群 laws hold pointwise
 — each plan's restatement corresponding law at sampled
 trace. （已译） *)

(** Counit law ε ∘ δ ≈ id, pointwise — the op-read of [join_ret]. *)
Lemma coq_traced_extract_duplicate {x : Type} (h : m → x) (w : m) :
  coq_traced_extract (coq_traced_duplicate h) w = h w.
Proof using mempty_left.
  unfold coq_traced_extract, coq_traced_duplicate.
  now rewrite mempty_left.
Qed.

(** Counit law W ε ∘ δ ≈ id, pointwise — the op-read of [join_fmap_ret]. *)
Lemma coq_traced_fmap_extract_duplicate {x : Type} (h : m → x) (w : m) :
  coq_traced_map coq_traced_extract (coq_traced_duplicate h) w = h w.
Proof using mempty_right.
  unfold coq_traced_map, coq_traced_extract, coq_traced_duplicate.
  now rewrite mempty_right.
Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ, pointwise — the op-read of
    [join_fmap_join]. *)
Lemma coq_traced_duplicate_coassoc {x : Type} (h : m → x) (a b c : m) :
  coq_traced_map coq_traced_duplicate (coq_traced_duplicate h) a b c
    = coq_traced_duplicate (coq_traced_duplicate h) a b c.
Proof using mappend_assoc.
  unfold coq_traced_map, coq_traced_duplicate.
  now rewrite mappend_assoc.
Qed.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma coq_traced_map_proper_entails_funext {y : Type}
  (respects : ∀ f g : m → y,
      (∀ v, f v = g v) →
      ∀ h : m → m, coq_traced_map f h = coq_traced_map g h) :
  ∀ f g : m → y, (∀ v, f v = g v) → f = g.
Proof.
  intros f g Hfg.
  exact (respects f g Hfg (λ w, w)).
Qed.

(** ** The traced setoid on [Sets] *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition traced_equiv {x : SetoidObject} : crelation (m → carrier x) :=
  λ h k, ∀ w : m, h w ≈ k w.

Arguments traced_equiv {x} _ _ /.

#[local] Obligation Tactic := idtac.

Program Definition traced_obj (x : SetoidObject) : SetoidObject := {|
  carrier := m → carrier x;
  is_setoid := {| equiv := traced_equiv; setoid_equiv := _ |}
|}.
Next Obligation.
  intros x; constructor.
  - intros h w.
    reflexivity.
  - intros h k Hhk w.
    symmetry; apply Hhk.
  - intros h k l Hhk Hkl w.
    etransitivity.
    + apply Hhk.
    + apply Hkl.
Qed.

(** ** The functorial action *)

(* Post-复合 under trace: f applied value observed at
 every trace. （已译） *)
Program Definition traced_map {x y : SetoidObject} (f : SetoidMorphism x y) :
  SetoidMorphism (traced_obj x) (traced_obj y) := {|
  morphism := λ h w, f (h w)
|}.
Next Obligation.
  intros x y f h k Hhk w; simpl.
  apply proper_morphism, Hhk.
Qed.

(** 本节：[traced_map] respects ≈ pointwise — field whose COQ counterpart is
 funext-entailing obligation above; here it immediate. （已译） *)
Lemma traced_map_respects {x y : SetoidObject} (f g : SetoidMorphism x y) :
  (∀ v : carrier x, f v ≈ g v) →
  ∀ h : m → carrier x, traced_equiv (traced_map f h) (traced_map g h).
Proof.
  intros Hfg h w; simpl.
  apply Hfg.
Qed.

Lemma traced_map_id {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map setoid_morphism_id h) h.
Proof.
  intros w; simpl.
  reflexivity.
Qed.

Lemma traced_map_comp {x y z : SetoidObject}
  (f : SetoidMorphism y z) (g : SetoidMorphism x y) (h : m → carrier x) :
  traced_equiv (traced_map (setoid_morphism_compose f g) h)
               (traced_map f (traced_map g h)).
Proof.
  intros w; simpl.
  reflexivity.
Qed.

(** The traced endofunctor m ⇒ − on [Sets]. *)
Definition TracedF : Sets ⟶ Sets := @Build_Functor Sets Sets
  (λ x : SetoidObject, traced_obj x)
  (λ (x y : SetoidObject) (f : SetoidMorphism x y), @traced_map x y f)
  (λ x y : SetoidObject, @traced_map_respects x y)
  (λ x : SetoidObject, @traced_map_id x)
  (λ (x y z : SetoidObject) (f : SetoidMorphism y z) (g : SetoidMorphism x y),
     @traced_map_comp x y z f g).

(** ** The comonad structure *)

(** 本节：The counit ε: evaluate at neutral trace. （已译） *)
Program Definition traced_extract {x : SetoidObject} :
  SetoidMorphism (traced_obj x) x := {|
  morphism := λ h, h mempty
|}.
Next Obligation.
  intros x h k Hhk; simpl.
  apply Hhk.
Qed.

(** The comultiplication δ: evaluate under every further translation. *)
Program Definition traced_duplicate {x : SetoidObject} :
  SetoidMorphism (traced_obj x) (traced_obj (traced_obj x)) := {|
  morphism := λ h w w', h (mappend w w')
|}.
Next Obligation.
  intros x h k Hhk w w'; simpl.
  apply Hhk.
Qed.

(** 本节：Naturality counit — op-read [fmap_ret]. （已译） *)
Lemma traced_extract_natural {x y : SetoidObject} (f : SetoidMorphism x y)
  (h : m → carrier x) :
  f (traced_extract h) ≈ traced_extract (traced_map f h).
Proof. reflexivity. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. *)
Lemma traced_duplicate_coassoc {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map traced_duplicate (traced_duplicate h))
               (traced_duplicate (traced_duplicate h)).
Proof using mappend_assoc.
  intros a b c; simpl.
  now rewrite mappend_assoc.
Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. *)
Lemma traced_fmap_extract_duplicate {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map traced_extract (traced_duplicate h)) h.
Proof using mempty_right.
  intros w; simpl.
  now rewrite mempty_right.
Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. *)
Lemma traced_extract_duplicate {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_extract (traced_duplicate h)) h.
Proof using mempty_left.
  intros w; simpl.
  now rewrite mempty_left.
Qed.

(** 本节：Naturality comultiplication — op-read [join_fmap_fmap]. （已译） *)
Lemma traced_duplicate_natural {x y : SetoidObject} (f : SetoidMorphism x y)
  (h : m → carrier x) :
  traced_equiv (traced_map (traced_map f) (traced_duplicate h))
               (traced_duplicate (traced_map f h)).
Proof.
  intros w w'; simpl.
  reflexivity.
Qed.

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Traced_Comonad : @Comonad Sets TracedF :=
  @Build_Monad (Sets^op) (TracedF^op)
    (λ x : SetoidObject, @traced_extract x)           (* ret  = ε *)
    (λ x : SetoidObject, @traced_duplicate x)         (* join = δ *)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @traced_extract_natural y x f)
    (λ x : SetoidObject, @traced_duplicate_coassoc x)
    (λ x : SetoidObject, @traced_fmap_extract_duplicate x)
    (λ x : SetoidObject, @traced_extract_duplicate x)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @traced_duplicate_natural y x f).

#[local] Existing Instance Traced_Comonad.

(*
   本节说明余单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Traced_extract_spec {x : SetoidObject} (h : m → carrier x) :
  extract[TracedF] h = h mempty.
Proof. reflexivity. Qed.

Lemma Traced_duplicate_spec {x : SetoidObject} (h : m → carrier x)
  (w w' : m) :
  duplicate[TracedF] h w w' = h (mappend w w').
Proof. reflexivity. Qed.

Lemma Traced_extend_spec {x y : SetoidObject}
  (f : SetoidMorphism (traced_obj x) y) (h : m → carrier x) (w : m) :
  extend[TracedF] f h w = f (λ w' : m, h (mappend w w')).
Proof. reflexivity. Qed.

End Traced.

(*
   本节说明余单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
