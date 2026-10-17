Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * Indexed categories: the coherent pseudofunctor-lite *)

(*
   nLab:      https://ncatlab.org/nlab/show/pseudofunctor
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record IndexedCat (B : Category) : Type := {
  idx_fib : B → Category;

  idx_map {x y : B} (f : x ~> y) : idx_fib x ⟶ idx_fib y;

  (* Reindexing respects ≈ on base morphisms, up to a chosen fibre iso,
     natural in the fibre argument and proof-irrelevant ([idx_resp_id],
     [idx_resp_trans] make any two such isos agree). *)
  idx_resp {x y : B} {f g : x ~> y} (e : f ≈ g) (a : idx_fib x) :
    idx_map f a ≅[idx_fib y] idx_map g a;
  idx_resp_natural {x y : B} {f g : x ~> y} (e : f ≈ g)
                   {a b : idx_fib x} (k : a ~> b) :
    fmap[idx_map g] k ∘ to (idx_resp e a)
      ≈ to (idx_resp e b) ∘ fmap[idx_map f] k;
  idx_resp_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : idx_fib x) :
    to (idx_resp e a) ≈ id;
  idx_resp_trans {x y : B} {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h)
                 (a : idx_fib x) :
    to (idx_resp e2 a) ∘ to (idx_resp e1 a)
      ≈ to (idx_resp (Equivalence_Transitive _ _ _ e1 e2) a);

  (* Unit: reindexing along the identity is isomorphic to doing nothing,
     naturally in the fibre argument. *)
  idx_id {x : B} (a : idx_fib x) : idx_map (@id B x) a ≅ a;
  idx_id_natural {x : B} {a b : idx_fib x} (k : a ~> b) :
    k ∘ to (idx_id a) ≈ to (idx_id b) ∘ fmap[idx_map (@id B x)] k;

  (* Composition: reindexing twice is isomorphic to reindexing along the
     composite, naturally in the fibre argument. *)
  idx_comp {x y z : B} (f : y ~> z) (g : x ~> y) (a : idx_fib x) :
    idx_map f (idx_map g a) ≅ idx_map (f ∘ g) a;
  idx_comp_natural {x y z : B} (f : y ~> z) (g : x ~> y)
                   {a b : idx_fib x} (k : a ~> b) :
    fmap[idx_map (f ∘ g)] k ∘ to (idx_comp f g a)
      ≈ to (idx_comp f g b) ∘ fmap[idx_map f] (fmap[idx_map g] k);

  (*
   本节说明hom、双范畴相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  idx_comp_resp_l {x y z : B} {f f' : y ~> z} (g : x ~> y) (e : f ≈ f')
                  (e' : f ∘ g ≈ f' ∘ g) (a : idx_fib x) :
    to (idx_comp f' g a) ∘ to (idx_resp e (idx_map g a))
      ≈ to (idx_resp e' a) ∘ to (idx_comp f g a);
  idx_comp_resp_r {x y z : B} (f : y ~> z) {g g' : x ~> y} (e : g ≈ g')
                  (e' : f ∘ g ≈ f ∘ g') (a : idx_fib x) :
    to (idx_comp f g' a) ∘ fmap[idx_map f] (to (idx_resp e a))
      ≈ to (idx_resp e' a) ∘ to (idx_comp f g a);

  (*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  idx_unit_left {x y : B} (f : x ~> y) (a : idx_fib x) :
    to (idx_resp (id_left f) a) ∘ to (idx_comp id f a)
      ≈ to (idx_id (idx_map f a));
  idx_unit_right {x y : B} (f : x ~> y) (a : idx_fib x) :
    to (idx_resp (id_right f) a) ∘ to (idx_comp f id a)
      ≈ fmap[idx_map f] (to (idx_id a));
  idx_cocycle {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
              (a : idx_fib w) :
    to (idx_comp (f ∘ g) h a) ∘ to (idx_comp f g (idx_map h a))
      ≈ to (idx_resp (comp_assoc f g h) a)
          ∘ to (idx_comp f (g ∘ h) a) ∘ fmap[idx_map f] (to (idx_comp g h a))
}.

Arguments idx_fib {B} _ _.
Arguments idx_map {B} _ {x y} _.
Arguments idx_resp {B} _ {x y f g} _ _.
Arguments idx_resp_natural {B} _ {x y f g} _ {a b} _.
Arguments idx_resp_id {B} _ {x y f} _ _.
Arguments idx_resp_trans {B} _ {x y f g h} _ _ _.
Arguments idx_id {B} _ {x} _.
Arguments idx_id_natural {B} _ {x a b} _.
Arguments idx_comp {B} _ {x y z} _ _ _.
Arguments idx_comp_natural {B} _ {x y z} _ _ {a b} _.
Arguments idx_comp_resp_l {B} _ {x y z f f'} _ _ _ _.
Arguments idx_comp_resp_r {B} _ {x y z} _ {g g'} _ _ _.
Arguments idx_unit_left {B} _ {x y} _ _.
Arguments idx_unit_right {B} _ {x y} _ _.
Arguments idx_cocycle {B} _ {w x y z} _ _ _ _.

(*
   本节说明 Indexed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section IndexedCatLemmas.

Context {B : Category}.
Context (A : IndexedCat B).

(* [idx_resp] at a reflexivity-flavoured proof has identity inverse as well:
   the [from]-side companion to [idx_resp_id]. *)
Lemma idx_resp_from_id {x y : B} {f : x ~> y} (e : f ≈ f) (a : idx_fib A x) :
  from (idx_resp A e a) ≈ id.
Proof.
  rewrite <- (iso_from_to (idx_resp A e a)).
  rewrite (idx_resp_id A e a).
  now rewrite id_right.
Qed.

(* The chosen iso at a symmetric proof is the inverse of the chosen iso:
   [to] at [symmetry e] agrees with [from] at [e]. *)
Lemma idx_resp_to_sym {x y : B} {f g : x ~> y} (e : f ≈ g) (a : idx_fib A x) :
  to (idx_resp A (symmetry e) a) ≈ from (idx_resp A e a).
Proof.
  apply (comp_inverse_unique (to (idx_resp A e a))).
  - rewrite (idx_resp_trans A (symmetry e) e a).
    apply idx_resp_id.
  - apply iso_from_to.
Qed.

(* Proof irrelevance: the chosen isos at any two proofs of [f ≈ g] agree.
   This is the [idx_resp_id]/[idx_resp_trans] pair in the form downstream
   proofs use directly. *)
Lemma idx_resp_irrel {x y : B} {f g : x ~> y} (e e' : f ≈ g)
      (a : idx_fib A x) :
  to (idx_resp A e a) ≈ to (idx_resp A e' a).
Proof.
  apply (comp_inverse_unique (from (idx_resp A e' a))).
  - rewrite <- (idx_resp_to_sym e' a).
    rewrite (idx_resp_trans A e (symmetry e') a).
    apply idx_resp_id.
  - apply iso_to_from.
Qed.

(* [from] at [symmetry e] agrees with [to] at [e]. *)
Lemma idx_resp_from_sym {x y : B} {f g : x ~> y} (e : f ≈ g)
      (a : idx_fib A x) :
  from (idx_resp A (symmetry e) a) ≈ to (idx_resp A e a).
Proof.
  rewrite <- (idx_resp_to_sym (symmetry e) a).
  apply idx_resp_irrel.
Qed.

(* Proof irrelevance on the [from] side. *)
Lemma idx_resp_from_irrel {x y : B} {f g : x ~> y} (e e' : f ≈ g)
      (a : idx_fib A x) :
  from (idx_resp A e a) ≈ from (idx_resp A e' a).
Proof.
  rewrite <- (idx_resp_to_sym e a), <- (idx_resp_to_sym e' a).
  apply idx_resp_irrel.
Qed.

(* Transitivity on the [from] side: inverses compose in reverse order. *)
Lemma idx_resp_from_trans {x y : B} {f g h : x ~> y}
      (e1 : f ≈ g) (e2 : g ≈ h) (a : idx_fib A x) :
  from (idx_resp A e1 a) ∘ from (idx_resp A e2 a)
    ≈ from (idx_resp A (Equivalence_Transitive _ _ _ e1 e2) a).
Proof.
  rewrite <- (idx_resp_to_sym e1 a), <- (idx_resp_to_sym e2 a),
          <- (idx_resp_to_sym (Equivalence_Transitive _ _ _ e1 e2) a).
  rewrite (idx_resp_trans A (symmetry e2) (symmetry e1) a).
  apply idx_resp_irrel.
Qed.

(* Naturality of [idx_resp] on the [from] side, by conjugating
   [idx_resp_natural] with the inverses. *)
Lemma idx_resp_natural_from {x y : B} {f g : x ~> y} (e : f ≈ g)
      {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A f] k ∘ from (idx_resp A e a)
    ≈ from (idx_resp A e b) ∘ fmap[idx_map A g] k.
Proof.
  rewrite <- (id_left (fmap[idx_map A f] k)).
  rewrite <- (iso_from_to (idx_resp A e b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_resp_natural A e k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_resp A e a)).
  apply id_right.
Qed.

(* Naturality of [idx_id] on the [from] side. *)
Lemma idx_id_natural_from {x : B} {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A (@id B x)] k ∘ from (idx_id A a) ≈ from (idx_id A b) ∘ k.
Proof.
  rewrite <- (id_left (fmap[idx_map A (@id B x)] k)).
  rewrite <- (iso_from_to (idx_id A b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_id_natural A k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_id A a)).
  apply id_right.
Qed.

(* Naturality of [idx_comp] on the [from] side. *)
Lemma idx_comp_natural_from {x y z : B} (f : y ~> z) (g : x ~> y)
      {a b : idx_fib A x} (k : a ~> b) :
  fmap[idx_map A f] (fmap[idx_map A g] k) ∘ from (idx_comp A f g a)
    ≈ from (idx_comp A f g b) ∘ fmap[idx_map A (f ∘ g)] k.
Proof.
  rewrite <- (id_left (fmap[idx_map A f] (fmap[idx_map A g] k))).
  rewrite <- (iso_from_to (idx_comp A f g b)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite comp_assoc.
  rewrite <- (idx_comp_natural A f g k).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (idx_comp A f g a)).
  apply id_right.
Qed.

End IndexedCatLemmas.
