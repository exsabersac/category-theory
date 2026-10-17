Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Construction.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Right.

Generalizable All Variables.

(*
   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module PAT := Category.Adjunction.Natural.Transformation.

(** * Adjunctions with a parameter *)

(*
   nLab: https://ncatlab.org/nlab/show/parametrized+adjoint
   nLab: https://ncatlab.org/nlab/show/adjoint+functor

   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** A. The 假设: family right adjoints partial 函子 （已译） *)

Section ParametrizedAdjunction.

Context {X P A : Category}.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record ParametrizedAdjunction (F : X ∏ P ⟶ A) := {
  pa_right : P → (A ⟶ X);
  pa_adj (p : P) : Partial_l F p ⊣ pa_right p
}.

End ParametrizedAdjunction.

Arguments ParametrizedAdjunction {X P A} F.
Arguments pa_right {X P A F} _ _.
Arguments pa_adj {X P A F} _ _.

(* 相关说明。 （已译） *)

Section ParamTransform.

Context {X P A : Category}.
Context (F : X ∏ P ⟶ A).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition param_transform {p p' : P} (h : p ~> p') :
  Partial_l F p ⟹ Partial_l F p' := {|
  transform := fun x => fmap[Partial_r F x] h
|}.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.

(* The component identification, at Leibniz equality, in both spellings. *)

Example param_transform_component {p p' : P} (h : p ~> p') (x : X) :
  transform[param_transform h] x = fmap[Partial_r F x] h := eq_refl.

Example param_transform_component_bimap {p p' : P} (h : p ~> p') (x : X) :
  transform[param_transform h] x = @bimap X P A F x x p p' id h := eq_refl.

Lemma param_transform_respects {p p' : P} (h h' : p ~> p') :
  h ≈ h' → param_transform h ≈ param_transform h'.
Proof. intros E x; simpl; now rewrite E. Qed.

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example param_transform_id_component {p : P} (x : X) :
  transform[param_transform (id[p])] x
    = transform[@nat_id X A (Partial_l F p)] x := eq_refl.

Lemma param_transform_id {p : P} : param_transform (id[p]) ≈ nat_id.
Proof. intro x; simpl; reflexivity. Qed.

Lemma param_transform_comp {p p' p'' : P}
      (h : p ~> p') (h' : p' ~> p'') :
  param_transform (h' ∘ h) ≈ param_transform h' ∙ param_transform h.
Proof. intro x; simpl; apply bimap_comp_id_left. Qed.

End ParamTransform.

Arguments param_transform {X P A} F {p p'} h.

(** ** C. Theorem 3 *)

Section Theorem3.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).

Notation "'G'" := (pa_right PA) (only parsing).

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pa_to (p : P) (x : X) (a : A) (k : F (x, p) ~> a) : x ~> G p a :=
  to (@adj A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) x a) k.

Definition pa_from (p : P) (x : X) (a : A) (g : x ~> G p a) : F (x, p) ~> a :=
  from (@adj A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) x a) g.

(* 相关说明。 （已译） *)

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pa_param_mate {p p' : P} (h : p' ~> p) : G p ⟹ G p' :=
  conj_mate (pa_adj PA p) (pa_adj PA p') (param_transform F h).

(* Mac Lane's closing sentence — "this assignment ... may also be described
   as the unique way to make G(h,−) a natural transformation conjugate to
   F(−,h)" — holds here by construction, not as a comparison. *)

Example pa_param_mate_is_conj_mate {p p' : P} (h : p' ~> p) :
  pa_param_mate h
    = conj_mate (pa_adj PA p) (pa_adj PA p') (param_transform F h)
  := eq_refl.

(* --- naturality in each of the three variables --- *)

(* In x there nothing new: these ARE [Adjunction] fields at a
 fixed parameter, re-exposed so consumer file sees all three
 自然性 statements together. （已译） *)

Lemma pa_natural_x (p : P) {x y : X} {a : A}
      (k : F (y, p) ~> a) (g : x ~> y) :
  pa_to p x a (k ∘ fmap[Partial_l F p] g) ≈ pa_to p y a k ∘ g.
Proof. exact (to_adj_nat_l (Adjunction:=pa_adj PA p) k g). Qed.

Lemma pa_natural_a (p : P) {x : X} {a b : A}
      (f : a ~> b) (k : F (x, p) ~> a) :
  pa_to p x b (f ∘ k) ≈ fmap[G p] f ∘ pa_to p x a k.
Proof. exact (to_adj_nat_r (Adjunction:=pa_adj PA p) f k). Qed.

(* Naturality in p is Mac Lane's square.  Stated elementarily first, so a
   reader sees the equation without unfolding any class. *)

Definition pa_square {p p' : P} (h : p' ~> p)
           (tau : G p ⟹ G p') : Type :=
  ∀ (x : X) (a : A) (k : F (x, p) ~> a),
    pa_to p' x a (k ∘ fmap[Partial_r F x] h) ≈ tau a ∘ pa_to p x a k.

(* 相关说明。 （已译） *)

Example pa_square_is_Conjugate {p p' : P} (h : p' ~> p)
        (tau : G p ⟹ G p') :
  pa_square h tau
    = Conjugate (pa_adj PA p) (pa_adj PA p') (param_transform F h) tau
  := eq_refl.

Theorem pa_natural_p {p p' : P} (h : p' ~> p) :
  pa_square h (pa_param_mate h).
Proof.
  exact (conjugate_conj_mate (pa_adj PA p) (pa_adj PA p')
           (param_transform F h)).
Qed.

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pa_square_from {p p' : P} (h : p' ~> p)
           (tau : G p ⟹ G p') : Type :=
  ∀ (x : X) (a : A) (g : x ~> G p a),
    pa_from p' x a (tau a ∘ g)
      ≈ pa_from p x a g ∘ fmap[Partial_r F x] h.

Example pa_square_from_is_ConjugateFrom {p p' : P} (h : p' ~> p)
        (tau : G p ⟹ G p') :
  pa_square_from h tau
    = ConjugateFrom (pa_adj PA p) (pa_adj PA p') (param_transform F h) tau
  := eq_refl.

Theorem pa_square_iff_from {p p' : P} (h : p' ~> p) (tau : G p ⟹ G p') :
  pa_square h tau ↔ pa_square_from h tau.
Proof.
  exact (conjugate_iff_from (pa_adj PA p) (pa_adj PA p')
           (param_transform F h) tau).
Defined.

(* --- the two functor laws of G(−,a), by uniqueness of conjugates --- *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma pa_param_mate_respects {p p' : P} (h h' : p' ~> p) :
  h ≈ h' → pa_param_mate h ≈ pa_param_mate h'.
Proof.
  intro E; unfold pa_param_mate.
  apply conj_mate_respects, param_transform_respects, E.
Qed.

Lemma pa_param_mate_id {p : P} : pa_param_mate (id[p]) ≈ nat_id.
Proof.
  unfold pa_param_mate.
  rewrite (conj_mate_respects (pa_adj PA p) (pa_adj PA p) _ nat_id
             (param_transform_id F)).
  apply conj_mate_id.
Qed.

Lemma pa_param_mate_comp {p p' p'' : P} (h : p' ~> p) (h' : p'' ~> p') :
  pa_param_mate (h ∘ h') ≈ pa_param_mate h' ∙ pa_param_mate h.
Proof.
  unfold pa_param_mate.
  rewrite (conj_mate_respects (pa_adj PA p) (pa_adj PA p'') _ _
             (param_transform_comp F h' h)).
  apply (conj_mate_compose (pa_adj PA p) (pa_adj PA p') (pa_adj PA p'')).
Qed.

(* 相关说明。 （已译） *)

Lemma pa_param_mate_id_at {p : P} (a : A) : pa_param_mate (id[p]) a ≈ id.
Proof.
  transitivity (transform[@nat_id A X (G p)] a).
  - exact (pa_param_mate_id a).
  - apply fmap_id.
Qed.

Lemma pa_param_mate_comp_at {p p' p'' : P}
      (h : p' ~> p) (h' : p'' ~> p') (a : A) :
  pa_param_mate (h ∘ h') a ≈ pa_param_mate h' a ∘ pa_param_mate h a.
Proof. exact (pa_param_mate_comp h h' a). Qed.

(* --- Mac Lane's G : P^op × A → X --- *)

#[local] Obligation Tactic := idtac.

Program Definition parametrized_right_adjoint_bifunctor : P^op ∏ A ⟶ X := {|
  fobj := fun q => G (fst q) (snd q);
  fmap := fun q q' hk =>
            fmap[G (fst q')] (snd hk)
              ∘ pa_param_mate (unop (fst hk)) (snd q)
|}.
Next Obligation.
  intros [p a] [p' a'] [h k] [h' k'] [Eh Ek]; simpl in Eh, Ek.
  apply compose_respects.
  - now apply fmap_respects.
  - exact (pa_param_mate_respects (unop h) (unop h') Eh a).
Qed.
Next Obligation.
  intros [p a].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (pa_param_mate_id_at a) ]. }
  simpl.
  rewrite !fmap_id.
  now rewrite id_left.
Qed.
Next Obligation.
  intros [p a] [p' a'] [p'' a''] [h k] [h' k'].
  etransitivity.
  { apply compose_respects.
    - apply fmap_comp.
    - exact (pa_param_mate_comp_at (unop h') (unop h) a). }
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (naturality (pa_param_mate (unop h)) _ _ k').
Qed.

#[local] Obligation Tactic := program_simpl.

(* The bifunctor's two actions, read back at Leibniz equality. *)

Example pa_bifunctor_obj (p : P) (a : A) :
  fobj[parametrized_right_adjoint_bifunctor] (p, a) = G p a := eq_refl.

Example pa_bifunctor_fmap {p p' : P} {a a' : A}
        (h : p ~{P^op}~> p') (k : a ~> a') :
  fmap[parametrized_right_adjoint_bifunctor] ((h, k) :
        (p, a) ~{P^op ∏ A}~> (p', a'))
    = fmap[G p'] k ∘ pa_param_mate (unop h) a := eq_refl.

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example pa_bifunctor_fmap_param {p p' : P} (h : p ~{P^op}~> p') (a : A) :
  fmap[parametrized_right_adjoint_bifunctor]
      ((h, id[a]) : (p, a) ~{P^op ∏ A}~> (p', a))
    = fmap[G p'] (id[a]) ∘ pa_param_mate (unop h) a := eq_refl.

Lemma pa_bifunctor_fmap_is_mate {p p' : P} (h : p ~{P^op}~> p') (a : A) :
  fmap[parametrized_right_adjoint_bifunctor]
      ((h, id[a]) : (p, a) ~{P^op ∏ A}~> (p', a))
    ≈ pa_param_mate (unop h) a.
Proof. simpl; rewrite fmap_id; now rewrite id_left. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example pa_bifunctor_partial_r_obj (p : P) (a : A) :
  fobj[Partial_r parametrized_right_adjoint_bifunctor p] a = G p a := eq_refl.

Example pa_bifunctor_partial_r_fmap_unfold (p : P) {a a' : A} (k : a ~> a') :
  fmap[Partial_r parametrized_right_adjoint_bifunctor p] k
    = fmap[G p] k ∘ pa_param_mate (id[p]) a := eq_refl.

Lemma pa_bifunctor_partial_r_fmap (p : P) {a a' : A} (k : a ~> a') :
  fmap[Partial_r parametrized_right_adjoint_bifunctor p] k ≈ fmap[G p] k.
Proof.
  transitivity (fmap[G p] k ∘ pa_param_mate (id[p]) a); [ reflexivity |].
  rewrite (pa_param_mate_id_at a).
  now rewrite id_right.
Qed.

(* --- UNIQUENESS: the content of Theorem 3 --- *)

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem pa_param_mate_uniq {p p' : P} (h : p' ~> p)
        (tau : G p ⟹ G p') :
  pa_square h tau → ∀ a : A, tau a ≈ pa_param_mate h a.
Proof.
  intros H a.
  exact (conj_mate_uniq (pa_adj PA p) (pa_adj PA p')
           (param_transform F h) tau H a).
Qed.

Theorem pa_assignment_unique
        (Gh : ∀ (p p' : P) (h : p' ~> p), G p ⟹ G p')
        (Hsq : ∀ (p p' : P) (h : p' ~> p), pa_square h (Gh p p' h)) :
  ∀ (p p' : P) (h : p' ~> p) (a : A),
    Gh p p' h a ≈ pa_param_mate h a.
Proof.
  intros p p' h a.
  exact (pa_param_mate_uniq h (Gh p p' h) (Hsq p p' h) a).
Qed.

(* 相关说明。 （已译） *)

Theorem pa_param_mate_universal {p p' : P} (h : p' ~> p) :
  ∃! tau : G p ⟹ G p', pa_square h tau.
Proof.
  exact (conjugate_unique_right (pa_adj PA p) (pa_adj PA p')
           (param_transform F h)).
Defined.

(* 相关说明。 （已译） *)

Corollary pa_bifunctor_fmap_determined
        (Gh : ∀ (p p' : P) (h : p' ~> p), G p ⟹ G p')
        (Hsq : ∀ (p p' : P) (h : p' ~> p), pa_square h (Gh p p' h))
        (q q' : P^op ∏ A) (hk : q ~> q') :
  fmap[parametrized_right_adjoint_bifunctor] hk
    ≈ fmap[G (fst q')] (snd hk)
        ∘ Gh (fst q) (fst q') (unop (fst hk)) (snd q).
Proof.
  destruct q as [p a], q' as [p' a'], hk as [h k]; simpl.
  apply compose_respects; [ reflexivity |].
  symmetry.
  exact (pa_assignment_unique Gh Hsq p p' (unop h) a).
Qed.

End Theorem3.

Arguments pa_param_mate {X P A F} PA {p p'} h.
Arguments pa_square {X P A F} PA {p p'} h tau.
Arguments parametrized_right_adjoint_bifunctor {X P A F} PA.

(* * ** D. The dual: bifunctor whose partial 函子 LEFT adjoints （已译） *)

(*
   本节说明伴随、函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoParamTransform.

Context {B C D : Category}.
Context (F : B ∏ C ⟶ D).

Program Definition param_transform_r {b b' : B} (m : b ~> b') :
  Partial_r F b ⟹ Partial_r F b' := {|
  transform := fun c => fmap[Partial_l F c] m
|}.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.

Example param_transform_r_component {b b' : B} (m : b ~> b') (c : C) :
  transform[param_transform_r m] c = fmap[Partial_l F c] m := eq_refl.

Example param_transform_r_component_bimap {b b' : B} (m : b ~> b') (c : C) :
  transform[param_transform_r m] c = @bimap B C D F b b' c c m id := eq_refl.

Lemma param_transform_r_respects {b b' : B} (m m' : b ~> b') :
  m ≈ m' → param_transform_r m ≈ param_transform_r m'.
Proof. intros E c; simpl; now rewrite E. Qed.

Example param_transform_r_id_component {b : B} (c : C) :
  transform[param_transform_r (id[b])] c
    = transform[@nat_id C D (Partial_r F b)] c := eq_refl.

Lemma param_transform_r_id {b : B} : param_transform_r (id[b]) ≈ nat_id.
Proof. intro c; simpl; reflexivity. Qed.

Lemma param_transform_r_comp {b b' b'' : B}
      (m : b ~> b') (m' : b' ~> b'') :
  param_transform_r (m' ∘ m)
    ≈ param_transform_r m' ∙ param_transform_r m.
Proof. intro c; simpl; apply bimap_comp_id_right. Qed.

End CoParamTransform.

Arguments param_transform_r {B C D} F {b b'} m.

(** *** D.2 The dual hypothesis *)

Section CoParametrizedAdjunction.

Context {P A X : Category}.

(*
   本节说明伴随、函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record CoParametrizedAdjunction (G : P^op ∏ A ⟶ X) := {
  pa_left : P → (X ⟶ A);
  pa_coadj (p : P) : Partial_r G p ⊣ pa_left p
}.

End CoParametrizedAdjunction.

Arguments CoParametrizedAdjunction {P A X} G.
Arguments pa_left {P A X G} _ _.
Arguments pa_coadj {P A X G} _ _.

(** *** D.3 The dual of Theorem 3 *)

Section DualTheorem3.

Context {P A X : Category}.
Context {G : P^op ∏ A ⟶ X}.
Context (CA : CoParametrizedAdjunction G).

Notation "'L'" := (pa_left CA) (only parsing).

(* As §C, every transpose names two 函子: they implicit the
 [adj] field cannot recovered 论元 type
 G (p, a) ~> x higher-order unification. （已译） *)

Definition copa_to (p : P) (a : A) (x : X) (k : G (p, a) ~> x) : a ~> L p x :=
  to (@adj X A (Partial_r G p) (pa_left CA p) (pa_coadj CA p) a x) k.

Definition copa_from (p : P) (a : A) (x : X) (g : a ~> L p x)
  : G (p, a) ~> x :=
  from (@adj X A (Partial_r G p) (pa_left CA p) (pa_coadj CA p) a x) g.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition copa_param_mate {p p' : P} (h : p ~> p') : L p ⟹ L p' :=
  conj_mate (pa_coadj CA p) (pa_coadj CA p') (param_transform_r G h).

Example copa_param_mate_is_conj_mate {p p' : P} (h : p ~> p') :
  copa_param_mate h
    = conj_mate (pa_coadj CA p) (pa_coadj CA p') (param_transform_r G h)
  := eq_refl.

(* --- naturality in each of the three variables --- *)

(* 相关说明。 （已译） *)

Lemma copa_natural_a (p : P) {a b : A} {x : X}
      (k : G (p, b) ~> x) (g : a ~> b) :
  copa_to p a x (k ∘ fmap[Partial_r G p] g) ≈ copa_to p b x k ∘ g.
Proof. exact (to_adj_nat_l (Adjunction:=pa_coadj CA p) k g). Qed.

Lemma copa_natural_x (p : P) {a : A} {x y : X}
      (f : x ~> y) (k : G (p, a) ~> x) :
  copa_to p a y (f ∘ k) ≈ fmap[L p] f ∘ copa_to p a x k.
Proof. exact (to_adj_nat_r (Adjunction:=pa_coadj CA p) f k). Qed.

(* Naturality in p, elementarily first. *)

Definition copa_square {p p' : P} (h : p ~> p')
           (sig : L p ⟹ L p') : Type :=
  ∀ (a : A) (x : X) (k : G (p, a) ~> x),
    copa_to p' a x (k ∘ fmap[Partial_l G a] h) ≈ sig x ∘ copa_to p a x k.

Example copa_square_is_Conjugate {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square h sig
    = Conjugate (pa_coadj CA p) (pa_coadj CA p')
        (param_transform_r G h) sig
  := eq_refl.

Theorem copa_natural_p {p p' : P} (h : p ~> p') :
  copa_square h (copa_param_mate h).
Proof.
  exact (conjugate_conj_mate (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h)).
Qed.

Definition copa_square_from {p p' : P} (h : p ~> p')
           (sig : L p ⟹ L p') : Type :=
  ∀ (a : A) (x : X) (g : a ~> L p x),
    copa_from p' a x (sig x ∘ g)
      ≈ copa_from p a x g ∘ fmap[Partial_l G a] h.

Example copa_square_from_is_ConjugateFrom {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square_from h sig
    = ConjugateFrom (pa_coadj CA p) (pa_coadj CA p')
        (param_transform_r G h) sig
  := eq_refl.

Theorem copa_square_iff_from {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square h sig ↔ copa_square_from h sig.
Proof.
  exact (conjugate_iff_from (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h) sig).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma copa_param_mate_respects {p p' : P} (h h' : p ~> p') :
  h ≈ h' → copa_param_mate h ≈ copa_param_mate h'.
Proof.
  intro E; unfold copa_param_mate.
  apply conj_mate_respects, param_transform_r_respects, E.
Qed.

Lemma copa_param_mate_id {p : P} : copa_param_mate (id[p]) ≈ nat_id.
Proof.
  unfold copa_param_mate.
  rewrite (conj_mate_respects (pa_coadj CA p) (pa_coadj CA p) _ nat_id
             (param_transform_r_id G)).
  apply conj_mate_id.
Qed.

Lemma copa_param_mate_comp {p p' p'' : P} (h : p ~> p') (h' : p' ~> p'') :
  copa_param_mate (h' ∘ h) ≈ copa_param_mate h' ∙ copa_param_mate h.
Proof.
  unfold copa_param_mate.
  rewrite (conj_mate_respects (pa_coadj CA p) (pa_coadj CA p'') _ _
             (param_transform_r_comp G h' h)).
  apply (conj_mate_compose (pa_coadj CA p) (pa_coadj CA p')
           (pa_coadj CA p'')).
Qed.

Lemma copa_param_mate_id_at {p : P} (x : X) :
  copa_param_mate (id[p]) x ≈ id.
Proof.
  transitivity (transform[@nat_id X A (L p)] x).
  - exact (copa_param_mate_id x).
  - apply fmap_id.
Qed.

Lemma copa_param_mate_comp_at {p p' p'' : P}
      (h : p ~> p') (h' : p' ~> p'') (x : X) :
  copa_param_mate (h' ∘ h) x
    ≈ copa_param_mate h' x ∘ copa_param_mate h x.
Proof. exact (copa_param_mate_comp h h' x). Qed.

(* --- Mac Lane's F : X × P → A.  No [op] occurs in its type. --- *)

#[local] Obligation Tactic := idtac.

Program Definition parametrized_left_adjoint_bifunctor : X ∏ P ⟶ A := {|
  fobj := fun q => L (snd q) (fst q);
  fmap := fun q q' fh =>
            fmap[L (snd q')] (fst fh)
              ∘ copa_param_mate (snd fh) (fst q)
|}.
Next Obligation.
  intros [x p] [x' p'] [f h] [f' h'] [Ef Eh]; simpl in Ef, Eh.
  apply compose_respects.
  - now apply fmap_respects.
  - exact (copa_param_mate_respects h h' Eh x).
Qed.
Next Obligation.
  intros [x p].
  etransitivity.
  { apply compose_respects; [ reflexivity |].
    exact (copa_param_mate_id_at x). }
  simpl.
  rewrite fmap_id.
  now rewrite id_left.
Qed.
Next Obligation.
  intros [x p] [x' p'] [x'' p''] [f h] [f' h'].
  etransitivity.
  { apply compose_respects.
    - apply fmap_comp.
    - exact (copa_param_mate_comp_at h' h x). }
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (naturality (copa_param_mate h) _ _ f').
Qed.

#[local] Obligation Tactic := program_simpl.

Example copa_bifunctor_obj (x : X) (p : P) :
  fobj[parametrized_left_adjoint_bifunctor] (x, p) = L p x := eq_refl.

Example copa_bifunctor_fmap {x x' : X} {p p' : P}
        (f : x ~> x') (h : p ~> p') :
  fmap[parametrized_left_adjoint_bifunctor] ((f, h) :
        (x, p) ~{X ∏ P}~> (x', p'))
    = fmap[L p'] f ∘ copa_param_mate h x := eq_refl.

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example copa_bifunctor_fmap_param {x : X} {p p' : P} (h : p ~> p') :
  fmap[parametrized_left_adjoint_bifunctor] ((id[x], h) :
        (x, p) ~{X ∏ P}~> (x, p'))
    = fmap[L p'] (id[x]) ∘ copa_param_mate h x := eq_refl.

Lemma copa_bifunctor_fmap_is_mate {x : X} {p p' : P} (h : p ~> p') :
  fmap[parametrized_left_adjoint_bifunctor] ((id[x], h) :
        (x, p) ~{X ∏ P}~> (x, p'))
    ≈ copa_param_mate h x.
Proof. simpl; rewrite fmap_id; now rewrite id_left. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example copa_bifunctor_partial_l_obj (p : P) (x : X) :
  fobj[Partial_l parametrized_left_adjoint_bifunctor p] x = L p x := eq_refl.

Example copa_bifunctor_partial_l_fmap_unfold (p : P) {x x' : X} (f : x ~> x') :
  fmap[Partial_l parametrized_left_adjoint_bifunctor p] f
    = fmap[L p] f ∘ copa_param_mate (id[p]) x := eq_refl.

Lemma copa_bifunctor_partial_l_fmap (p : P) {x x' : X} (f : x ~> x') :
  fmap[Partial_l parametrized_left_adjoint_bifunctor p] f ≈ fmap[L p] f.
Proof.
  transitivity (fmap[L p] f ∘ copa_param_mate (id[p]) x); [ reflexivity |].
  rewrite (copa_param_mate_id_at x).
  now rewrite id_right.
Qed.

(* --- UNIQUENESS, over the assignment, exactly as in §C --- *)

Theorem copa_param_mate_uniq {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square h sig → ∀ x : X, sig x ≈ copa_param_mate h x.
Proof.
  intros H x.
  exact (conj_mate_uniq (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h) sig H x).
Qed.

Theorem copa_assignment_unique
        (Fh : ∀ (p p' : P) (h : p ~> p'), L p ⟹ L p')
        (Hsq : ∀ (p p' : P) (h : p ~> p'), copa_square h (Fh p p' h)) :
  ∀ (p p' : P) (h : p ~> p') (x : X),
    Fh p p' h x ≈ copa_param_mate h x.
Proof.
  intros p p' h x.
  exact (copa_param_mate_uniq h (Fh p p' h) (Hsq p p' h) x).
Qed.

Theorem copa_param_mate_universal {p p' : P} (h : p ~> p') :
  ∃! sig : L p ⟹ L p', copa_square h sig.
Proof.
  exact (conjugate_unique_right (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h)).
Defined.

Corollary copa_bifunctor_fmap_determined
        (Fh : ∀ (p p' : P) (h : p ~> p'), L p ⟹ L p')
        (Hsq : ∀ (p p' : P) (h : p ~> p'), copa_square h (Fh p p' h))
        (q q' : X ∏ P) (fh : q ~> q') :
  fmap[parametrized_left_adjoint_bifunctor] fh
    ≈ fmap[L (snd q')] (fst fh) ∘ Fh (snd q) (snd q') (snd fh) (fst q).
Proof.
  destruct q as [x p], q' as [x' p'], fh as [f h]; simpl.
  apply compose_respects; [ reflexivity |].
  symmetry.
  exact (copa_assignment_unique Fh Hsq p p' h x).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example copa_swap_obj (p : P) (a : A) :
  fobj[Partial_l (G ◯ @Swap A (P^op)) p] a = fobj[Partial_r G p] a := eq_refl.

Example copa_swap_fmap (p : P) {a a' : A} (k : a ~> a') :
  fmap[Partial_l (G ◯ @Swap A (P^op)) p] k = fmap[Partial_r G p] k := eq_refl.

Definition copa_swap_transport (p : P)
  (Adj : Partial_r G p ⊣ pa_left CA p) :
  Partial_l (G ◯ @Swap A (P^op)) p ⊣ pa_left CA p :=
  @Build_Adjunction X A (Partial_l (G ◯ @Swap A (P^op)) p) (pa_left CA p)
    (@adj            _ _ _ _ Adj)
    (@to_adj_nat_l   _ _ _ _ Adj)
    (@to_adj_nat_r   _ _ _ _ Adj)
    (@from_adj_nat_l _ _ _ _ Adj)
    (@from_adj_nat_r _ _ _ _ Adj).

Definition copa_swap_route : ParametrizedAdjunction (G ◯ @Swap A (P^op)) :=
  @Build_ParametrizedAdjunction A (P^op) X (G ◯ @Swap A (P^op))
    (pa_left CA) (fun p => copa_swap_transport p (pa_coadj CA p)).

(* 相关说明。 （已译） *)

Example copa_swap_route_bifunctor : P ∏ X ⟶ A :=
  parametrized_right_adjoint_bifunctor copa_swap_route.

End DualTheorem3.

Arguments copa_param_mate {P A X G} CA {p p'} h.
Arguments copa_square {P A X G} CA {p p'} h sig.
Arguments parametrized_left_adjoint_bifunctor {P A X G} CA.

(* * ** E. The currying instance, 自然性 parameter （已译） *)

(*
   本节说明伴随、hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Currying.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** *** E.1 The instance *)

Example curry_prod_functor_obj (p x : C) :
  fobj[Partial_l ×(C) p] x = fobj[Prod_Functor p] x := eq_refl.

Lemma curry_prod_functor_fmap (p : C) {x y : C} (f : x ~> y) :
  fmap[Partial_l ×(C) p] f ≈ fmap[Prod_Functor p] f.
Proof. simpl; unfold first; now rewrite id_left. Qed.

Program Definition curry_pa_adj (p : C) : Partial_l ×(C) p ⊣ Exp_Functor p :=
  Build_Adjunction'
    (F:=Partial_l ×(C) p) (U:=Exp_Functor p)
    (fun x y => @adj C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p) x y) _ _.
Next Obligation.
  simpl.
  transitivity (curry (f ∘ first g)).
  - apply proper_morphism; simpl; unfold first; now rewrite id_left.
  - symmetry; apply curry_comp_l.
Qed.
Next Obligation. simpl; apply curry_comp. Qed.

Definition curry_ParametrizedAdjunction : ParametrizedAdjunction ×(C) := {|
  pa_right := Exp_Functor;
  pa_adj := curry_pa_adj
|}.

Notation "'CPA'" := curry_ParametrizedAdjunction (only parsing).

(* 相关说明。 （已译） *)

Example curry_pa_right (p : C) : pa_right CPA p = Exp_Functor p := eq_refl.

Example curry_pa_counit_is_eval (p a : C) :
  @counit C C (Partial_l ×(C) p) (Exp_Functor p) (curry_pa_adj p) a
    = @eval C _ _ p a := eq_refl.

Example curry_pa_to_is_curry (p x a : C) (k : x × p ~> a) :
  pa_to CPA p x a k = curry k := eq_refl.

Example curry_pa_from_is_uncurry (p x a : C) (g : x ~> a ^ p) :
  pa_from CPA p x a g = uncurry g := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example curry_pa_square_unfold {p p' : C} (h : p' ~> p)
        (tau : Exp_Functor p ⟹ Exp_Functor p') :
  pa_square CPA h tau
    = (∀ (x a : C) (k : x × p ~> a),
         curry (k ∘ ((id[x] ∘ exl) △ (h ∘ exr))) ≈ tau a ∘ curry k)
  := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Lemma ihom_id_action {p p' a : C} (h : p' ~> p) :
  ihom h (id[a]) ≈ curry (eval ∘ second h).
Proof. unfold ihom; apply proper_morphism; now rewrite id_left. Qed.

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example curry_param_mate_unfold {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a
    = curry (@counit C C (Partial_l ×(C) p) (Exp_Functor p)
               (curry_pa_adj p) a
             ∘ transform[param_transform ×(C) h] (a ^ p))
  := eq_refl.

Example curry_param_mate_residue {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a
    = curry (eval ∘ ((id[a ^ p] ∘ exl) △ (h ∘ exr))) := eq_refl.

Lemma curry_param_mate_is_closed_action {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a ≈ curry (eval ∘ second h).
Proof.
  simpl.
  apply proper_morphism, compose_respects; [ reflexivity |].
  unfold second; now rewrite id_left.
Qed.

Lemma curry_param_mate_is_ihom {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a ≈ ihom h (id[a]).
Proof.
  rewrite curry_param_mate_is_closed_action.
  symmetry; apply ihom_id_action.
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma curry_param_mate_is_internal_hom {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a
    ≈ @fmap _ _ (InternalHomFunctor C) (p, a) (p', a) (h, id[a]).
Proof. apply curry_param_mate_is_ihom. Qed.

Example curry_internal_hom_fmap_unfold {p p' : C} (h : p' ~> p) (a : C) :
  @fmap _ _ (InternalHomFunctor C) (p, a) (p', a) (h, id[a])
    = curry (id[a] ∘ eval ∘ second h) := eq_refl.

(* * *** E.3 Naturality currying parameter — standalone 引理 （已译） *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma curry_natural_param {x p p' a : C} (h : p' ~> p) (f : x × p ~> a) :
  curry (f ∘ second h) ≈ curry (eval ∘ second h) ∘ curry f.
Proof.
  rewrite <- ihom_id_action.
  rewrite (ihom_curry h (id[a]) f).
  apply proper_morphism.
  now rewrite id_left.
Qed.

(* The same statement, obtained Theorem 3's square instead: 这是 what
 shows right-hand side above was read off mate. （已译） *)

Lemma curry_natural_param_from_mate
      {x p p' a : C} (h : p' ~> p) (f : x × p ~> a) :
  curry (f ∘ second h) ≈ curry (eval ∘ second h) ∘ curry f.
Proof.
  transitivity (curry (f ∘ ((id[x] ∘ exl) △ (h ∘ exr)))).
  { apply proper_morphism, compose_respects; [ reflexivity |].
    unfold second; now rewrite id_left. }
  transitivity (pa_param_mate CPA h a ∘ curry f).
  { exact (pa_natural_p CPA h x a f). }
  apply compose_respects; [| reflexivity ].
  apply curry_param_mate_is_closed_action.
Qed.

(* 相关说明。 （已译） *)

Example curry_natural_param_routes_agree : Prop :=
  @curry_natural_param = @curry_natural_param_from_mate.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma uncurry_natural_param {x p p' a : C} (h : p' ~> p) (g : x ~> a ^ p) :
  uncurry (curry (eval ∘ second h) ∘ g) ≈ uncurry g ∘ second h.
Proof.
  rewrite uncurry_comp, uncurry_curry.
  rewrite <- comp_assoc.
  rewrite <- first_second.
  rewrite comp_assoc.
  now rewrite eval_first.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example curry_bifunctor_obj (p a : C) :
  fobj[parametrized_right_adjoint_bifunctor CPA] (p, a)
    = fobj[InternalHomFunctor C] (p, a) := eq_refl.

Lemma curry_bifunctor_fmap {p p' a a' : C}
      (h : p ~{C^op}~> p') (k : a ~> a') :
  fmap[parametrized_right_adjoint_bifunctor CPA]
      ((h, k) : (p, a) ~{C^op ∏ C}~> (p', a'))
    ≈ fmap[InternalHomFunctor C] ((h, k) : (p, a) ~{C^op ∏ C}~> (p', a')).
Proof.
  simpl.
  rewrite <- curry_comp.
  apply proper_morphism.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  apply compose_respects; [ reflexivity |].
  unfold second; now rewrite id_left.
Qed.

End Currying.

Arguments curry_natural_param {C _ _ x p p' a} h f.
Arguments uncurry_natural_param {C _ _ x p p' a} h g.

(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UnitWedge.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).

Notation "'G'" := (pa_right PA) (only parsing).

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition pa_unit (p : P) (x : X) : x ~> G p (F (x, p)) :=
  @unit A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) x.

Definition pa_counit (p : P) (a : A) : F (G p a, p) ~> a :=
  @counit A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) a.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition UnitIntegrand (x : X) : P^op ∏ P ⟶ X :=
  parametrized_right_adjoint_bifunctor PA
    ◯ (Id[P^op] ∏⟶ (Partial_r F x)).

Example unit_integrand_obj (x : X) (p q : P) :
  fobj[UnitIntegrand x] (p, q) = G p (F (x, q)) := eq_refl.

(* Exercise 2's answer, elementarily.  Both sides run x ~> G p (F (x, p')). *)

Lemma pa_unit_dinatural (x : X) {p p' : P} (h : p ~> p') :
  fmap[G p] (fmap[Partial_r F x] h) ∘ pa_unit p x
    ≈ pa_param_mate PA h (F (x, p')) ∘ pa_unit p' x.
Proof.
  symmetry.
  exact (conjugate_to_unit (pa_adj PA p') (pa_adj PA p)
           (param_transform F h) (pa_param_mate PA h)
           (conjugate_conj_mate (pa_adj PA p') (pa_adj PA p)
              (param_transform F h)) x).
Qed.

(*
   本节说明 Parameter 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Program Definition pa_unit_Wedge (x : X) : Wedge (UnitIntegrand x) := {|
  wedge_obj := x;
  wedge_map := fun p => pa_unit p x
|}.
Next Obligation.
  intros x p q h.
  transitivity ((fmap[G p] (fmap[Partial_r F x] h)
                   ∘ pa_param_mate PA (id[p]) (F (x, p)))
                  ∘ pa_unit p x).
  { reflexivity. }
  transitivity ((fmap[G p] (fmap[Partial_r F x] (id[q]))
                   ∘ pa_param_mate PA h (F (x, q)))
                  ∘ pa_unit q x).
  2: { reflexivity. }
  rewrite (pa_param_mate_id_at PA (F (x, p))).
  rewrite (@fmap_id P A (Partial_r F x) q).
  rewrite (@fmap_id A X (G p) (F (x, q))).
  rewrite id_right, id_left.
  apply pa_unit_dinatural.
Qed.

#[local] Obligation Tactic := program_simpl.

Example pa_unit_Wedge_obj (x : X) : @wedge_obj _ _ _ (pa_unit_Wedge x) = x
  := eq_refl.

Example pa_unit_Wedge_map (x : X) (p : P) :
  @wedge_map _ _ _ (pa_unit_Wedge x) p = pa_unit p x := eq_refl.

(* The counit's 镜像: extranaturality parameter. Both sides run
 F (G p' a, p) ~> a. （已译） *)

Lemma pa_counit_extranatural (a : A) {p p' : P} (h : p ~> p') :
  pa_counit p' a ∘ fmap[Partial_r F (G p' a)] h
    ≈ pa_counit p a ∘ fmap[Partial_l F p] (pa_param_mate PA h a).
Proof.
  exact (conjugate_to_counit (pa_adj PA p') (pa_adj PA p)
           (param_transform F h) (pa_param_mate PA h)
           (conjugate_conj_mate (pa_adj PA p') (pa_adj PA p)
              (param_transform F h)) a).
Qed.

End UnitWedge.

Arguments pa_unit {X P A F} PA p x.
Arguments pa_counit {X P A F} PA p a.
Arguments UnitIntegrand {X P A F} PA x.

(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PATransform.

Context {X P A : Category}.

Record ParametrizedAdjunctionTransform (F : X ∏ P ⟶ A) := {
  pat_right : P → (A ⟶ X);
  pat_adj (p : P) :
    PAT.Adjunction_Transform (Partial_l F p) (pat_right p)
}.

End PATransform.

Arguments ParametrizedAdjunctionTransform {X P A} F.
Arguments pat_right {X P A F} _ _.
Arguments pat_adj {X P A F} _ _.

Section PATransformPassages.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.

Definition pat_of_pa (PA : ParametrizedAdjunction F) :
  ParametrizedAdjunctionTransform F := {|
  pat_right := pa_right PA;
  pat_adj p := @Adjunction_to_Transform A X (Partial_l F p)
                 (pa_right PA p) (pa_adj PA p)
|}.

Definition pa_of_pat (PT : ParametrizedAdjunctionTransform F) :
  ParametrizedAdjunction F := {|
  pa_right := pat_right PT;
  pa_adj p := @Adjunction_from_Transform A X (Partial_l F p)
                (pat_right PT p) (pat_adj PT p)
|}.

Theorem parametrized_adjunction_iff_transform :
  ParametrizedAdjunction F ↔ ParametrizedAdjunctionTransform F.
Proof. split; [ exact pat_of_pa | exact pa_of_pat ]. Defined.

(* 相关说明。 （已译） *)

Example pat_of_pa_right (PA : ParametrizedAdjunction F) :
  pat_right (pat_of_pa PA) = pa_right PA := eq_refl.

Example pa_of_pat_right (PT : ParametrizedAdjunctionTransform F) :
  pa_right (pa_of_pat PT) = pat_right PT := eq_refl.

Example pa_pat_round_right (PA : ParametrizedAdjunction F) :
  pa_right (pa_of_pat (pat_of_pa PA)) = pa_right PA := eq_refl.

(* 相关说明。 （已译） *)

Example pat_unit_is_pa_unit (PA : ParametrizedAdjunction F) (p : P) (x : X) :
  transform[@PAT.unit A X (Partial_l F p) (pa_right PA p)
              (pat_adj (pat_of_pa PA) p)] x = pa_unit PA p x := eq_refl.

Example pat_counit_is_pa_counit
        (PA : ParametrizedAdjunction F) (p : P) (a : A) :
  transform[@PAT.counit A X (Partial_l F p) (pa_right PA p)
              (pat_adj (pat_of_pa PA) p)] a = pa_counit PA p a := eq_refl.

(* 相关说明。 （已译） *)

Lemma pa_pat_round_to (PA : ParametrizedAdjunction F)
      (p : P) (x : X) (a : A) (k : F (x, p) ~> a) :
  pa_to (pa_of_pat (pat_of_pa PA)) p x a k ≈ pa_to PA p x a k.
Proof.
  symmetry.
  exact (@to_adj_unit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x a k).
Qed.

Lemma pa_pat_round_from (PA : ParametrizedAdjunction F)
      (p : P) (x : X) (a : A) (g : x ~> pa_right PA p a) :
  pa_from (pa_of_pat (pat_of_pa PA)) p x a g ≈ pa_from PA p x a g.
Proof.
  symmetry.
  exact (@from_adj_counit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x a g).
Qed.

(* --- the two triangle identities, in parametrized form --- *)

Theorem pa_triangle_left (PA : ParametrizedAdjunction F) (p : P) (x : X) :
  pa_counit PA p (F (x, p)) ∘ fmap[Partial_l F p] (pa_unit PA p x)
    ≈ id[F (x, p)].
Proof.
  exact (@counit_fmap_unit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x).
Qed.

Theorem pa_triangle_right (PA : ParametrizedAdjunction F) (p : P) (a : A) :
  fmap[pa_right PA p] (pa_counit PA p a) ∘ pa_unit PA p (pa_right PA p a)
    ≈ id[pa_right PA p a].
Proof.
  exact (@fmap_counit_unit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) a).
Qed.

End PATransformPassages.

(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MirrorFamily.

Context {X P A : Category}.
Context (F : X ∏ P ⟶ A).

Example mirror_partial_obj (x : X) (p : P) :
  fobj[Partial_l (F ◯ @Swap P X) x] p = fobj[Partial_r F x] p := eq_refl.

Example mirror_partial_fmap (x : X) {p p' : P} (h : p ~> p') :
  fmap[Partial_l (F ◯ @Swap P X) x] h = fmap[Partial_r F x] h := eq_refl.

Definition mirror_transport (x : X) (U : A ⟶ P)
  (Adj : Partial_r F x ⊣ U) : Partial_l (F ◯ @Swap P X) x ⊣ U :=
  @Build_Adjunction A P (Partial_l (F ◯ @Swap P X) x) U
    (@adj            _ _ _ _ Adj)
    (@to_adj_nat_l   _ _ _ _ Adj)
    (@to_adj_nat_r   _ _ _ _ Adj)
    (@from_adj_nat_l _ _ _ _ Adj)
    (@from_adj_nat_r _ _ _ _ Adj).

Definition mirror_family (H : X → (A ⟶ P))
  (Adjs : ∀ x : X, Partial_r F x ⊣ H x)
  : ParametrizedAdjunction (F ◯ @Swap P X) :=
  {| pa_right := H; pa_adj := fun x => mirror_transport x (H x) (Adjs x) |}.

Example mirror_family_right (H : X → (A ⟶ P))
        (Adjs : ∀ x : X, Partial_r F x ⊣ H x) :
  pa_right (mirror_family H Adjs) = H := eq_refl.

End MirrorFamily.

Arguments mirror_transport {X P A} F x U Adj.
Arguments mirror_family {X P A} F H Adjs.

Section MutuallyRight.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA  : ParametrizedAdjunction F).
Context (MPA : ParametrizedAdjunction (F ◯ @Swap P X)).
Context (c : A).

Definition mr_left  : P^op ⟶ X :=
  Partial_l (parametrized_right_adjoint_bifunctor PA) c.
Definition mr_right : X^op ⟶ P :=
  Partial_l (parametrized_right_adjoint_bifunctor MPA) c.

Example mr_left_obj (p : P) : mr_left p = pa_right PA p c := eq_refl.
Example mr_right_obj (x : X) : mr_right x = pa_right MPA x c := eq_refl.

Example mr_left_fmap {p p' : P} (g : p' ~> p) :
  fmap[mr_left] g
    = fmap[pa_right PA p'] (id[c]) ∘ pa_param_mate PA g c := eq_refl.

Example mr_right_fmap {x x' : X} (k : x ~> x') :
  fmap[mr_right] k
    = fmap[pa_right MPA x] (id[c]) ∘ pa_param_mate MPA k c := eq_refl.

Lemma mr_left_fmap_is_mate {p p' : P} (g : p' ~> p) :
  fmap[mr_left] g ≈ pa_param_mate PA g c.
Proof.
  transitivity (fmap[pa_right PA p'] (id[c]) ∘ pa_param_mate PA g c).
  { reflexivity. }
  rewrite fmap_id; now rewrite id_left.
Qed.

Lemma mr_right_fmap_is_mate {x x' : X} (k : x ~> x') :
  fmap[mr_right] k ≈ pa_param_mate MPA k c.
Proof.
  transitivity (fmap[pa_right MPA x] (id[c]) ∘ pa_param_mate MPA k c).
  { reflexivity. }
  rewrite fmap_id; now rewrite id_left.
Qed.

(* the two [Swap] reductions 自然性 proofs consume （已译） *)

Example mr_swap_fmap_l (x : X) {p p' : P} (g : p ~> p') :
  fmap[Partial_l (F ◯ @Swap P X) x] g = fmap[Partial_r F x] g := eq_refl.

Example mr_swap_fmap_r (p : P) {x x' : X} (k : x ~> x') :
  fmap[Partial_r (F ◯ @Swap P X) p] k = fmap[Partial_l F p] k := eq_refl.

(* the bijection, 复合 two transposes （已译） *)

Definition mr_to (p : P) (x : X) (g : p ~> pa_right MPA x c)
  : x ~> pa_right PA p c :=
  pa_to PA p x c (pa_from MPA x p c g).

Definition mr_from (p : P) (x : X) (g : x ~> pa_right PA p c)
  : p ~> pa_right MPA x c :=
  pa_to MPA x p c (pa_from PA p x c g).

Lemma mr_to_respects (p : P) (x : X) :
  Proper (equiv ==> equiv) (mr_to p x).
Proof. intros g g' E; unfold mr_to, pa_to, pa_from; now rewrite E. Qed.

Lemma mr_from_respects (p : P) (x : X) :
  Proper (equiv ==> equiv) (mr_from p x).
Proof. intros g g' E; unfold mr_from, pa_to, pa_from; now rewrite E. Qed.

Lemma mr_to_from (p : P) (x : X) (g : x ~> pa_right PA p c) :
  mr_to p x (mr_from p x g) ≈ g.
Proof.
  unfold mr_to, mr_from, pa_to, pa_from.
  rewrite (@to_adj_comp_law A P (Partial_l (F ◯ @Swap P X) x)
             (pa_right MPA x) (pa_adj MPA x) p c).
  exact (@from_adj_comp_law A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x c g).
Qed.

Lemma mr_from_to (p : P) (x : X) (g : p ~> pa_right MPA x c) :
  mr_from p x (mr_to p x g) ≈ g.
Proof.
  unfold mr_to, mr_from, pa_to, pa_from.
  rewrite (@to_adj_comp_law A X (Partial_l F p)
             (pa_right PA p) (pa_adj PA p) x c).
  exact (@from_adj_comp_law A P (Partial_l (F ◯ @Swap P X) x)
           (pa_right MPA x) (pa_adj MPA x) p c g).
Qed.

#[local] Obligation Tactic := idtac.

Program Definition mr_iso (p : P) (x : X) :
  @Isomorphism Sets
    {| carrier := @hom P p (mr_right x)
     ; is_setoid := @homset P p (mr_right x) |}
    {| carrier := @hom X x (mr_left p)
     ; is_setoid := @homset X x (mr_left p) |} :=
  {| to   := {| morphism := mr_to p x |}
   ; from := {| morphism := mr_from p x |} |}.
Next Obligation. intros p x; exact (mr_to_respects p x). Qed.
Next Obligation. intros p x; exact (mr_from_respects p x). Qed.
Next Obligation. intros p x g; exact (mr_to_from p x g). Qed.
Next Obligation. intros p x g; exact (mr_from_to p x g). Qed.

#[local] Obligation Tactic := program_simpl.

(* 自然性 parameter: Mac Lane's square PA （已译） *)

Lemma mr_to_nat_a {p p' : P} {x : X} (f : p ~> mr_right x) (g : p' ~> p) :
  mr_to p' x (f ∘ g) ≈ fmap[mr_left] g ∘ mr_to p x f.
Proof.
  unfold mr_to.
  transitivity (pa_to PA p' x c
                  (pa_from MPA x p c f ∘ fmap[Partial_r F x] g)).
  { apply (@to_adj_respects A X (Partial_l F p')
             (pa_right PA p') (pa_adj PA p') x c).
    exact (@from_adj_nat_l A P (Partial_l (F ◯ @Swap P X) x)
             (pa_right MPA x) (pa_adj MPA x) p' p c f g). }
  rewrite (pa_natural_p PA g x c (pa_from MPA x p c f)).
  apply compose_respects; [| reflexivity ].
  symmetry; apply mr_left_fmap_is_mate.
Qed.

(* 自然性 other variable: Mac Lane's square MPA, read through
 inverse transposes, then PA's 自然性 x （已译） *)

Lemma mr_to_nat_x {p : P} {x x' : X} (f : p ~> mr_right x') (k : x ~> x') :
  mr_to p x (fmap[mr_right] k ∘ f) ≈ mr_to p x' f ∘ k.
Proof.
  unfold mr_to.
  transitivity (pa_to PA p x c
                  (pa_from MPA x p c (pa_param_mate MPA k c ∘ f))).
  { apply (@to_adj_respects A X (Partial_l F p)
             (pa_right PA p) (pa_adj PA p) x c).
    apply (@from_adj_respects A P (Partial_l (F ◯ @Swap P X) x)
             (pa_right MPA x) (pa_adj MPA x) p c).
    apply compose_respects; [| reflexivity ].
    apply mr_right_fmap_is_mate. }
  transitivity (pa_to PA p x c
                  (pa_from MPA x' p c f ∘ fmap[Partial_l F p] k)).
  { apply (@to_adj_respects A X (Partial_l F p)
             (pa_right PA p) (pa_adj PA p) x c).
    exact (fst (pa_square_iff_from MPA k (pa_param_mate MPA k))
             (pa_natural_p MPA k) p c f). }
  exact (pa_natural_x PA p (pa_from MPA x' p c f) k).
Qed.

(* the two inverse readings, conjugating two above the
 同构; no further 自然性 论元 run （已译） *)

Lemma mr_from_nat_a {p p' : P} {x : X} (q : x ~> mr_left p) (g : p' ~> p) :
  mr_from p' x (fmap[mr_left] g ∘ q) ≈ mr_from p x q ∘ g.
Proof.
  transitivity (mr_from p' x (mr_to p' x (mr_from p x q ∘ g))).
  - apply mr_from_respects.
    rewrite (mr_to_nat_a (mr_from p x q) g).
    apply compose_respects; [ reflexivity |].
    symmetry; apply mr_to_from.
  - apply mr_from_to.
Qed.

Lemma mr_from_nat_x {p : P} {x x' : X} (q : x' ~> mr_left p) (k : x ~> x') :
  mr_from p x (q ∘ k) ≈ fmap[mr_right] k ∘ mr_from p x' q.
Proof.
  transitivity (mr_from p x (mr_to p x (fmap[mr_right] k ∘ mr_from p x' q))).
  - apply mr_from_respects.
    rewrite (mr_to_nat_x (mr_from p x' q) k).
    apply compose_respects; [| reflexivity ].
    symmetry; apply mr_to_from.
  - apply mr_from_to.
Qed.

Definition mutually_right_adjoint : AdjointOnTheRight mr_left mr_right :=
  {| aor := mr_iso
   ; to_aor_nat_a := fun p p' x f g => mr_to_nat_a f g
   ; to_aor_nat_x := fun p x x' f k => mr_to_nat_x f k
   ; from_aor_nat_a := fun p p' x q g => mr_from_nat_a q g
   ; from_aor_nat_x := fun p x x' q k => mr_from_nat_x q k |}.

Example mr_aor_is_iso (p : P) (x : X) :
  @aor P X mr_left mr_right mutually_right_adjoint p x = mr_iso p x
  := eq_refl.

Example mr_aor_to_is_mr_to (p : P) (x : X) (g : p ~> mr_right x) :
  to (@aor P X mr_left mr_right mutually_right_adjoint p x) g
    = mr_to p x g := eq_refl.

Example mr_aor_from_is_mr_from (p : P) (x : X) (g : x ~> mr_left p) :
  from (@aor P X mr_left mr_right mutually_right_adjoint p x) g
    = mr_from p x g := eq_refl.

End MutuallyRight.

Arguments mr_left {X P A F} PA c.
Arguments mr_right {X P A F} MPA c.
Arguments mr_to {X P A F} PA MPA c p x g.
Arguments mr_from {X P A F} PA MPA c p x g.
Arguments mutually_right_adjoint {X P A F} PA MPA c.
