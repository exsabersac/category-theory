Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Morphisms.

Context {C : Category}.

Open Scope type_scope.

(* 特殊态射类及其关系：幂等元与对合、截面与收缩（分裂 mono/epi）、满射与单射，
   以及它们之间的蕴含。全程定律使用 hom-setoid 等价 `≈` 而非 Coq 的 `=`。 *)

(* nLab: https://ncatlab.org/nlab/show/idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Idempotence

   An endomorphism `f : x ~> x` is idempotent when `f ∘ f ≈ f` (idem). *)

Class Idempotent `(f : x ~> x) := {
  idem : f ∘ f ≈ f             (* idempotency law: f ∘ f ≈ f *)
}.

(* nLab: https://ncatlab.org/nlab/show/involution
   Wikipedia: https://en.wikipedia.org/wiki/Involution_(mathematics)

   An endomorphism `f : x ~> x` is involutive when it is its own inverse,
   `f ∘ f ≈ id` (invol). *)

Class Involutive `(f : x ~> x) := {
  invol : f ∘ f ≈ id           (* involution law: f ∘ f ≈ id *)
}.

(* For an involution g, precomposition by g is its own inverse, so it may be
   moved across an equation: f ≈ g ∘ h  iff  g ∘ f ≈ h. *)
Lemma flip_invol {x y} (f h : x ~> y) (g : y ~> y) `{@Involutive _ g} :
  f ≈ g ∘ h ↔ g ∘ f ≈ h.
Proof.
  split; intros.
  - rewrite X, comp_assoc, invol; cat.
  - rewrite <- X, comp_assoc, invol; cat.
Qed.

(*
 nLab: https://ncatlab.org/nlab/show/split+monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   本文件给出态射类/性质相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Section `(f : x ~> y) := {
  section : y ~> x;               (* the retraction (left inverse) of f *)
  section_comp : section ∘ f ≈ id (* left inverse law: section ∘ f ≈ id *)
}.

(*
   nLab: https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Retraction `(f : x ~> y) := {
  retract : y ~> x;               (* the section (right inverse) of f *)
  retract_comp : f ∘ retract ≈ id (* right inverse law: f ∘ retract ≈ id *)
}.

(*
   nLab: https://ncatlab.org/nlab/show/split+idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class SplitIdempotent {x y : C} := {
  split_idem_retract := y;                  (* the splitting object y *)

  split_idem    : x ~> x;                   (* the idempotent on x *)
  split_idem_r  : x ~> split_idem_retract;  (* retraction x ~> y *)
  split_idem_s  : split_idem_retract ~> x;  (* section y ~> x *)
  split_idem_sr : split_idem_s ∘ split_idem_r ≈ split_idem;
                                            (* s ∘ r ≈ split_idem *)
  split_idem_rs : split_idem_r ∘ split_idem_s ≈ id
                                            (* r ∘ s ≈ id on y *)
}.

(* nLab: https://ncatlab.org/nlab/show/epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   `Epic f` witnesses that `f : x ~> y` is an epimorphism: f is
   right-cancellable, `g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2` for all parallel
   `g1 g2 : y ~> z` (epic). This is exactly `Monic f` in `C^op`. *)

Class Epic {x y} (f : x ~> y) := {
  epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2
                                  (* right cancellation: g1∘f ≈ g2∘f → g1 ≈ g2 *)
}.

(* nLab: https://ncatlab.org/nlab/show/monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Monomorphism

   `Monic f` witnesses that `f : x ~> y` is a monomorphism: f is
   left-cancellable, `f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2` for all parallel
   `g1 g2 : z ~> x` (monic). This is exactly `Epic f` in `C^op`. *)

Class Monic {x y} (f : x ~> y) := {
  monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2
                                  (* left cancellation: f∘g1 ≈ f∘g2 → g1 ≈ g2 *)
}.

(* A bimorphism both epic monic; split epi retraction a
 split mono section (the converse 蕴含 above hold via
 retractions_are_epic sections_are_monic). （已译） *)

Definition Bimorphic `(f : x ~> y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : x ~> y) := Retraction f.
Definition SplitMono `(f : x ~> y) := Section f.

Corollary id_idem : ∀ x, Idempotent (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_invol : ∀ x, Involutive (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_monic : ∀ x, Monic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_left in X.
  assumption.
Qed.

Corollary id_epic : ∀ x, Epic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_right in X.
  assumption.
Qed.

#[local] Hint Unfold Bimorphic : core.
#[local] Hint Unfold SplitEpi : core.
#[local] Hint Unfold SplitMono : core.

Section Lemmas.

Variables x y : C.
Variable f : x ~> y.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

(* Every split epimorphism is an epimorphism. *)
Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_right.
  transitivity (g2 ∘ (f ∘ retract0));
    [ now apply compose_respects |];
  transitivity (g1 ∘ (f ∘ retract0));
    [| now apply compose_respects ].
  reassociate_right.
Qed.

(* Every split monomorphism is a monomorphism. *)
Lemma sections_are_monic : Section f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_left.
  symmetry.
  rewrite <- id_left.
  transitivity ((section0 ∘ f) ∘ g2);
    [ now apply compose_respects |];
  transitivity ((section0 ∘ f) ∘ g1);
    [| now apply compose_respects ].
  reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

(* Epimorphisms are closed under composition. *)
Definition epi_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic f → Epic g → Epic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply epic0, epic1.
  reassociate_left.
Qed.

(*
   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition epic_cancel {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic (f ∘ g) → Epic f.
Proof.
  intro H; constructor; intros w g1 g2 Hgg.
  apply (@epic x z (f ∘ g) H w g1 g2).
  rewrite !comp_assoc.
  now rewrite Hgg.
Qed.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition monic_cancel {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic (f ∘ g) → Monic g.
Proof.
  intro H; constructor; intros w g1 g2 Hgg.
  apply (@monic x z (f ∘ g) H w g1 g2).
  rewrite <- !comp_assoc.
  now rewrite Hgg.
Qed.

(* Monomorphisms are closed under composition. *)
Definition monic_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic f → Monic g → Monic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply monic1, monic0.
  reassociate_right.
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/split+epimorphism
   nLab: https://ncatlab.org/nlab/show/idempotent

   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma split_pair_idempotent {x y : C} (g : x ~> y) (h : y ~> x) :
  g ∘ h ≈ id → Idempotent (h ∘ g).
Proof.
  intro Hgh.
  constructor.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g h g).
  rewrite Hgh, id_left.
  reflexivity.
Qed.

(* Idempotence transports along `≈`, the hom-setoid equivalence. *)
Lemma idempotent_respects {x : C} (f g : x ~> x) :
  f ≈ g → Idempotent f → Idempotent g.
Proof.
  intros Hfg [Hf].
  constructor.
  rewrite <- Hfg.
  exact Hf.
Qed.

(*
   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma split_idem_Idempotent {x y : C} (S : @SplitIdempotent x y) :
  Idempotent (@split_idem x y S).
Proof.
  apply (idempotent_respects (@split_idem_s x y S ∘ @split_idem_r x y S)).
  - exact (@split_idem_sr x y S).
  - exact (split_pair_idempotent _ _ (@split_idem_rs x y S)).
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Von_Neumann_regular_ring

   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition RegularMorphism `(f : x ~> y) := ∃ g : y ~> x, f ∘ g ∘ f ≈ f.

(* 相关说明。 （已译） *)
Definition regular_of_section `(f : x ~> y) : Section f → RegularMorphism f.
Proof.
  intros [s Hs].
  exists s.
  rewrite <- comp_assoc, Hs.
  apply id_right.
Defined.

(* An arrow with a RIGHT inverse is regular: dually, (f ∘ r) ∘ f ≈ id ∘ f. *)
Definition regular_of_retraction `(f : x ~> y) :
  Retraction f → RegularMorphism f.
Proof.
  intros [r Hr].
  exists r.
  rewrite Hr.
  apply id_left.
Defined.

(*
   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma regular_composites_idempotent {x y : C} (f : x ~> y) (g : y ~> x) :
  f ∘ g ∘ f ≈ f → Idempotent (f ∘ g) ∧ Idempotent (g ∘ f).
Proof.
  intro Hg.
  split; constructor.
  - rewrite (comp_assoc (f ∘ g) f g), Hg.
    reflexivity.
  - rewrite <- comp_assoc, (comp_assoc f g f), Hg.
    reflexivity.
Qed.

(*
   本节说明 Morphisms 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition regular_epic_retraction `(f : x ~> y) :
  RegularMorphism f → Epic f → Retraction f.
Proof.
  intros [g Hg] E.
  exists g.
  apply (@epic x y f E y (f ∘ g) id).
  rewrite Hg.
  symmetry.
  apply id_left.
Defined.

(* Dually, a regular MONO splits: cancel f on the left of
   f ∘ (g ∘ f) ≈ f ∘ id. *)
Definition regular_monic_section `(f : x ~> y) :
  RegularMorphism f → Monic f → Section f.
Proof.
  intros [g Hg] M.
  exists g.
  apply (@monic x y f M x (g ∘ f) id).
  rewrite comp_assoc, Hg.
  symmetry.
  apply id_right.
Defined.

End Morphisms.

#[export] Hint Unfold Bimorphic : core.
#[export] Hint Unfold SplitEpi : core.
#[export] Hint Unfold SplitMono : core.

(* 相关说明。 （已译） *)
Definition flip_Section {C : Category} `(f : x ~> y)
           (s : @Section C x y f) : @Retraction C y x section.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.

(* 相关说明。 （已译） *)
Definition flip_Retraction {C : Category} `(f : x ~> y)
           (s : @Retraction C x y f) : @Section C y x retract.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.
