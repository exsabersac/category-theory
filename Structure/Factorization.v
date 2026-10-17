Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Orthogonality.
Require Import Category.Instance.Fact.

Generalizable All Variables.

(*
   nLab:      https://ncatlab.org/nlab/show/orthogonal+factorization+system
   Wikipedia: https://en.wikipedia.org/wiki/Factorization_system

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:      https://ncatlab.org/nlab/show/weak+factorization+system
   Wikipedia: https://en.wikipedia.org/wiki/Lifting_property

   本节说明 Factorization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* An (E, M)-factorization f : x ~> y: middle 对象 [fact_mid], a
 left leg [fact_e] belonging E, right leg [fact_m] belonging to
 M, [fact_m ∘ fact_e ≈ f]. （已译） *)
Record Factorization {C : Category} {x y : C} (f : x ~> y)
  (E M : MorphismClass C) := {
  fact_mid  : C;
  fact_e    : x ~> fact_mid;
  fact_e_in : E _ _ fact_e;
  fact_m    : fact_mid ~> y;
  fact_m_in : M _ _ fact_m;
  fact_comm : fact_m ∘ fact_e ≈ f
}.

Arguments fact_mid  {C x y f E M} _.
Arguments fact_e    {C x y f E M} _.
Arguments fact_e_in {C x y f E M} _.
Arguments fact_m    {C x y f E M} _.
Arguments fact_m_in {C x y f E M} _.
Arguments fact_comm {C x y f E M} _.

(* An orthogonal factorization system: two morphism classes closed under ≈,
   a factorization of every morphism, and orthogonality of E against M. *)
Class OFS {C : Category} (E M : MorphismClass C) := {
  ofs_e_respects {x y} (f g : x ~> y) : f ≈ g → E x y f → E x y g;
  ofs_m_respects {x y} (f g : x ~> y) : f ≈ g → M x y f → M x y g;
  ofs_factor {x y} (f : x ~> y) : Factorization f E M;
  ofs_orth {a b x y} (e : a ~> b) (m : x ~> y) :
    E a b e → M x y m → e ⫫ m
}.

Section FactorizationSystem.

Context {C : Category}.
Context {E M : MorphismClass C}.

(* Two factorizations one 态射 bound same 交换方块: the
 two composites both ≈ f, hence ≈ each other. （已译） *)
Lemma factorization_square {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘ fact_e F1.
Proof.
  rewrite (fact_comm F2).
  rewrite (fact_comm F1).
  reflexivity.
Qed.

(* The comparison 态射 between two factorizations f: unique
 diagonal filler square [fact_m F2 ∘ fact_e F2 ≈ fact_m F1 ∘
 fact_e F1], obtained (fact_e F1) ⫫ (fact_m F2). （已译） *)
Lemma factorization_lift {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  ∃ d : fact_mid F1 ~> fact_mid F2,
    (d ∘ fact_e F1 ≈ fact_e F2) ∧ (fact_m F2 ∘ d ≈ fact_m F1).
Proof.
  pose proof (ofs_orth (fact_e F1) (fact_m F2)
                (fact_e_in F1) (fact_m_in F2)) as Ho.
  pose proof (@ortho_lift _ _ _ _ _ (fact_e F1) (fact_m F2) Ho
                (fact_e F2) (fact_m F1) (factorization_square F1 F2)) as U.
  exact (unique_obj U; unique_property U).
Qed.

(* Any two comparison 态射 between same pair factorizations
 agree: both fill same orthogonality square, whose filler unique. （已译） *)
Lemma factorization_lift_unique {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) (d d' : fact_mid F1 ~> fact_mid F2)
  (de : d ∘ fact_e F1 ≈ fact_e F2) (md : fact_m F2 ∘ d ≈ fact_m F1)
  (d'e : d' ∘ fact_e F1 ≈ fact_e F2) (md' : fact_m F2 ∘ d' ≈ fact_m F1) :
  d ≈ d'.
Proof.
  pose proof (ofs_orth (fact_e F1) (fact_m F2)
                (fact_e_in F1) (fact_m_in F2)) as Ho.
  pose proof (@ortho_lift _ _ _ _ _ (fact_e F1) (fact_m F2) Ho
                (fact_e F2) (fact_m F1) (factorization_square F1 F2)) as U.
  assert (H1 : unique_obj U ≈ d). {
    apply (uniqueness U).
    split.
    - exact de.
    - exact md.
  }
  assert (H2 : unique_obj U ≈ d'). {
    apply (uniqueness U).
    split.
    - exact d'e.
    - exact md'.
  }
  rewrite <- H1.
  exact H2.
Qed.

(*
   本节说明 Factorization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem factorization_unique {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  ∃ i : fact_mid F1 ≅ fact_mid F2,
    (to i ∘ fact_e F1 ≈ fact_e F2) ∧ (fact_m F2 ∘ to i ≈ fact_m F1).
Proof.
  destruct (factorization_lift F1 F2) as [d [de md]].
  destruct (factorization_lift F2 F1) as [d' [d'e md']].
  assert (dd' : d ∘ d' ≈ id). {
    apply (factorization_lift_unique F2 F2 (d ∘ d') id).
    - rewrite <- comp_assoc.
      rewrite d'e.
      exact de.
    - rewrite comp_assoc.
      rewrite md.
      exact md'.
    - cat.
    - cat.
  }
  assert (d'd : d' ∘ d ≈ id). {
    apply (factorization_lift_unique F1 F1 (d' ∘ d) id).
    - rewrite <- comp_assoc.
      rewrite de.
      exact d'e.
    - rewrite comp_assoc.
      rewrite md'.
      exact md.
    - cat.
    - cat.
  }
  exists {| to := d; from := d'; iso_to_from := dd'; iso_from_to := d'd |}.
  split.
  - exact de.
  - exact md.
Qed.

(*
   本节说明 Factorization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary ofs_m_orth {O : OFS E M} {x y : C} (m : x ~> y) :
  M x y m → ∀ (a b : C) (e : a ~> b), E a b e → e ⫫ m.
Proof.
  intros Hm a b e He.
  exact (ofs_orth e m He Hm).
Qed.

(* Dually, every E-morphism is left orthogonal to every M-morphism. *)
Corollary ofs_e_orth {O : OFS E M} {x y : C} (e : x ~> y) :
  E x y e → ∀ (a b : C) (m : a ~> b), M a b m → e ⫫ m.
Proof.
  intros He a b m Hm.
  exact (ofs_orth e m He Hm).
Qed.

(*
   本节说明同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem ofs_m_char {O : OFS E M}
  (Mclosed : ∀ (x y z : C) (i : x ~> y) (m : y ~> z),
      IsIsomorphism i → M y z m → M x z (m ∘ i))
  {x y : C} (m : x ~> y) :
  (∀ (a b : C) (e : a ~> b), E a b e → e ⫫ m) → M x y m.
Proof.
  intros H.
  destruct (ofs_factor m) as [mid e' He' m' Hm' comm'].
  simpl in *.
  (* Lift the square m ∘ id ≈ m' ∘ e' through e' ⫫ m. *)
  assert (comm1 : m ∘ id ≈ m' ∘ e'). {
    rewrite id_right.
    symmetry.
    exact comm'.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m (H _ _ e' He') id m' comm1) as U.
  destruct (unique_property U) as [dE mD].
  (* dE : unique_obj U ∘ e' ≈ id,  mD : m ∘ unique_obj U ≈ m'. *)
  pose proof (ofs_orth e' m' He' Hm') as Hself.
  assert (selfcomm : m' ∘ e' ≈ m' ∘ e'). {
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m' Hself e' m' selfcomm) as Uself.
  (* 相关说明。 （已译） *)
  assert (Hu1 : unique_obj Uself ≈ e' ∘ unique_obj U). {
    apply (uniqueness Uself).
    split.
    - rewrite <- comp_assoc.
      rewrite dE.
      cat.
    - rewrite comp_assoc.
      rewrite comm'.
      exact mD.
  }
  assert (Hu2 : unique_obj Uself ≈ id). {
    apply (uniqueness Uself).
    split.
    - cat.
    - cat.
  }
  assert (ed : e' ∘ unique_obj U ≈ id). {
    rewrite <- Hu1.
    exact Hu2.
  }
  assert (Hiso : IsIsomorphism e'). {
    exact {| two_sided_inverse := unique_obj U;
             is_right_inverse  := ed;
             is_left_inverse   := dE |}.
  }
  apply (ofs_m_respects (m' ∘ e') m comm').
  exact (Mclosed _ _ _ e' m' Hiso Hm').
Qed.

(* Characterization of E, hypothesis form, dual to [ofs_m_char]: e belongs
   to E as soon as e ⫫ m for every m ∈ M, granted that E is closed under
   postcomposition with isomorphisms ([Eclosed]). *)
Theorem ofs_e_char {O : OFS E M}
  (Eclosed : ∀ (x y z : C) (e : x ~> y) (i : y ~> z),
      IsIsomorphism i → E x y e → E x z (i ∘ e))
  {x y : C} (e : x ~> y) :
  (∀ (a b : C) (m : a ~> b), M a b m → e ⫫ m) → E x y e.
Proof.
  intros H.
  destruct (ofs_factor e) as [mid e' He' m' Hm' comm'].
  simpl in *.
  (* Lift the square m' ∘ e' ≈ id ∘ e through e ⫫ m'. *)
  assert (comm1 : m' ∘ e' ≈ id ∘ e). {
    rewrite id_left.
    exact comm'.
  }
  pose proof (@ortho_lift _ _ _ _ _ e m' (H _ _ m' Hm') e' id comm1) as U.
  destruct (unique_property U) as [dE mD].
  (* dE : unique_obj U ∘ e ≈ e',  mD : m' ∘ unique_obj U ≈ id. *)
  pose proof (ofs_orth e' m' He' Hm') as Hself.
  assert (selfcomm : m' ∘ e' ≈ m' ∘ e'). {
    reflexivity.
  }
  pose proof (@ortho_lift _ _ _ _ _ e' m' Hself e' m' selfcomm) as Uself.
  (* 相关说明。 （已译） *)
  assert (Hu1 : unique_obj Uself ≈ unique_obj U ∘ m'). {
    apply (uniqueness Uself).
    split.
    - rewrite <- comp_assoc.
      rewrite comm'.
      exact dE.
    - rewrite comp_assoc.
      rewrite mD.
      cat.
  }
  assert (Hu2 : unique_obj Uself ≈ id). {
    apply (uniqueness Uself).
    split.
    - cat.
    - cat.
  }
  assert (dm : unique_obj U ∘ m' ≈ id). {
    rewrite <- Hu1.
    exact Hu2.
  }
  assert (Hiso : IsIsomorphism m'). {
    exact {| two_sided_inverse := unique_obj U;
             is_right_inverse  := mD;
             is_left_inverse   := dm |}.
  }
  apply (ofs_e_respects (m' ∘ e') e comm').
  exact (Eclosed _ _ _ e' m' Hiso He').
Qed.

(*
   本节说明 Factorization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition factorization_to_fact {x y : C} (f : x ~> y)
  (F1 : Factorization f E M) : Fact f.
Proof.
  refine (fact_mid F1; (fact_e F1; (fact_m F1; _))).
  symmetry.
  exact (fact_comm F1).
Defined.

(*
   本节说明 Factorization 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem factorization_fact_iso {O : OFS E M} {x y : C} {f : x ~> y}
  (F1 F2 : Factorization f E M) :
  factorization_to_fact f F1 ≅[Fact f] factorization_to_fact f F2.
Proof.
  destruct (factorization_lift F1 F2) as [d [de md]].
  destruct (factorization_lift F2 F1) as [d' [d'e md']].
  assert (dd' : d ∘ d' ≈ id). {
    apply (factorization_lift_unique F2 F2 (d ∘ d') id).
    - rewrite <- comp_assoc.
      rewrite d'e.
      exact de.
    - rewrite comp_assoc.
      rewrite md.
      exact md'.
    - cat.
    - cat.
  }
  assert (d'd : d' ∘ d ≈ id). {
    apply (factorization_lift_unique F1 F1 (d' ∘ d) id).
    - rewrite <- comp_assoc.
      rewrite de.
      exact d'e.
    - rewrite comp_assoc.
      rewrite md'.
      exact md.
    - cat.
    - cat.
  }
  unshelve refine {| to := _; from := _ |}.
  - refine (d; _).
    split.
    + exact de.
    + exact md.
  - refine (d'; _).
    split.
    + exact d'e.
    + exact md'.
  - exact dd'.
  - exact d'd.
Qed.

End FactorizationSystem.
