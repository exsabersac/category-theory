Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The left unitor [1 □ C ≅ C] *)

(* Forward action as separately functorial data: [1]-steps die, [C]-steps
   pass through. *)
Program Definition Funny_unit_left_sep {C : Category} :
  SepFunctorial (C:=1) (D:=C) (E:=C) (fun _ c => c) := {|
  sf_lmap := fun _ _ _ _ => id;
  sf_rmap := fun _ _ _ g => g
|}.

Definition Funny_unit_left_to {C : Category} : (1 □ C) ⟶ C :=
  FunnyUP Funny_unit_left_sep.

(* The injection at lone 对象 [1] inverse. （已译） *)
Definition Funny_unit_left_from {C : Category} : C ⟶ (1 □ C) :=
  FunnyR (C:=1) ttt.

(*
   本节说明 Unitors 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition funny_unit_left_obj {C : Category} (u : poly_unit) (d : C) :
  @eq (obj[1 □ C]) (ttt, d) (u, d) :=
  match u as p return (@eq (obj[1 □ C]) (ttt, d) (p, d)) with
  | ttt => eq_refl
  end.

Lemma funny_unit_left_to_from {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid C C)
    (Funny_unit_left_to ◯ Funny_unit_left_from) Id.
Proof.
  apply (Functor_StrictEq_intro
           (Funny_unit_left_to ◯ Funny_unit_left_from) Id
           (fun _ => eq_refl)).
  intros c c' f.
  (* id ∘ f ≈ f, up to the (trivial) transports *)
  exact (id_left f).
Qed.

(*
   本节说明 Unitors 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma funny_unit_left_from_to {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (1 □ C) (1 □ C))
    (Funny_unit_left_from ◯ Funny_unit_left_to) Id.
Proof.
  apply (Funny_strict_eq (Funny_unit_left_from ◯ Funny_unit_left_to) Id
           funny_unit_left_obj).
  - intros u u' f d.
    destruct u, u', f.
    (* feq (rstep (id ∘ id)) (lstep ttt); note ttt ≡ id[1] *)
    exact (@feq_trans _1 C ttt d ttt d
             (@rstep _1 C ttt d d (@compose C d d d (@id C d) (@id C d)))
             (@rstep _1 C ttt d d (@id C d))
             (@lstep _1 C ttt ttt d (@id _1 ttt))
             (@feq_consR _1 C ttt d d
                (@compose C d d d (@id C d) (@id C d)) (@id C d) ttt d
                (@fnil _1 C ttt d) (@fnil _1 C ttt d)
                (@id_left C d d (@id C d))
                (@feq_refl _1 C ttt d ttt d (@fnil _1 C ttt d)))
             (@feq_trans _1 C ttt d ttt d
                (@rstep _1 C ttt d d (@id C d))
                (@fnil _1 C ttt d)
                (@lstep _1 C ttt ttt d (@id _1 ttt))
                (@feq_idR _1 C ttt d ttt d (@fnil _1 C ttt d))
                (@feq_sym _1 C ttt d ttt d
                   (@lstep _1 C ttt ttt d (@id _1 ttt))
                   (@fnil _1 C ttt d)
                   (@feq_idL _1 C ttt d ttt d (@fnil _1 C ttt d))))).
  - intros u d d' g.
    destruct u.
    (* feq (rstep (id ∘ g)) (rstep g) *)
    exact (@feq_consR _1 C ttt d d'
             (@compose C d d' d' (@id C d') g) g ttt d'
             (@fnil _1 C ttt d') (@fnil _1 C ttt d')
             (@id_left C d d' g)
             (@feq_refl _1 C ttt d' ttt d' (@fnil _1 C ttt d'))).
Qed.

Definition Funny_unit_left {C : Category} : (1 □ C) ≅[StrictCat] C :=
  @Build_Isomorphism StrictCat (1 □ C) C
    Funny_unit_left_to Funny_unit_left_from
    funny_unit_left_to_from funny_unit_left_from_to.

(** ** The right unitor [C □ 1 ≅ C] *)

(* Forward action: [C]-steps pass through, [1]-steps die. *)
Program Definition Funny_unit_right_sep {C : Category} :
  SepFunctorial (C:=C) (D:=1) (E:=C) (fun c _ => c) := {|
  sf_lmap := fun _ _ f _ => f;
  sf_rmap := fun _ _ _ _ => id
|}.

Definition Funny_unit_right_to {C : Category} : (C □ 1) ⟶ C :=
  FunnyUP Funny_unit_right_sep.

Definition Funny_unit_right_from {C : Category} : C ⟶ (C □ 1) :=
  FunnyL (D:=1) ttt.

Definition funny_unit_right_obj {C : Category} (c : C) (u : poly_unit) :
  @eq (obj[C □ 1]) (c, ttt) (c, u) :=
  match u as p return (@eq (obj[C □ 1]) (c, ttt) (c, p)) with
  | ttt => eq_refl
  end.

Lemma funny_unit_right_to_from {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid C C)
    (Funny_unit_right_to ◯ Funny_unit_right_from) Id.
Proof.
  apply (Functor_StrictEq_intro
           (Funny_unit_right_to ◯ Funny_unit_right_from) Id
           (fun _ => eq_refl)).
  intros c c' f.
  (* id ∘ f ≈ f, up to the (trivial) transports *)
  exact (id_left f).
Qed.

Lemma funny_unit_right_from_to {C : Category} :
  @equiv _ (@Functor_StrictEq_Setoid (C □ 1) (C □ 1))
    (Funny_unit_right_from ◯ Funny_unit_right_to) Id.
Proof.
  apply (Funny_strict_eq (Funny_unit_right_from ◯ Funny_unit_right_to) Id
           funny_unit_right_obj).
  - intros c c' f u.
    destruct u.
    (* feq (lstep (id ∘ f)) (lstep f) *)
    exact (@feq_consL C _1 c c' ttt
             (@compose C c c' c' (@id C c') f) f c' ttt
             (@fnil C _1 c' ttt) (@fnil C _1 c' ttt)
             (@id_left C c c' f)
             (@feq_refl C _1 c' ttt c' ttt (@fnil C _1 c' ttt))).
  - intros c u u' g.
    destruct u, u', g.
    (* feq (lstep (id ∘ id)) (rstep ttt); note ttt ≡ id[1] *)
    exact (@feq_trans C _1 c ttt c ttt
             (@lstep C _1 c c ttt (@compose C c c c (@id C c) (@id C c)))
             (@lstep C _1 c c ttt (@id C c))
             (@rstep C _1 c ttt ttt (@id _1 ttt))
             (@feq_consL C _1 c c ttt
                (@compose C c c c (@id C c) (@id C c)) (@id C c) c ttt
                (@fnil C _1 c ttt) (@fnil C _1 c ttt)
                (@id_left C c c (@id C c))
                (@feq_refl C _1 c ttt c ttt (@fnil C _1 c ttt)))
             (@feq_trans C _1 c ttt c ttt
                (@lstep C _1 c c ttt (@id C c))
                (@fnil C _1 c ttt)
                (@rstep C _1 c ttt ttt (@id _1 ttt))
                (@feq_idL C _1 c ttt c ttt (@fnil C _1 c ttt))
                (@feq_sym C _1 c ttt c ttt
                   (@rstep C _1 c ttt ttt (@id _1 ttt))
                   (@fnil C _1 c ttt)
                   (@feq_idR C _1 c ttt c ttt (@fnil C _1 c ttt))))).
Qed.

Definition Funny_unit_right {C : Category} : (C □ 1) ≅[StrictCat] C :=
  @Build_Isomorphism StrictCat (C □ 1) C
    Funny_unit_right_to Funny_unit_right_from
    funny_unit_right_to_from funny_unit_right_from_to.

(* * ** The unitors weak [Cat]

 Strict 同构 refines 同构-up-to-natural-同构, so
 comparison 函子 transfers both unitors [Cat] free. （已译） *)

Definition Funny_unit_left_cat {C : Category} : (1 □ C) ≅[Cat] C :=
  fobj_iso StrictCat_to_Cat (1 □ C) C Funny_unit_left.

Definition Funny_unit_right_cat {C : Category} : (C □ 1) ≅[Cat] C :=
  fobj_iso StrictCat_to_Cat (C □ 1) C Funny_unit_right.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Funny_unit_left_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid (1 □ x) y)
    (g ◯ Funny_unit_left_to) (Funny_unit_left_to ◯ FunnyBimap Id[1] g).
Proof.
  apply (Funny_strict_eq (g ◯ Funny_unit_left_to)
           (Funny_unit_left_to ◯ FunnyBimap Id[1] g) (fun _ _ => eq_refl)).
  - intros u u' f d; unfold transport_r; simpl.
    (* fmap[g] (id ∘ id) ≈ id ∘ id *)
    cat.
  - intros u c c' h; unfold transport_r; simpl.
    (* fmap[g] (id ∘ h) ≈ id ∘ fmap[g] h *)
    cat.
Qed.

Lemma Funny_unit_left_from_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid x (1 □ y))
    (FunnyBimap Id[1] g ◯ Funny_unit_left_from) (Funny_unit_left_from ◯ g).
Proof.
  apply (Functor_StrictEq_intro
           (FunnyBimap Id[1] g ◯ Funny_unit_left_from)
           (Funny_unit_left_from ◯ g) (fun _ => eq_refl)).
  intros c c' h.
  (* rstep (fmap[g] h) on both sides, definitionally *)
  reflexivity.
Qed.

Lemma Funny_unit_right_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid (x □ 1) y)
    (g ◯ Funny_unit_right_to) (Funny_unit_right_to ◯ FunnyBimap g Id[1]).
Proof.
  apply (Funny_strict_eq (g ◯ Funny_unit_right_to)
           (Funny_unit_right_to ◯ FunnyBimap g Id[1]) (fun _ _ => eq_refl)).
  - intros c c' f u; unfold transport_r; simpl.
    (* fmap[g] (id ∘ f) ≈ id ∘ fmap[g] f *)
    cat.
  - intros c u u' f; unfold transport_r; simpl.
    (* fmap[g] (id ∘ id) ≈ id ∘ id *)
    cat.
Qed.

Lemma Funny_unit_right_from_natural {x y : Category} (g : x ⟶ y) :
  @equiv _ (@Functor_StrictEq_Setoid x (y □ 1))
    (FunnyBimap g Id[1] ◯ Funny_unit_right_from) (Funny_unit_right_from ◯ g).
Proof.
  apply (Functor_StrictEq_intro
           (FunnyBimap g Id[1] ◯ Funny_unit_right_from)
           (Funny_unit_right_from ◯ g) (fun _ => eq_refl)).
  intros c c' h.
  (* lstep (fmap[g] h) on both sides, definitionally *)
  reflexivity.
Qed.
