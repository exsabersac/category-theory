Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Wikipedia: none-exists (no category-theoretic article; the page title

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Corelation.

Context {C : Category}.
Context `{@Cocartesian C}.

(*
   本节说明 Corelation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record CorelationArrow (X Y : C) : Type := {
  corelation_cospan : CospanArrow X Y;
  corelation_copairing_epic :
    Epic (cospan_in1 corelation_cospan ▽ cospan_in2 corelation_cospan)
}.

Arguments corelation_cospan {X Y} _.
Arguments corelation_copairing_epic {X Y} _.

(** Coercion: a corelation IS a cospan. *)
Coercion corelation_cospan : CorelationArrow >-> CospanArrow.

(** 本节：Two corelations equivalent iff underlying cospans are. （已译） *)
Definition corelation_equiv {X Y : C} (f g : CorelationArrow X Y) : Type :=
  cospan_equiv (corelation_cospan f) (corelation_cospan g).

#[export] Program Instance CorelationArrow_Setoid {X Y : C} :
  Setoid (CorelationArrow X Y) := {|
  equiv := fun f g => corelation_equiv f g
|}.
Next Obligation.
  unfold corelation_equiv.
  constructor.
  - intros f.
    apply (@Equivalence_Reflexive _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
  - intros f g.
    apply (@Equivalence_Symmetric _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
  - intros f g h.
    apply (@Equivalence_Transitive _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
Defined.

(** The 恒等 cospan corelation: copairing is
 [id ▽ id : X + X ~> X], codiagonal — epi. （已译） *)
Lemma id_copairing_epic (X : C) :
  Epic (cospan_in1 (cospan_id X) ▽ cospan_in2 (cospan_id X)).
Proof.
  unfold cospan_id, cospan_in1, cospan_in2; simpl.
  constructor.
  intros Z g1 g2 Heq.
  (* g1 ∘ (id ▽ id) ≈ g2 ∘ (id ▽ id) implies g1 ≈ g2.
     Compose both sides with inl: g1 ∘ (id ▽ id) ∘ inl ≈ g2 ∘ (id ▽ id) ∘ inl.
     But (id ▽ id) ∘ inl = id, so g1 ≈ g2. *)
  assert (Hl : g1 ≈ g2).
  { rewrite <- (id_right g1).
    rewrite <- (@inl_merge _ _ X X X id[X] id[X]).
    rewrite comp_assoc.
    rewrite Heq.
    rewrite <- comp_assoc.
    rewrite (@inl_merge _ _ X X X id[X] id[X]).
    apply id_right. }
  exact Hl.
Qed.

Definition corelation_id (X : C) : CorelationArrow X X :=
  {| corelation_cospan := cospan_id X;
     corelation_copairing_epic := id_copairing_epic X |}.

(* * ** Composition: requires epi-stable pushouts

 The 复合 two corelations corelation pushouts
 preserve epimorphisms. We carry typeclass 假设. （已译） *)

Context (HP : HasPushouts C).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class CorelComposable : Type := {
  composite_copairing_epic :
    forall {X Y Z : C}
           (f : CorelationArrow X Y) (g : CorelationArrow Y Z),
    let cf := corelation_cospan f in
    let cg := corelation_cospan g in
    let P  := pushout (cospan_in2 cf) (cospan_in1 cg) in
      Epic ((pushout_in1 P ∘ cospan_in1 cf) ▽ (pushout_in2 P ∘ cospan_in2 cg))
}.

Context `{CC : CorelComposable}.

(** Underlying cospan-level composition of corelations. *)
Definition corelation_underlying_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CospanArrow X Z :=
  cospan_compose HP (corelation_cospan g) (corelation_cospan f).

(** Composition corelations. The copairing-epi witness exactly
 [composite_copairing_epic] [CorelComposable] 假设. （已译） *)
Definition corelation_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CorelationArrow X Z :=
  {| corelation_cospan := corelation_underlying_compose g f;
     corelation_copairing_epic := composite_copairing_epic f g |}.

End Corelation.

Arguments CorelationArrow {C _} X Y.
Arguments corelation_cospan {C _ X Y} _.
Arguments corelation_copairing_epic {C _ X Y} _.
Arguments corelation_id {C _} X.
Arguments corelation_compose {C _ HP CC X Y Z} g f.

(* 相关说明。 （已译） *)
Arguments CorelationArrow_Setoid {C _} X Y.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CorelationCategory.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).
Context `{CC : @CorelComposable C H_Coc HP}.

Lemma corelation_id_left {X Y : C} (f : CorelationArrow X Y) :
  corelation_equiv (corelation_compose (corelation_id Y) f) f.
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  apply (cospan_id_left HP (corelation_cospan f)).
Defined.

Lemma corelation_id_right {X Y : C} (f : CorelationArrow X Y) :
  corelation_equiv (corelation_compose f (corelation_id X)) f.
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  apply (cospan_id_right HP (corelation_cospan f)).
Defined.

Lemma corelation_compose_assoc {X Y Z W : C}
      (h : CorelationArrow Z W) (g : CorelationArrow Y Z) (f : CorelationArrow X Y) :
  corelation_equiv
    (corelation_compose h (corelation_compose g f))
    (corelation_compose (corelation_compose h g) f).
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose; simpl.
  apply (cospan_compose_assoc HP
           (corelation_cospan h)
           (corelation_cospan g)
           (corelation_cospan f)).
Defined.

Lemma corelation_compose_assoc_sym {X Y Z W : C}
      (h : CorelationArrow Z W) (g : CorelationArrow Y Z) (f : CorelationArrow X Y) :
  corelation_equiv
    (corelation_compose (corelation_compose h g) f)
    (corelation_compose h (corelation_compose g f)).
Proof.
  apply (@Equivalence_Symmetric _ _
           (@setoid_equiv _ (@CorelationArrow_Setoid C _ X W))),
        corelation_compose_assoc.
Defined.

Lemma corelation_compose_respects_aux {X Y Z : C}
      (g g' : CorelationArrow Y Z) (f f' : CorelationArrow X Y) :
  corelation_equiv f f' ->
  corelation_equiv g g' ->
  corelation_equiv (corelation_compose g f) (corelation_compose g' f').
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  intros Hf Hg.
  exact (@cospan_compose_respects_aux C HP X Y Z
           (corelation_cospan g) (corelation_cospan g')
           (corelation_cospan f) (corelation_cospan f')
           Hf Hg).
Defined.

(** The corelation category. *)
Program Definition CorelCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => CorelationArrow X Y;
  homset   := fun X Y => @CorelationArrow_Setoid C _ X Y;
  id       := fun X => corelation_id X;
  compose  := fun X Y Z g f => corelation_compose g f;
  compose_respects := _;
  id_left  := fun X Y f => corelation_id_left f;
  id_right := fun X Y f => corelation_id_right f;
  comp_assoc := fun X Y Z W f g h => corelation_compose_assoc f g h;
  comp_assoc_sym := fun X Y Z W f g h => corelation_compose_assoc_sym f g h
|}.
Next Obligation.
  unfold Proper, respectful.
  intros g g' Hg f f' Hf.
  now apply corelation_compose_respects_aux.
Defined.

End CorelationCategory.

Arguments CorelCat C {H_Coc} HP {CC}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CorelToCospan.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).
Context `{CC : @CorelComposable C H_Coc HP}.

Program Definition Corel_to_Cospan : @CorelCat C H_Coc HP CC ⟶ CospanCat C HP := {|
  fobj := fun X => X;
  fmap := fun X Y f => corelation_cospan f
|}.
Solve All Obligations with
  (try (intros; reflexivity);
   try (intros; unfold Proper, respectful;
        intros f f' Hff'; exact Hff')).

End CorelToCospan.

(*
   Reference: nLab "corelation"; B. Fong, "The Algebra of Open and

   本节说明 Corelation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
