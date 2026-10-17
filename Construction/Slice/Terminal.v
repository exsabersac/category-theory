Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * The slice over 终对象 ambient 范畴 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/over+category
   nLab:      https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Block A: slice over 终对象 （已译） *)

Section SliceTerminal.

Context {C : Category}.
Context {T : @Terminal C}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Slice_Forget :
  @Slice C (@terminal_obj C T) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Slice_Section :
  C ⟶ @Slice C (@terminal_obj C T) := {|
  fobj := fun x => (x; one);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply one_unique. Qed.

(*
   本节说明同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition slice_terminal_unit (x : @Slice C (@terminal_obj C T)) :
  Slice_Section (Slice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(* The component carried 恒等 C, both directions. （已译） *)
Corollary slice_terminal_unit_carrier
  (x : @Slice C (@terminal_obj C T)) :
  (`1 (to (slice_terminal_unit x)) ≈ id) ∧
  (`1 (from (slice_terminal_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(*
   本节说明等价、同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Slice_Terminal :
  @Slice C (@terminal_obj C T) ≅[Cat] C := {|
  to   := Slice_Forget;
  from := Slice_Section
|}.
(*
   本节说明 Terminal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  (*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  exists slice_terminal_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

(*
   本节说明函子、同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Slice_Terminal_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Slice_Forget ◯ Slice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End SliceTerminal.

(* * ** Block B: coslice under 始对象 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CosliceInitial.

Context {C : Category}.
Context {I : @Initial C}.

(* Drop the structure morphism out of 0. *)
Program Definition Coslice_Forget :
  @Coslice C (@initial_obj C I) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(* Equip 对象 唯一箭头 out 0; triangle condition
 `zero ≈ f ∘ zero` discharged [zero_unique] (equivalently, the
 推论 [zero_comp]). （已译） *)
Program Definition Coslice_Section :
  C ⟶ @Coslice C (@initial_obj C I) := {|
  fobj := fun x => (x; zero);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply zero_unique. Qed.

Program Definition coslice_initial_unit (x : @Coslice C (@initial_obj C I)) :
  Coslice_Section (Coslice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply zero_unique. Qed.
Next Obligation. apply zero_unique. Qed.

Corollary coslice_initial_unit_carrier
  (x : @Coslice C (@initial_obj C I)) :
  (`1 (to (coslice_initial_unit x)) ≈ id) ∧
  (`1 (from (coslice_initial_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(* 相关说明。 （已译） *)
Program Definition Coslice_Initial :
  @Coslice C (@initial_obj C I) ≅[Cat] C := {|
  to   := Coslice_Forget;
  from := Coslice_Section
|}.
(*
   本节说明 Terminal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  exists coslice_initial_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

Lemma Coslice_Initial_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Coslice_Forget ◯ Coslice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End CosliceInitial.
