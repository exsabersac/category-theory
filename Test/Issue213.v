Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(*
   本文件为测试：Issue213。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Issue213 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac Tauto.intuition_solver ::= idtac.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac equivalence_old :=
  constructor; repeat intro; simpl; try cat; intuition.

Section Issue213.

Context {C : Category}.
Context {D : Category}.

(* Verbatim the relation of [adj_morphism_setoid]. *)
Definition issue_213_rel (f g : @adj_morphism C D) : Type :=
  (free_functor f ≅[Fun] free_functor g) *
  (forgetful_functor f ≅[Fun] forgetful_functor g).

(*
   本节说明 Issue213 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example issue_213_old_script_needs_the_wide_search : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  (* 相关说明。 （已译） *)
  assert_fails
    (equivalence_old;
     solve [ transitivity (free_functor y); assumption
           | transitivity (forgetful_functor y); assumption ]).
  (* The positive half, so stays live [Qed] rather than aborted
 sketch: 关系 等价, closed deterministic way. （已译） *)
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* 相关说明。 （已译） *)
Example issue_213_symmetry_is_the_missing_law : Symmetric issue_213_rel.
Proof.
  unfold issue_213_rel.
  assert_fails (solve [ repeat intro; simpl; try cat; intuition ]).
  intros f g [Hfree Hforget].
  split; symmetry; assumption.
Qed.

(* 相关说明。 （已译） *)
Example issue_213_equivalence_unaided : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example issue_213_tactic_is_deterministic : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  equivalence.
  - transitivity (free_functor y); assumption.
  - transitivity (forgetful_functor y); assumption.
Qed.

(* Finally, instance library actually exports really 等价
 [adj_morphism], [≈] resolves it. （已译） *)
Example issue_213_setoid_reflexive (f : @adj_morphism C D) : f ≈ f.
Proof. reflexivity. Qed.

Example issue_213_setoid_symmetric (f g : @adj_morphism C D) : f ≈ g → g ≈ f.
Proof. intros; symmetry; assumption. Qed.

Example issue_213_setoid_transitive (f g h : @adj_morphism C D) :
  f ≈ g → g ≈ h → f ≈ h.
Proof. intros; etransitivity; eassumption. Qed.

End Issue213.
