(*
   本文件给出极限/余极限的创造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(* * * A full subcategory closed under limits created 含入 （已译） *)

Section SubcategoryCreation.

Context {C : Category} (S : Subcategory C) (full : Full C S).

(* Closure under limits: apex any limiting cone [C] over diagram
 [S]-对象 again [S]-对象. The legs need no clause because
 [S] full. （已译） *)
Definition ClosedUnderLimits : Type :=
  ∀ (J : Category) (K : J ⟶ Sub C S) (N : Cone (Incl C S ◯ K)),
    IsLimitCone N → sobj C S (vertex_obj[N]).

Context (closed : ClosedUnderLimits).

Section AtDiagram.
Context {J : Category} (K : J ⟶ Sub C S).

(* 相关说明。 （已译） *)
Definition sub_lift (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) : Cone K.
Proof using C J K S closed full.
  unshelve refine
    (@Build_Cone J (Sub C S) K (vertex_obj[N]; closed J K N HN)
       (@Build_ACone J (Sub C S) (vertex_obj[N]; closed J K N HN) K
          (fun x => (cone_leg N x; full _ _ _ _ (cone_leg N x))) _)).
  intros x y f; simpl.
  exact (@cone_coherence J C (vertex_obj[N]) (Incl C S ◯ K) coneFrom x y f).
Defined.

Example sub_lift_apex (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) :
  (`1 vertex_obj[sub_lift N HN]) = vertex_obj[N] := eq_refl.

Example sub_lift_leg (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) (x : J) :
  (`1 (cone_leg (sub_lift N HN) x)) = cone_leg N x := eq_refl.

(* The image lift [N] itself, up 恒等 同构. （已译） *)
Definition sub_cone_iso (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N) :
  ConeIso (FCone (Incl C S) (sub_lift N HN)) N.
Proof using C J K S closed full.
  exists iso_id.
  intro x; simpl. now rewrite id_right.
Defined.

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sub_ReflectsLimitCone : ReflectsLimitCone K (Incl C S) :=
  fun M H =>
    @ff_ReflectsLimitCone (Sub C S) C (Incl C S)
      (Full_Implies_Full_Functor C S full) (Incl_Faithful C S) J K M H.

Definition sub_CreatesLimit : CreatesLimit K (Incl C S) :=
  {| creates_lift      := sub_lift
   ; creates_lift_over := sub_cone_iso
   ; creates_reflect   := sub_ReflectsLimitCone |}.

End AtDiagram.

Definition sub_CreatesAllLimits : CreatesAllLimits (Incl C S) :=
  fun J K => sub_CreatesLimit K.

(* Mac Lane §V.4 Theorem 2, second half, at a full subcategory closed under
   limits: the subcategory inherits completeness. *)
Definition sub_Complete (HC : @Complete C) : @Complete (Sub C S) :=
  creates_limits_Complete (Incl C S) HC sub_CreatesAllLimits.

End SubcategoryCreation.
