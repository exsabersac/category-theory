Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Equivalence.Adjoint.Compose.

Generalizable All Variables.

(*
   本文件为测试：ProbeAdjointCompose379。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instrument check: a name that exists nowhere must be rejected. *)
Fail Check probe379_no_such_constant_anywhere.

(* * ** Guards: every 常值 negative names, named outside [Fail] （已译） *)

Check @AdjointEquivalence_Compose.
Check @AdjointEquivalence_Compose_via_equivalence.
Check @AdjointEquivalence_Compose_unit.
Check @AdjointEquivalence_Compose_counit.
Check @AdjointEquivalence_Compose_unit_transpose.
Check @AdjointEquivalence_Id.
Check @Id.
Check @adjoint_equivalence_compose_adj.
Check @assoc_left.
Check @assoc_right.
Check @indiscrete_square.
Check @indiscrete_swap.
Check @IsIso_id.
Check @IsIso_along.
Check @IsIso_comp.
Check @IsIso_fmap.
Check @adj_equivalence.
Check @Adjunction_Compose.
Check @unit.
Check @counit.
Check @AdjointEquivalence.
Check @Adjunction.
Check @Equivalence_to_AdjointEquivalence.
Check @EquivalenceOfCategories_Compose.
Check @AdjointEquivalence_to_Equivalence.
Check @AdjointEquivalence_swap.
Check IndT.
Check (Indiscrete bool).
Check @Erase.

(* 相关说明。 （已译） *)

Section Routes.

Context {C D E : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context {F' : D ⟶ E} {U' : E ⟶ D}.
Context (A : AdjointEquivalence F U).
Context (B : AdjointEquivalence F' U').

(* 相关说明。 （已译） *)
Check (AdjointEquivalence_Compose A B
       : AdjointEquivalence (F' ◯ F) (U ◯ U')).
Check (AdjointEquivalence_Compose_via_equivalence A B
       : AdjointEquivalence (F' ◯ F) (U ◯ U')).

(* Negative 1 (CONVERSION): refinement route not direct
 复合, whole record. （已译） *)
Fail Example probe379_neg1 :
  AdjointEquivalence_Compose_via_equivalence A B
    = AdjointEquivalence_Compose A B := eq_refl.

(* Negative 2 (CONVERSION): nor on the underlying adjunction. *)
Fail Example probe379_neg2 :
  @adj_equivalence _ _ _ _ (AdjointEquivalence_Compose_via_equivalence A B)
    = @adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B) := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe379_neg3 (x : C) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose_via_equivalence A B))
    x
  = @unit _ _ _ _
      (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x := eq_refl.

Example probe379_ctrl_direct_reduces (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    = to (@adj _ _ _ _ (@adj_equivalence _ _ _ _ A) x (U' (F' (F x))))
         (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x)) := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe379_neg4 (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    = fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example probe379_ctrl_unit_approx (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    ≈ fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  AdjointEquivalence_Compose_unit A B x.

(* 相关说明。 （已译） *)
Fail Example probe379_neg5 (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y))
  := eq_refl.

Example probe379_ctrl_counit_approx (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) y
    ≈ @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) :=
  AdjointEquivalence_Compose_counit A B y.

End Routes.

(* 相关说明。 （已译） *)

Section Laws.

Context {C1 C2 C3 C4 : Category}.
Context {F1 : C1 ⟶ C2} {U1 : C2 ⟶ C1}.
Context {F2 : C2 ⟶ C3} {U2 : C3 ⟶ C2}.
Context {F3 : C3 ⟶ C4} {U3 : C4 ⟶ C3}.
Context (A : AdjointEquivalence F1 U1).
Context (B : AdjointEquivalence F2 U2).
Context (G : AdjointEquivalence F3 U3).

(* Positive controls: each bracketing is formable, at ITS OWN type. *)
Check (assoc_left A B G
       : AdjointEquivalence (F3 ◯ (F2 ◯ F1)) ((U1 ◯ U2) ◯ U3)).
Check (assoc_right A B G
       : AdjointEquivalence ((F3 ◯ F2) ◯ F1) (U1 ◯ (U2 ◯ U3))).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (assoc_left A B G = assoc_right A B G).

Example probe379_ctrl_assoc_unit (x : C1) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (assoc_left A B G)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ (assoc_right A B G)) x :=
  AdjointEquivalence_Compose_assoc_unit A B G x.

(* Negative 7 (TYPING): same left 恒等 law. （已译） *)
Fail Check (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A = A).

Example probe379_ctrl_id_left_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  AdjointEquivalence_Compose_id_left_unit A x.

End Laws.

(* Negative 8 (TYPING): the witness is likewise not of identity type --
   its two functors move an object, so it does not even have the TYPE of
   an identity adjoint equivalence.  Control: the object is moved. *)
Example probe379_ctrl_witness_moves :
  (IndT ◯ Erase (Indiscrete bool)) false = true := eq_refl.

Fail Check (indiscrete_square = @AdjointEquivalence_Id (Indiscrete bool)).

(* 相关说明。 （已译） *)

Section HomIsProof.

Universes co ch cp.
Constraint ch < cp.
Context (Cu : Category@{co ch cp}).
Context (G H : Cu ⟶ Cu).
Context (x y : Cu).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (x ~{Cu}~> y).
Check (@id Cu x).
Check (Cu ⟶ Cu).
Check (@IsIsomorphism Cu x y).
Check (@IsIso_id Cu x).
Check (@IsIso_along Cu x y).
Check (@IsIso_comp Cu x y).
Check (@IsIso_fmap Cu Cu G x y).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@Id Cu).

(* Negative 10 (FORMABILITY): [Adjunction] identifies hom 证明
 INDEPENDENTLY
 that, probed here at two arbitrary endofunctors so no [Id]
 occurs command. （已译） *)
Fail Check (@Adjunction Cu Cu G H).

(* Negative 11 (FORMABILITY): so does [AdjointEquivalence] -- but it
   CANNOT be
   tested apart from [Adjunction], its first field being [F -| U], so
   this is a second donor and NOT an independent cause. *)
Fail Check (@AdjointEquivalence Cu Cu G H).

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@AdjointEquivalence_Id Cu).

End HomIsProof.

Section HomLevelsApart.

Universes ao ah bo bh.
Constraint ah < bh.
Context (Au : Category@{ao ah ah}).
Context (Bu : Category@{bo bh bh}).

(* Control: a functor in one direction is formable. *)
Check (Au ⟶ Bu).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Bu ⟶ Au).

End HomLevelsApart.
