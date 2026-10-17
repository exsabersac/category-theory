Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件给出例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** A commuting square in [Coq] *)

(*      unit --(fun _ => true)--> bool
          |                        |
    (fun _ => false)             negb
          |                        |
          v                        v
         bool --------id--------> bool

   Both routes send the unique element of [unit] to [false]. *)

Definition coq_sq_u : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => true.
Definition coq_sq_v : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_sq_h : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => false.
Definition coq_sq_k : (bool : Coq) ~{Coq}~> (bool : Coq) := Datatypes.id.

Definition CoqCommutingSquare : Diagram SquareQuiver Coq :=
  SquareDiagram coq_sq_u coq_sq_v coq_sq_h coq_sq_k.

(* The square commutes, hence so does every pair of parallel paths over it. *)
Example coq_square_commutative : Commutative CoqCommutingSquare.
Proof.
  apply square_commutes.
  now intros [].
Qed.

(* 相关说明。 （已译） *)
Example coq_sq_legs_differ : (coq_sq_u ≈[Coq] coq_sq_h) -> False.
Proof.
  intro Heq.
  specialize (Heq tt); simpl in Heq.
  discriminate Heq.
Qed.

Example coq_sq_sides_differ : (coq_sq_v ≈[Coq] coq_sq_k) -> False.
Proof.
  intro Heq.
  specialize (Heq true); simpl in Heq.
  discriminate Heq.
Qed.

(* 相关说明。 （已译） *)

(*      unit ----id----> unit
          |                |
         id        (fun _ => true)
          |                |
          v                v
         unit --(fun _ => false)--> bool

   One route lands on [true], the other on [false]. *)

Definition coq_bad_u : (unit : Coq) ~{Coq}~> (unit : Coq) := Datatypes.id.
Definition coq_bad_v : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => true.
Definition coq_bad_h : (unit : Coq) ~{Coq}~> (unit : Coq) := Datatypes.id.
Definition coq_bad_k : (unit : Coq) ~{Coq}~> (bool : Coq) := fun _ => false.

Definition CoqNonCommutingSquare : Diagram SquareQuiver Coq :=
  SquareDiagram coq_bad_u coq_bad_v coq_bad_h coq_bad_k.

(* [Coq] is not thin: these two parallel morphisms are not [≈]. *)
Example coq_parallel_not_equiv : (coq_bad_v ≈[Coq] coq_bad_k) -> False.
Proof.
  intro Heq.
  specialize (Heq tt); simpl in Heq.
  discriminate Heq.
Qed.

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example coq_square_not_commutative : Commutative CoqNonCommutingSquare -> False.
Proof.
  intro Hc.
  pose proof (square_commutes_inv coq_bad_u coq_bad_v coq_bad_h coq_bad_k Hc)
    as Hbad.
  specialize (Hbad tt); simpl in Hbad.
  discriminate Hbad.
Qed.

(** ** The same, for the triangle *)

(*   bool --negb--> bool --negb--> bool   versus   bool --id--> bool  *)

Definition coq_tri_u : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_tri_v : (bool : Coq) ~{Coq}~> (bool : Coq) := negb.
Definition coq_tri_w : (bool : Coq) ~{Coq}~> (bool : Coq) := Datatypes.id.

Definition CoqCommutingTriangle : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_tri_u coq_tri_v coq_tri_w.

Example coq_triangle_commutative : Commutative CoqCommutingTriangle.
Proof.
  apply triangle_commutes.
  now intros [].
Qed.

(* 相关说明。 （已译） *)
Definition CoqNonCommutingTriangle : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_tri_u coq_tri_v coq_tri_u.

Example coq_triangle_not_commutative :
  Commutative CoqNonCommutingTriangle -> False.
Proof.
  intro Hc.
  pose proof (triangle_commutes_inv coq_tri_u coq_tri_v coq_tri_u Hc) as Hbad.
  specialize (Hbad true); simpl in Hbad.
  discriminate Hbad.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary cone_leg_commutative_iff {J C : Category} {F : J ⟶ C} {c : C}
          `{@ACone J C c F} {x y : J} (f : x ~{J}~> y) :
  Commutative (TriangleDiagram (vertex_map x) (fmap[F] f) (vertex_map y))
    ↔ fmap[F] f ∘ vertex_map x ≈ vertex_map y.
Proof. apply triangle_commutative_iff. Qed.

Corollary cone_leg_commutes {J C : Category} {F : J ⟶ C} {c : C}
          `{@ACone J C c F} {x y : J} (f : x ~{J}~> y) :
  Commutative (TriangleDiagram (vertex_map x) (fmap[F] f) (vertex_map y)).
Proof. apply triangle_commutes, cone_coherence. Qed.

(* A pullback square: [Theory/Morphisms/Stability.v]'s
 [is_pullback_commutes] exactly commutativity walking square
 two projections two given 态射. （已译） *)
Corollary pullback_square_commutative_iff {C : Category} {x y z : C}
          (f : x ~> z) (g : y ~> z) {P : C} (p1 : P ~> x) (p2 : P ~> y) :
  Commutative (SquareDiagram p1 f p2 g) ↔ f ∘ p1 ≈ g ∘ p2.
Proof. apply square_commutative_iff. Qed.

Corollary pullback_square_commutes {C : Category} {x y z : C}
          {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
          (Hpb : IsPullback f g P p1 p2) :
  Commutative (SquareDiagram p1 f p2 g).
Proof. apply square_commutes, (is_pullback_commutes Hpb). Qed.


(* * ** The walking loop: diagram draws non-恒等 endomorphism （已译） *)

(*
   本节说明 Examples 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CoqLoopNegb : Diagram LoopQuiver Coq :=
  LoopDiagram (negb : (bool : Coq) ~{Coq}~> (bool : Coq)).

Definition CoqLoopId : Diagram LoopQuiver Coq :=
  LoopDiagram (Datatypes.id : (bool : Coq) ~{Coq}~> (bool : Coq)).

(* 相关说明。 （已译） *)
Example coq_loop_negb_not_commutative : Commutative CoqLoopNegb -> False.
Proof.
  intro Hc.
  pose proof (loop_commutes_inv _ Hc true) as H.
  discriminate H.
Qed.

(* The positive witness over same shape same 范畴. （已译） *)
Example coq_loop_id_commutative : Commutative CoqLoopId.
Proof.
  apply loop_commutes.
  now intro b.
Qed.
