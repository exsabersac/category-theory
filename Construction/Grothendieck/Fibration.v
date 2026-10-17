Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Fibration.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GrothendieckFibration.

Context {B : Category}.
Context (A : IndexedCat B).

(** ** The chosen opcartesian lift *)

(*
   本节说明 Fibration 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grothendieck_op_lift {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  @dhom (B^op) (Displayed_op (Grothendieck_Displayed A)) y x
        (idx_map A f dx) dx f :=
  @id (idx_fib A y) (idx_map A f dx).

(*
   本节说明 Fibration 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grothendieck_lift_cocartesian {x y : B} (f : x ~> y)
  (dx : idx_fib A x) :
  DCartesian (D := Displayed_op (Grothendieck_Displayed A))
             (Grothendieck_op_lift f dx).
Proof.
  unfold Grothendieck_op_lift.
  constructor; intros z g dz hh; simpl in *.
  unshelve refine {| unique_obj := hh ∘ to (idx_comp A g f dx) |}.
  - (* 相关说明。 （已译） *)
    rewrite fmap_id, id_right.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    apply id_right.
  - (* uniqueness: cancel [from] against [to] *)
    intros v Hv.
    rewrite <- Hv.
    rewrite fmap_id, id_right.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    apply id_right.
Defined.

(** ** The opcleaving *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grothendieck_OpCleaving :
  OpCleaving (Grothendieck_Displayed A) :=
  @Build_Cleaving (B^op) (Displayed_op (Grothendieck_Displayed A))
    (fun u v (f : u ~{ B^op }~> v) (dv : idx_fib A v) =>
       (idx_map A f dv;
        (@Grothendieck_op_lift v u f dv;
         @Grothendieck_lift_cocartesian v u f dv))).

(* * ** The chosen lifts, read total 范畴 ∫ A （已译） *)

(* The chosen opcartesian lift of [f] at [dx], as a morphism of ∫ A from
   [(x; dx)] to [(y; idx_map A f dx)].  Its displayed component is
   definitionally the one chosen by [Grothendieck_OpCleaving]
   ([Grothendieck_colift_is_clift] below). *)
Definition Grothendieck_colift {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  (x; dx) ~{ Grothendieck A }~> (y; idx_map A f dx) :=
  (f; Grothendieck_op_lift f dx).

(* Vertical morphisms: a fibre morphism [k : a ~> b] over [z], embedded as
   a total morphism over [id[z]] by recentring along the unit iso. *)
Definition Grothendieck_vert {z : B} {a b : idx_fib A z} (k : a ~> b) :
  (z; a) ~{ Grothendieck A }~> (z; b) :=
  (@id B z; k ∘ to (idx_id A a)).

(* The total-level lift cleaving's chosen lift agree — both are
 恒等 pushforward, so comparison definitional. （已译） *)
Lemma Grothendieck_colift_is_clift {x y : B} (f : x ~> y)
  (dx : idx_fib A x) :
  `1 (`2 (@clift (B^op) (Displayed_op (Grothendieck_Displayed A))
                 Grothendieck_OpCleaving y x f dx))
    ≈ `2 (Grothendieck_colift f dx).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma Grothendieck_colift_over {x y : B} (f : x ~> y) (dx : idx_fib A x) :
  fmap[Grothendieck_Proj A] (Grothendieck_colift f dx) ≈ f.
Proof. reflexivity. Qed.

(** ** The split laws *)

(*
   本节说明 Fibration 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Grothendieck_split_lift_id {x : B} (dx : idx_fib A x) :
  Grothendieck_vert (to (idx_id A dx)) ∘ Grothendieck_colift (@id B x) dx
    ≈ @id (Grothendieck A) (x; dx).
Proof.
  simpl.
  exists (id_left (@id B x)); simpl.
  unfold Grothendieck_op_lift.
  rewrite fmap_id.
  (* [id_right] applied at exact occurrence: goal carries the
 复合 [id ∘ id] inside dependent 论元 [idx_resp], which
 ambient rewrite would try abstract （已译） *)
  rewrite (id_right
             (to (idx_id A dx) ∘ to (idx_id A (idx_map A (@id B x) dx)))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (idx_id A (idx_map A (@id B x) dx)))).
  rewrite (idx_unit_left_from A (@id B x) dx).
  rewrite iso_to_from.
  apply id_right.
Qed.

(*
   本节说明 Fibration 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Grothendieck_split_lift_comp {x y z : B} (g : y ~> z) (f : x ~> y)
  (dx : idx_fib A x) :
  Grothendieck_vert (to (idx_comp A g f dx))
      ∘ Grothendieck_colift g (idx_map A f dx)
      ∘ Grothendieck_colift f dx
    ≈ Grothendieck_colift (g ∘ f) dx.
Proof.
  assert (e0 : (@id B z ∘ g) ∘ f ≈ g ∘ f).
  { now rewrite id_left. }
  simpl.
  exists e0; simpl.
  unfold Grothendieck_op_lift.
  rewrite !fmap_id, !id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (idx_id A (idx_map A g (idx_map A f dx))))).
  rewrite (idx_unit_left_from A g (idx_map A f dx)).
  rewrite <- (idx_resp_from_sym A (id_left g) (idx_map A f dx)).
  rewrite (comp_assoc (from (idx_resp A (symmetry (id_left g))
                                        (idx_map A f dx)))).
  rewrite (idx_comp_resp_l_from A f (symmetry (id_left g)) (symmetry e0) dx).
  rewrite <- (comp_assoc (from (idx_comp A g f dx))).
  rewrite (comp_assoc (to (idx_comp A g f dx)) (from (idx_comp A g f dx))).
  rewrite iso_to_from.
  rewrite id_left.
  rewrite (idx_resp_from_trans A (symmetry e0) e0 dx).
  apply (idx_resp_from_id A).
Qed.

(** ** The split laws, bundled *)

(* The splitting canonical opcleaving, one named 定理: the
 chosen lifts functorial nose, mediated chosen unit
 复合 isos [A]. （已译） *)
Theorem Grothendieck_Split :
  (∀ (x : B) (dx : idx_fib A x),
     Grothendieck_vert (to (idx_id A dx))
         ∘ Grothendieck_colift (@id B x) dx
       ≈ @id (Grothendieck A) (x; dx))
  ∧ (∀ (x y z : B) (g : y ~> z) (f : x ~> y) (dx : idx_fib A x),
     Grothendieck_vert (to (idx_comp A g f dx))
         ∘ Grothendieck_colift g (idx_map A f dx)
         ∘ Grothendieck_colift f dx
       ≈ Grothendieck_colift (g ∘ f) dx).
Proof.
  split.
  - intros x dx.
    apply Grothendieck_split_lift_id.
  - intros x y z g f dx.
    apply Grothendieck_split_lift_comp.
Qed.

(* * ** The projection cloven fibration op-total 范畴 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Grothendieck_OpCloven :
  ClovenFibration (Total_Proj (Displayed_op (Grothendieck_Displayed A))) :=
  @cleaving_total_cloven (B^op) (Displayed_op (Grothendieck_Displayed A))
    Grothendieck_OpCleaving.

End GrothendieckFibration.
