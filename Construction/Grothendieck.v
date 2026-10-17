Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.

Generalizable All Variables.

(** * The Grothendieck construction *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the construction的来源与用途

   nLab:  https://ncatlab.org/nlab/show/Grothendieck+construction

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Section Grothendieck.

Context {B : Category}.
Context (A : IndexedCat B).

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition idx_map_iso {x y : B} (f : x ~> y) {a b : idx_fib A x}
  (i : a ≅ b) : idx_map A f a ≅ idx_map A f b := {|
  to   := fmap[idx_map A f] (to i);
  from := fmap[idx_map A f] (from i)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp, iso_to_from.
  apply fmap_id.
Qed.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp, iso_from_to.
  apply fmap_id.
Qed.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Transport inverses are proof-irrelevant, so [from] at [e] agrees with
   [to] at any proof [e'] of the reversed relation. *)
Lemma idx_resp_from_flip {x y : B} {f g : x ~> y} (e : f ≈ g) (e' : g ≈ f)
  (a : idx_fib A x) :
  from (idx_resp A e a) ≈ to (idx_resp A e' a).
Proof.
  rewrite <- (idx_resp_to_sym A e a).
  apply idx_resp_irrel.
Qed.

(* [idx_comp_resp_l], inverted. *)
Lemma idx_comp_resp_l_from {x y z : B} {f f' : y ~> z} (g : x ~> y)
  (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g) (a : idx_fib A x) :
  from (idx_resp A e (idx_map A g a)) ∘ from (idx_comp A f' g a)
    ≈ from (idx_comp A f g a) ∘ from (idx_resp A e' a).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A f' g a) (idx_resp A e (idx_map A g a)))
    (iso_compose (idx_resp A e' a) (idx_comp A f g a))
    (idx_comp_resp_l A g e e' a))).
Qed.

(* [idx_comp_resp_r], inverted. *)
Lemma idx_comp_resp_r_from {x y z : B} (f : y ~> z) {g g' : x ~> y}
  (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g') (a : idx_fib A x) :
  fmap[idx_map A f] (from (idx_resp A e a)) ∘ from (idx_comp A f g' a)
    ≈ from (idx_comp A f g a) ∘ from (idx_resp A e' a).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A f g' a) (idx_map_iso f (idx_resp A e a)))
    (iso_compose (idx_resp A e' a) (idx_comp A f g a))
    (idx_comp_resp_r A f e e' a))).
Qed.

(* [idx_unit_left] rearranged: cancelling the composition iso against its
   inverse isolates the mediator of the left unit law. *)
Lemma idx_unit_left_from {x y : B} (f : x ~> y) (a : idx_fib A x) :
  to (idx_id A (idx_map A f a)) ∘ from (idx_comp A (@id B y) f a)
    ≈ to (idx_resp A (id_left f) a).
Proof.
  rewrite <- (idx_unit_left A f a).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(* [idx_unit_right] rearranged likewise. *)
Lemma idx_unit_right_from {x y : B} (f : x ~> y) (a : idx_fib A x) :
  fmap[idx_map A f] (to (idx_id A a)) ∘ from (idx_comp A f (@id B x) a)
    ≈ to (idx_resp A (id_right f) a).
Proof.
  rewrite <- (idx_unit_right A f a).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(* [idx_cocycle], inverted: the from-composites reverse. *)
Lemma idx_cocycle_from {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : idx_fib A w) :
  from (idx_comp A f g (idx_map A h a)) ∘ from (idx_comp A (f ∘ g) h a)
    ≈ fmap[idx_map A f] (from (idx_comp A g h a))
        ∘ (from (idx_comp A f (g ∘ h) a)
             ∘ from (idx_resp A (comp_assoc f g h) a)).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_comp A (f ∘ g) h a) (idx_comp A f g (idx_map A h a)))
    (iso_compose (iso_compose (idx_resp A (comp_assoc f g h) a)
                              (idx_comp A f (g ∘ h) a))
                 (idx_map_iso f (idx_comp A g h a)))
    (idx_cocycle A f g h a))).
Qed.

(*
   本节说明 Grothendieck 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Grothendieck_transport_trans {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f g h : x ~> y}
  (e1 : f ≈ g) (e2 : g ≈ h) (e3 : f ≈ h) (ff : idx_map A f dx ~> dy) :
  (ff ∘ from (idx_resp A e1 dx)) ∘ from (idx_resp A e2 dx)
    ≈ ff ∘ from (idx_resp A e3 dx).
Proof.
  rewrite <- comp_assoc.
  rewrite (idx_resp_from_trans A e1 e2 dx).
  apply compose_respects.
  - reflexivity.
  - apply idx_resp_from_irrel.
Qed.

Lemma Grothendieck_transport_comp_l {x y z : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f f' : y ~> z} {g : x ~> y} (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g)
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy) :
  (ff ∘ from (idx_resp A e dy)) ∘ fmap[idx_map A f'] gg
      ∘ from (idx_comp A f' g dx)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx))
        ∘ from (idx_resp A e' dx).
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_resp A e dy)) (fmap[idx_map A f'] gg)).
  rewrite <- (idx_resp_natural_from A e gg).
  rewrite <- !comp_assoc.
  rewrite (idx_comp_resp_l_from g e e' dx).
  reflexivity.
Qed.

Lemma Grothendieck_transport_comp_r {x y z : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f : y ~> z} {g g' : x ~> y} (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g')
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy) :
  ff ∘ fmap[idx_map A f] (gg ∘ from (idx_resp A e dx))
     ∘ from (idx_comp A f g' dx)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx))
        ∘ from (idx_resp A e' dx).
Proof.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (idx_comp_resp_r_from f e e' dx).
  reflexivity.
Qed.

Lemma Grothendieck_did_left {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f : x ~> y}
  (e : f ≈ @id B y ∘ f) (ff : idx_map A f dx ~> dy) :
  to (idx_id A dy) ∘ fmap[idx_map A (@id B y)] ff
     ∘ from (idx_comp A (@id B y) f dx)
    ≈ ff ∘ from (idx_resp A e dx).
Proof.
  rewrite (idx_resp_from_flip e (id_left f) dx).
  rewrite <- (idx_id_natural A ff).
  rewrite <- comp_assoc.
  rewrite (idx_unit_left_from f dx).
  reflexivity.
Qed.

Lemma Grothendieck_did_right {x y : B}
  {dx : idx_fib A x} {dy : idx_fib A y} {f : x ~> y}
  (e : f ≈ f ∘ @id B x) (ff : idx_map A f dx ~> dy) :
  ff ∘ fmap[idx_map A f] (to (idx_id A dx))
     ∘ from (idx_comp A f (@id B x) dx)
    ≈ ff ∘ from (idx_resp A e dx).
Proof.
  rewrite (idx_resp_from_flip e (id_right f) dx).
  rewrite <- comp_assoc.
  rewrite (idx_unit_right_from f dx).
  reflexivity.
Qed.

Lemma Grothendieck_assoc {w x y z : B}
  {dw : idx_fib A w} {dx : idx_fib A x} {dy : idx_fib A y} {dz : idx_fib A z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h))
  (ff : idx_map A f dy ~> dz) (gg : idx_map A g dx ~> dy)
  (hh : idx_map A h dw ~> dx) :
  ff ∘ fmap[idx_map A f]
         (gg ∘ fmap[idx_map A g] hh ∘ from (idx_comp A g h dw))
     ∘ from (idx_comp A f (g ∘ h) dw)
    ≈ (ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
          ∘ fmap[idx_map A (f ∘ g)] hh ∘ from (idx_comp A (f ∘ g) h dw))
        ∘ from (idx_resp A e dw).
Proof.
  rewrite (idx_resp_from_flip e (comp_assoc f g h) dw).
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_comp A f g dx))
                      (fmap[idx_map A (f ∘ g)] hh)).
  rewrite <- (idx_comp_natural_from A f g hh).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (from (idx_comp A f g (idx_map A h dw)))
                      (from (idx_comp A (f ∘ g) h dw))).
  rewrite (idx_cocycle_from f g h dw).
  rewrite <- !comp_assoc.
  rewrite (iso_from_to (idx_resp A (comp_assoc f g h) dw)).
  rewrite id_right.
  reflexivity.
Qed.

(** ** The displayed category over B, its total category, the projection *)

Program Definition Grothendieck_Displayed : Displayed B := {|
  dobj := fun x => idx_fib A x;
  dhom := fun x y dx dy f => idx_map A f dx ~{ idx_fib A y }~> dy;
  dhomset := fun x y dx dy f => @homset (idx_fib A y) (idx_map A f dx) dy;
  dtransport := fun x y dx dy f g e ff => ff ∘ from (idx_resp A e dx);
  did := fun x dx => to (idx_id A dx);
  dcomp := fun x y z dx dy dz f g ff gg =>
             ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
|}.
Next Obligation.
  (* dtransport_respects *)
  intros x y dx dy f g e ff gg Hfg; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  (* dtransport_id, from proof irrelevance of [idx_resp] *)
  intros x y dx dy f e ff; simpl.
  rewrite (idx_resp_from_id A e dx).
  apply id_right.
Qed.
Next Obligation.
  (* dtransport_trans *)
  intros x y dx dy f g h e1 e2 ff; simpl.
  apply Grothendieck_transport_trans.
Qed.
Next Obligation.
  (* dcomp_respects *)
  intros x y z dx dy dz f g ff ff' Hf gg gg' Hg; simpl.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  (* dtransport_comp_l *)
  intros x y z dx dy dz f f' g e e' ff gg; simpl.
  apply Grothendieck_transport_comp_l.
Qed.
Next Obligation.
  (* dtransport_comp_r *)
  intros x y z dx dy dz f g g' e e' ff gg; simpl.
  apply Grothendieck_transport_comp_r.
Qed.
Next Obligation.
  (* did_left *)
  intros x y dx dy f ff; simpl.
  apply Grothendieck_did_left.
Qed.
Next Obligation.
  (* did_right *)
  intros x y dx dy f ff; simpl.
  apply Grothendieck_did_right.
Qed.
Next Obligation.
  (* dcomp_assoc *)
  intros w x y z dw dx dy dz f g h ff gg hh; simpl.
  apply Grothendieck_assoc.
Qed.

(** The Grothendieck construction ∫ A: the total category of the displayed
    presentation. *)
Definition Grothendieck : Category := Total Grothendieck_Displayed.

(** The projection ∫ A ⟶ B, taking first components. *)
Definition Grothendieck_Proj : Grothendieck ⟶ B :=
  Total_Proj Grothendieck_Displayed.

End Grothendieck.
