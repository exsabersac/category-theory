Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Record ReflexivePair {C : Category} {x y : C} (f g : x ~> y) := {
  refl_section : y ~> x;                   (* the common section *)
  refl_section_f : f ∘ refl_section ≈ id;  (* f retracts it *)
  refl_section_g : g ∘ refl_section ≈ id   (* and so does g *)
}.

Arguments refl_section   {_ _ _ _ _} _.
Arguments refl_section_f {_ _ _ _ _} _.
Arguments refl_section_g {_ _ _ _ _} _.

(* A category has reflexive coequalizers when every reflexive pair
   carries an elementary coequalizer.  Compare [HasCoequalizers] in
   [Structure/Coequalizer.v], which asks the same of every parallel
   pair. *)
Class HasReflexiveCoequalizers (C : Category) := {
  reflexive_coeq {x y : C} (f g : x ~> y) :
    ReflexivePair f g → ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e
}.

(** ** Recognizing reflexive pairs *)

(*
   本节说明 Reflexive 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma common_section_reflexive {C : Category} {x y : C} (f g : x ~> y)
  (s : y ~> x) (Hf : f ∘ s ≈ id) (Hg : g ∘ s ≈ id) :
  ReflexivePair f g.
Proof.
  exact {| refl_section   := s
         ; refl_section_f := Hf
         ; refl_section_g := Hg |}.
Defined.

(* When every parallel pair has a coequalizer, so in particular does
   every reflexive one. *)
#[export] Instance HasCoequalizers_HasReflexiveCoequalizers
  {C : Category} `{H : @HasCoequalizers C} : HasReflexiveCoequalizers C := {|
  reflexive_coeq := fun x y f g _ => @coeq C H x y f g
|}.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem functor_preserves_reflexive {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  ReflexivePair f g → ReflexivePair (fmap[F] f) (fmap[F] g).
Proof.
  intros R.
  unshelve refine {| refl_section := fmap[F] (refl_section R) |}.
  - (* fmap f ∘ fmap s ≈ id *)
    rewrite <- fmap_comp.
    rewrite (refl_section_f R).
    apply fmap_id.
  - (* fmap g ∘ fmap s ≈ id *)
    rewrite <- fmap_comp.
    rewrite (refl_section_g R).
    apply fmap_id.
Defined.
