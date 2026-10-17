Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * Monic/epi duality, carried out through the opposite category *)

(*
 nLab: https://ncatlab.org/nlab/show/monomorphism
   nLab: https://ncatlab.org/nlab/show/epimorphism
   Book: Riehl, "Category Theory in Context", §1.2 (Lemma 1.2.11)

   本文件给出对偶性。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The four bridges *)

Definition Monic_of_op_Epic {C : Category} {x y : C} (f : x ~> y)
  (H : @Epic (C^op) y x f) : @Monic C x y f :=
  @Build_Monic C x y f (@epic (C^op) y x f H).

Definition op_Epic_of_Monic {C : Category} {x y : C} (f : x ~> y)
  (H : @Monic C x y f) : @Epic (C^op) y x f :=
  @Build_Epic (C^op) y x f (@monic C x y f H).

Definition Epic_of_op_Monic {C : Category} {x y : C} (f : x ~> y)
  (H : @Monic (C^op) y x f) : @Epic C x y f :=
  @Build_Epic C x y f (@monic (C^op) y x f H).

Definition op_Monic_of_Epic {C : Category} {x y : C} (f : x ~> y)
  (H : @Epic C x y f) : @Monic (C^op) y x f :=
  @Build_Monic (C^op) y x f (@epic C x y f H).

(** ** The dual derivations *)

(*
   本节说明 Duality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition monic_cancel_op {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} : Monic (f ∘ g) → Monic g :=
  fun H => Monic_of_op_Epic g
             (@epic_cancel (C^op) z y x g f (op_Epic_of_Monic (f ∘ g) H)).

(* And [monic_compose] from [epi_compose], the same way. *)
Definition monic_compose_op {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} : Monic f → Monic g → Monic (f ∘ g) :=
  fun Hf Hg =>
    Monic_of_op_Epic (f ∘ g)
      (@epi_compose (C^op) z y x g f
         (op_Epic_of_Monic g Hg) (op_Epic_of_Monic f Hf)).

(*
   本节说明 Duality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition monic_cancel_agrees {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} :
  (Monic (f ∘ g) → Monic g) * (Monic (f ∘ g) → Monic g) :=
  (@monic_cancel C x y z f g, @monic_cancel_op C x y z f g).

Definition monic_compose_agrees {C : Category} {x y z : C}
  {f : y ~> z} {g : x ~> y} :
  (Monic f → Monic g → Monic (f ∘ g)) *
  (Monic f → Monic g → Monic (f ∘ g)) :=
  (@monic_compose C x y z f g, @monic_compose_op C x y z f g).

(** ** The wide subcategories of monos and of epis *)

(*
   本节说明 Duality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition MonoSub (C : Category) : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => Monic f;
  scomp := fun x y z _ _ _ f g Hf Hg => monic_compose Hf Hg;
  sid   := fun x _ => id_monic x
|}.

Definition MonoSub_Wide (C : Category) : Wide C (MonoSub C) :=
  fun _ => ttt.

(*
   本节说明 Duality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition EpiSub (C : Category) : Subcategory C.
Proof.
  unshelve refine {| sobj := fun _ => poly_unit
                   ; shom := fun x y _ _ f => Epic f |}.
  - (* closure under composition, from [monic_compose] read in C^op *)
    intros x y z ox oy oz f g Hf Hg.
    exact (Epic_of_op_Monic (f ∘ g)
             (@monic_compose (C^op) z y x g f
                (op_Monic_of_Epic g Hg) (op_Monic_of_Epic f Hf))).
  - (* identities, from [id_monic] read in C^op *)
    intros x ox.
    exact (Epic_of_op_Monic (@id C x) (@id_monic (C^op) x)).
Defined.

Definition EpiSub_Wide (C : Category) : Wide C (EpiSub C) :=
  fun _ => ttt.

(*
   本节说明 Duality 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Program Definition op_Retraction_of_Section {C : Category} {x y : C}
  (f : x ~> y) (S : Section f) : @Retraction (C^op) y x f := {|
  retract := @section C x y f S
|}.
Next Obligation.
  intros; exact (@section_comp C x y f S).
Qed.

Program Definition Section_of_op_Retraction {C : Category} {x y : C}
  (f : x ~> y) (R : @Retraction (C^op) y x f) : Section f := {|
  section := @retract (C^op) y x f R
|}.
Next Obligation.
  intros; exact (@retract_comp (C^op) y x f R).
Qed.

Program Definition op_Section_of_Retraction {C : Category} {x y : C}
  (f : x ~> y) (R : Retraction f) : @Section (C^op) y x f := {|
  section := @retract C x y f R
|}.
Next Obligation.
  intros; exact (@retract_comp C x y f R).
Qed.

Program Definition Retraction_of_op_Section {C : Category} {x y : C}
  (f : x ~> y) (S : @Section (C^op) y x f) : Retraction f := {|
  retract := @section (C^op) y x f S
|}.
Next Obligation.
  intros; exact (@section_comp (C^op) y x f S).
Qed.
