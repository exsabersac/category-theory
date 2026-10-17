Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoid.

Generalizable All Variables.

(** * Group objects in a cartesian monoidal category *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Group_object

   本文件给出群对象相关同态/结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于group objects的来源与用途

   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/Hopf+algebra
   Paper: Eckmann, Hilton, "Group-Like Structures in General Categories I:

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section GroupObject.

Context `{@CartesianMonoidal C}.

Class GroupObject (grp : C) := {
  (* Underlying monoid object: supplies mappend (μ), mempty (η) and the
     associativity + two-sided unit laws. *)
  groupobject_is_monoid : MonoidObject grp;
  (* Inversion / antipode ι : grp ~> grp. *)
  inverse : grp ~> grp;

  (* Left inverse: μ ∘ (ι ⨂ id) ∘ ∆ ≈ η ∘ eliminate (the constant-identity
     endomorphism). Copy g with ∆, invert the left copy, then multiply. *)
  left_inverse : mappend ∘ inverse ⨂ id ∘ ∆ grp ≈ mempty ∘ eliminate;

  (* Right inverse: μ ∘ (id ⨂ ι) ∘ ∆ ≈ η ∘ eliminate, dually inverting the
     right copy. *)
  right_inverse : mappend ∘ id ⨂ inverse ∘ ∆ grp ≈ mempty ∘ eliminate;
}.
#[export] Existing Instance groupobject_is_monoid.

Coercion groupobject_is_monoid : GroupObject >-> MonoidObject.

End GroupObject.

(* Projection to the inversion morphism ι of a given group object [G]. *)
Notation "'inverse' [ G ]" := (@inverse _ _ G _)
  (at level 9, format "inverse [ G ]") : category_scope.
