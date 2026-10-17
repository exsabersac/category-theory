Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(*
   Wikipedia: https://en.wikipedia.org/wiki/Reflective_subcategory

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma counit_naturality
      {Cadj Dadj : Category} {F : Dadj ⟶ Cadj} {U : Cadj ⟶ Dadj}
      (A : F ⊣ U) {x y : Cadj} (f : x ~> y) :
  @counit Cadj Dadj F U A y ∘ fmap[F] (fmap[U] f)
    ≈ f ∘ @counit Cadj Dadj F U A x.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  now rewrite id_left, id_right.
Qed.

(* The reflector, the fullness witness, and the reflection adjunction. *)

Record Reflective {C : Category} (S : Subcategory C) := {
  reflective_full : Construction.Subcategory.Full C S;
  reflector : C ⟶ Sub C S;
  reflective_adj : reflector ⊣ Incl C S
}.

Arguments reflective_full {C S} r.
Arguments reflector {C S} r.
Arguments reflective_adj {C S} r.

(* The opposite subcategory: the same selected objects, with a C^op-morphism
   x ~> y (that is, a C-morphism y ~> x) selected exactly when the underlying
   C-morphism is selected by S. *)

Definition op_subcategory {C : Category} (S : Subcategory C) :
  Subcategory (C^op) :=
  @Build_Subcategory (C^op)
    (sobj C S)
    (fun x y ox oy f => shom C S oy ox f)
    (fun x y z ox oy oz f g Hf Hg => scomp C S oz oy ox Hg Hf)
    (fun x ox => sid C S ox).

(* A coreflective subcategory of C is a reflective subcategory of C^op on the
   opposite subcategory: the inclusion then has a right adjoint in C. *)

Definition Coreflective {C : Category} (S : Subcategory C) : Type :=
  @Reflective (C^op) (op_subcategory S).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma reflective_counit_iso {C : Category} {S : Subcategory C}
      (R : Reflective S) (x : Sub C S) :
  reflector R (Incl C S x) ≅[Sub C S] x.
Proof.
  unshelve refine
    {| to   := @counit (Sub C S) C (reflector R) (Incl C S)
                 (reflective_adj R) x
     ; from := _
     ; iso_to_from := _
     ; iso_from_to := _ |}.
  - (* inverse: the unit, lifted into the subcategory by fullness *)
    exists (@Category.Theory.Adjunction.unit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (Incl C S x)).
    apply (reflective_full R).
  - (* ε_x ∘ η ≈ id, one triangle identity *)
    apply (@fmap_counit_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
  - (* η ∘ ε_x ≈ id, by counit naturality and the other triangle identity *)
    rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
             (Incl C S x)).
Qed.
