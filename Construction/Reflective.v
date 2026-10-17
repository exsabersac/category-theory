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

(* The reflector, fullness witness, reflection 伴随. （已译） *)

Record Reflective {C : Category} (S : Subcategory C) := {
  reflective_full : Construction.Subcategory.Full C S;
  reflector : C ⟶ Sub C S;
  reflective_adj : reflector ⊣ Incl C S
}.

Arguments reflective_full {C S} r.
Arguments reflector {C S} r.
Arguments reflective_adj {C S} r.

(* The opposite subcategory: same selected 对象, C^op-态射
 x ~> y (that is, C-态射 y ~> x) selected exactly underlying
 C-态射 selected S. （已译） *)

Definition op_subcategory {C : Category} (S : Subcategory C) :
  Subcategory (C^op) :=
  @Build_Subcategory (C^op)
    (sobj C S)
    (fun x y ox oy f => shom C S oy ox f)
    (fun x y z ox oy oz f g Hf Hg => scomp C S oz oy ox Hg Hf)
    (fun x ox => sid C S ox).

(* A coreflective subcategory C reflective subcategory C^op the
 opposite subcategory: 含入 then has 右伴随 C. （已译） *)

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
  - (* inverse: unit, lifted 进入 subcategory fullness （已译） *)
    exists (@Category.Theory.Adjunction.unit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (Incl C S x)).
    apply (reflective_full R).
  - (* ε_x ∘ η ≈ id, one triangle identity *)
    apply (@fmap_counit_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
  - (* η ∘ ε_x ≈ id, counit 自然性 other triangle 恒等 （已译） *)
    rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
             (Incl C S x)).
Qed.
