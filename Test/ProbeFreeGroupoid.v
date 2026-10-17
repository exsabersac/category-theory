(*
   本文件为测试：ProbeFreeGroupoid。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.

Local Open Scope category_scope.

#[local] Existing Instance edgeset.

(* 相关说明。 （已译） *)

(* The hom TYPES free groupoid free 范畴 signed
 quiver agree nose: quotient coarsens 等价 and
 nothing else. （已译） *)
Example control_hom_type (G : Quiver) (x y : G) :
  (x ~{FreeGroupoid G}~> y) = (x ~{FreeSigned G}~> y) := eq_refl.

(* 相关说明。 （已译） *)
Example control_ginv_is_reversal (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  ginv (FreeGroupoid_IsGroupoid G) f = fginv f := eq_refl.

(* Reversal is involutive at Leibniz [=], before any quotient. *)
Check (fun (G : Quiver) (x y : G) (f : x ~{FreeGroupoid G}~> y) =>
         fginv_involutive f : fginv (fginv f) = f).

(* The generator clause 普遍性质 typechecks once 对象
 agreement [Hobj] scope, then conjugated [hom_cast]. （已译） *)
Check (∀ (G : Quiver) (D : Category)
         (F : QuiverHomomorphism G (QuiverOfCat D))
         (K : FreeGroupoid G ⟶ D)
         (Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x)
         (x y : G) (e : edges x y),
       hom_cast (Hobj x) (Hobj y) (fmap[K] (fgpos e))
         ≈ @fedgemap _ _ F x y e).

(* The free 函子's 对象 part word group, definitionally. （已译） *)
Example control_FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X
  := eq_refl.

(* The unit 伴随 computes one-letter word. （已译） *)
Example control_unit_computes (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

(* [Deloop] accepts an [Instance/Grp.v] group only through the bridge. *)
Check (fun H : GrpObject => grp_deloop H).

(* 相关说明。 （已译） *)

(* The free groupoid not free 范畴 signed quiver: the
 [homset] fields differ. (Stripped [Fail]: "cannot unify".) （已译） *)
Fail Example probe_groupoid_is_free_category (G : Quiver) :
  FreeGroupoid G = FreeSigned G := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe_inverse_definitional (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  @compose (FreeGroupoid G) x y x (fginv f) f = @id (FreeGroupoid G) x
  := eq_refl.

(* 相关说明。 （已译） *)
Fail Example probe_counit_computes (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w = free_grp_extend (@id Sets (Grp_Forget H)) w
  := eq_refl.

(*
   本节说明 ProbeFreeGroupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (∀ (G : Quiver) (D : Category)
              (F : QuiverHomomorphism G (QuiverOfCat D))
              (K : FreeGroupoid G ⟶ D)
              (x y : G) (e : edges x y),
            fmap[K] (fgpos e) ≈ @fedgemap _ _ F x y e).

(* [Deloop] does not accept an [Instance/Grp.v] group directly: it wants a
   [MonObject], and there is no coercion.  (Stripped of [Fail]: "The term
   ... has type GrpObject while it is expected to have type MonObject".) *)
Fail Check (fun H : GrpObject => Deloop H).
