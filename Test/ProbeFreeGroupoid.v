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

(** ** Positive controls: the definitional claims *)

(* The hom TYPES of the free groupoid and of the free category on the signed
   quiver agree on the nose: the quotient coarsens the equivalence and
   nothing else. *)
Example control_hom_type (G : Quiver) (x y : G) :
  (x ~{FreeGroupoid G}~> y) = (x ~{FreeSigned G}~> y) := eq_refl.

(* The chosen inverse of the groupoid structure IS word reversal. *)
Example control_ginv_is_reversal (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  ginv (FreeGroupoid_IsGroupoid G) f = fginv f := eq_refl.

(* Reversal is involutive at Leibniz [=], before any quotient. *)
Check (fun (G : Quiver) (x y : G) (f : x ~{FreeGroupoid G}~> y) =>
         fginv_involutive f : fginv (fginv f) = f).

(* The generator clause of the universal property typechecks once the object
   agreement [Hobj] is in scope, and is then conjugated by [hom_cast]. *)
Check (∀ (G : Quiver) (D : Category)
         (F : QuiverHomomorphism G (QuiverOfCat D))
         (K : FreeGroupoid G ⟶ D)
         (Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x)
         (x y : G) (e : edges x y),
       hom_cast (Hobj x) (Hobj y) (fmap[K] (fgpos e))
         ≈ @fedgemap _ _ F x y e).

(* The free functor's object part is the word group, definitionally. *)
Example control_FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X
  := eq_refl.

(* The unit of the adjunction computes to the one-letter word. *)
Example control_unit_computes (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

(* [Deloop] accepts an [Instance/Grp.v] group only through the bridge. *)
Check (fun H : GrpObject => grp_deloop H).

(** ** Negative probes: these commands MUST fail *)

(* The free groupoid is not the free category on the signed quiver: the
   [homset] fields differ.  (Stripped of [Fail]: "cannot unify".) *)
Fail Example probe_groupoid_is_free_category (G : Quiver) :
  FreeGroupoid G = FreeSigned G := eq_refl.

(* The inverse law is not definitional.  (Stripped of [Fail]: "Unable to
   unify ... with ...".) *)
Fail Example probe_inverse_definitional (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  @compose (FreeGroupoid G) x y x (fginv f) f = @id (FreeGroupoid G) x
  := eq_refl.

(* The counit does not compute.  (Stripped of [Fail]: "cannot unify",
   the offending head being the opaque [ump_universal_arrows].) *)
Fail Example probe_counit_computes (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w = free_grp_extend (@id Sets (Grp_Forget H)) w
  := eq_refl.

(* The generator clause of the universal property is not even well-typed
   without the object agreement in scope — this is why the bundled
   [free_groupoid_universal] nests [Hobj] inside the sigma.  (Stripped of
   [Fail]: a typing error on the two sides of [≈].) *)
Fail Check (∀ (G : Quiver) (D : Category)
              (F : QuiverHomomorphism G (QuiverOfCat D))
              (K : FreeGroupoid G ⟶ D)
              (x y : G) (e : edges x y),
            fmap[K] (fgpos e) ≈ @fedgemap _ _ F x y e).

(* [Deloop] does not accept an [Instance/Grp.v] group directly: it wants a
   [MonObject], and there is no coercion.  (Stripped of [Fail]: "The term
   ... has type GrpObject while it is expected to have type MonObject".) *)
Fail Check (fun H : GrpObject => Deloop H).
