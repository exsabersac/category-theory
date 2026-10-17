(*
   本文件为测试：ProbeQuiverConstructions。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Constructions.

Local Open Scope category_scope.

(*
   本节说明 ProbeQuiverConstructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition control_op (C : Category) :
  QuiverOfCat (C^op) = QuiverOp (QuiverOfCat C) := eq_refl.

Definition control_prod (C D : Category) :
  QuiverOfCat (C ∏ D) = QuiverProd (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

Definition control_invol (G : Quiver) : QuiverOp (QuiverOp G) = G := eq_refl.

(** ** Negative probes: the boundary.

    These must FAIL.  Each is the [eq_refl] strengthening of a statement that
    Constructions.v delivers at [≈]. *)

(* [Fst]/[Snd] are [Program Instance]s: [fmap_respects] is opaque. *)
Fail Definition probe_fst_strict (C D : Category) :
  QuiverHomomorphismOfFunctor _ _ (@Fst C D)
    = @QuiverFst (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

Fail Definition probe_snd_strict (C D : Category) :
  QuiverHomomorphismOfFunctor _ _ (@Snd C D)
    = @QuiverSnd (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

(* Surjective pairing is not definitional for [prod]. *)
Fail Definition probe_swap_invol_strict (G H : Quiver) :
  @compose QuiverCategory (QuiverProd G H) (QuiverProd H G) (QuiverProd G H)
    QuiverSwap QuiverSwap
    = @id QuiverCategory (QuiverProd G H) := eq_refl.

(*
   本节说明 ProbeQuiverConstructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition QuiverProd_alt (G H : Quiver) : Quiver := {|
  nodes   := (@nodes G * @nodes H)%type;
  edges   := fun x y =>
    (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type;
  edgeset := fun x y =>
    @prod_setoid _ _ (@edgeset G (fst x) (fst y)) (@edgeset H (snd x) (snd y))
|}.

Fail Definition probe_prod_setoid_strict (C D : Category) :
  QuiverOfCat (C ∏ D) = QuiverProd_alt (QuiverOfCat C) (QuiverOfCat D)
    := eq_refl.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Definition probe_pair_eta_strict {G H K : Quiver}
  (M : QuiverHomomorphism K (QuiverProd G H)) :
  QuiverPair (@compose QuiverCategory _ _ _ QuiverFst M)
             (@compose QuiverCategory _ _ _ QuiverSnd M) = M := eq_refl.
