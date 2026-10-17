Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Theory.Bicategory.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Theory.Concrete.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Finite.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Functor.Construction.Postcompose.

Generalizable All Variables.

(** * Probes guarding Functor/Construction/Postcompose.v *)

(*
   本文件为测试：ProbePostcompose。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Group 1 (CONVERSION): the Hcompose route's arrow action *)

Section HcomposeConversion.

Context {D E E' : Category}.
Context (J : E ⟶ E').
Context (K L : D ⟶ E).
Context (θ : K ⟹ L).

(* POSITIVE CONTROL 1.  The OBJECT actions of the two routes DO agree on the
   nose, so the instrument is not simply rejecting everything about
   [PostcomposeViaHcompose]. *)
Definition control_hcompose_obj :
  fobj[PostcomposeViaHcompose J] K = fobj[Postcompose J] K := eq_refl.

(* POSITIVE CONTROL 2.  The Hcompose route's component IS
   [fmap[J] id ∘ fmap[J] (θ x)] on the nose — this is what the negative
   below is measuring the presence of. *)
Definition control_hcompose_component (x : D) :
  transform[fmap[PostcomposeViaHcompose J] θ] x
    = fmap[J] (@id E (L x)) ∘ fmap[J] (transform[θ] x) := eq_refl.

(*
   本节说明 ProbePostcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition negative_hcompose_fmap :
  fmap[PostcomposeViaHcompose J] θ = fmap[Postcompose J] θ := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition negative_hcompose_functor :
  PostcomposeViaHcompose J = Postcompose J := eq_refl.

(* NEGATIVE 3 (conversion).  Not even componentwise at a fixed x. *)
Fail Definition negative_hcompose_component (x : D) :
  transform[fmap[PostcomposeViaHcompose J] θ] x
    = transform[fmap[Postcompose J] θ] x := eq_refl.

(* POSITIVE CONTROL 3.  All three hold up to `≈`, which is the strength the
   library file claims. *)
Definition control_hcompose_equiv :
  fmap[PostcomposeViaHcompose J] θ ≈ fmap[Postcompose J] θ :=
  postcompose_via_hcompose_fmap J K L θ.

End HcomposeConversion.

(** ** Group 2 (CONVERSION): [prefmap] does not compute *)

Section PrefmapConversion.

(* POSITIVE CONTROL 4.  The FORWARD leg of the isomorphism computes: it is
   the functor's own action on 2-cells, on the nose. *)
Definition control_iso_to (θ : finpost_K ⟹ finpost_K) :
  to finpost_hom_iso θ = fmap[SubPostcompose FinSets] θ := eq_refl.

(*
   本节说明 ProbePostcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition negative_prefmap_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x = FinSets_negb := eq_refl.

(* POSITIVE CONTROL 5.  It does hold up to `≈`, by [fmap_sur]. *)
Definition control_prefmap_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x ≈ FinSets_negb :=
  finpost_preimage_component x.

(*
   本节说明 ProbePostcompose 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition negative_roundtrip :
  from finpost_hom_iso (to finpost_hom_iso finpost_theta) = finpost_theta
    := eq_refl.

(* POSITIVE CONTROL 6.  The round trip at `≈`, which IS what
   [postcompose_hom_iso] proves. *)
Definition control_roundtrip :
  from finpost_hom_iso (to finpost_hom_iso finpost_theta) ≈ finpost_theta :=
  iso_from_to finpost_hom_iso finpost_theta.

End PrefmapConversion.

(** ** Group 3 (FORMABILITY): the hom universes cannot be kept apart *)

(* [Postcompose] identifies the hom AND proof universes of all three of its
   categories.  The object universes stay free.  Both halves are probed. *)

Section UniverseFormability.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section ObjectsFree.
  Universes uo1 uo2 uo3 uh.
  Constraint uo1 < uo2.
  Constraint uo2 < uo3.

  Check (fun (D : Category@{uo1 uh uh}) (E : Category@{uo2 uh uh})
             (E' : Category@{uo3 uh uh}) (J : E ⟶ E') =>
           @Postcompose D E E' J).
End ObjectsFree.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section HomsApart.
  Universes uo uh1 uh2.
  Constraint uh1 < uh2.

  Fail Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh1 uh1})
                  (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
                @Postcompose D E E' J).
End HomsApart.

(* NEGATIVE 7 (formability).  Same for the SHAPE category's hom universe
   against the two others. *)
Section ShapeHomApart.
  Universes uo uh1 uh2.
  Constraint uh1 < uh2.

  Fail Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh2 uh2})
                  (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
                @Postcompose D E E' J).
End ShapeHomApart.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section HomsTogether.
  Universes uo uh1 uh2.

  Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh1 uh1})
             (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
           @Postcompose D E E' J).
End HomsTogether.

End UniverseFormability.

(** ** Group 4 (FORMABILITY): the enlargement of Sets is out of reach *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsEnlargement.

(* NEGATIVE 8 (formability).  [Postcompose] along the lift. *)
Fail Check (fun (D : Category) => Postcompose (D:=D) Sets_Lift).

(* NEGATIVE 9 (formability).  And already the bare object action, with no
   functor category and no [Postcompose] in sight — which is what shows the
   wall belongs to [Compose]. *)
Fail Check (fun (D : Category) (K : D ⟶ Sets) => Sets_Lift ◯ K).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Sets_Lift.

Check (fun (D : Category) (K : D ⟶ Sets) => (Id[Sets]) ◯ K).

End SetsEnlargement.

(** ** Group 5: the headline results are inhabited at the witness *)

(* POSITIVE CONTROLS 11 and 12.  The two boundary theorems of the library
   file, each named at its full type, so that a rename or a weakening of
   either statement breaks this file. *)

Definition control_finpost_iso :
  (finpost_K ⟹ finpost_K)
    ≊ (FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K) :=
  finpost_hom_iso.

Definition control_full_needed :
  Category.Theory.Functor.Full (Postcompose (D:=_1) DiscToTwo) → False :=
  postcompose_full_needs_full.
