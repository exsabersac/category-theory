(*
   本文件为测试：FullIssue118。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Id_Full_build (C : Category) : Full (Id[C]) :=
  Build_Full _ _ Id[C]
    (fun x y (g : Id[C] x ~> Id[C] y) => g)
    (fun x y (g : Id[C] x ~> Id[C] y) => reflexivity g).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Full_from_section
  `(F : C ⟶ D)
  (pre : ∀ x y, F x ~> F y → x ~> y)
  (sec : ∀ x y (g : F x ~> F y), fmap[F] (pre x y g) ≈ g) : Full F :=
  {| prefmap x y g := pre x y g
   ; fmap_sur x y g := sec x y g |}.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Id_Full {C : Category} : Full (@Id C) :=
  Full_from_section Id (fun _ _ g => g) (fun _ _ g => reflexivity g).

(** Register an instance so resolution of the leaner class is exercised too. *)
#[local] Existing Instance Id_Full.

(** The two surviving projections, expected types under the
 corrected 定义. （已译） *)
Check @prefmap.
Check @fmap_sur.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Program Instance Id_Faithful (C : Category) : Faithful (Id[C]) := {|
  fmap_inj := fun x y (f g : x ~> y) (H : f ≈ g) => H
|}.

Definition FullyFaithful_under_lean_Full
  `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F} :
  ∀ x y, F x ≅ F y → x ≅ y := FullyFaithful F.

(** Pin a concrete instantiation as well, independent of implicit inference. *)
Check (fun C : Category =>
         @FullyFaithful C C Id[C] (Id_Full_build C) (Id_Faithful C)).
