Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Pseudofunctor.

Generalizable All Variables.

(** Lax and oplax transformations between pseudofunctors. *)

(*
 nLab: https://ncatlab.org/nlab/show/lax+natural+transformation
   nLab: https://ncatlab.org/nlab/show/pseudonatural+transformation
   Reference: Johnson–Yau, "2-Dimensional Categories", Definition 4.2.1.

   本文件给出松弛（lax）结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class LaxTransformation {B B' : Bicategory} (F G : Pseudofunctor B B') := {
  (* component 1-cells α_x : F x ~~> G x *)
  lt0 (x : @bi0cell B) : @bicat B' (pf0 F x) (pf0 G x);

  (* naturator 2-cells, in the lax orientation *)
  lt1 {x y : @bi0cell B} (f : @bicat B x y) :
    pf1[G] f ∘∘∘ lt0 x
      ~{ @bicat B' (pf0 F x) (pf0 G y) }~> lt0 y ∘∘∘ pf1[F] f;

  (* 相关说明。 （已译） *)
  lt1_natural {x y : @bi0cell B} {f f' : @bicat B x y}
      (μ : f ~{ @bicat B x y }~> f') :
    lt1 f' ∘∘ hcomp2 (fmap[pf1[G]] μ) (bi2id (a:=lt0 x))
      ≈ hcomp2 (bi2id (a:=lt0 y)) (fmap[pf1[F]] μ) ∘∘ lt1 f;

  (* unit coherence: naturator at 恒等 1-cell, conjugated the
 unit isos pf_id F G, agrees comparison two unitors
 component 1-cell. （已译） *)
  lt_unit (x : @bi0cell B) :
    hcomp2 (bi2id (a:=lt0 x)) (to (@pf_id _ _ F x))
      ∘∘ lt1 (@bi1id B x)
      ∘∘ hcomp2 (from (@pf_id _ _ G x)) (bi2id (a:=lt0 x))
    ≈ from (hunit_right (lt0 x)) ∘∘ to (hunit_left (lt0 x));

  (*
   本节说明 Lax 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  lt_comp {x y z : @bi0cell B} (g : @bicat B y z) (f : @bicat B x y) :
    hcomp2 (bi2id (a:=lt0 z)) (to (@pf_comp _ _ F x y z g f))
      ∘∘ lt1 (g ∘∘∘ f)
      ∘∘ hcomp2 (from (@pf_comp _ _ G x y z g f)) (bi2id (a:=lt0 x))
    ≈ to (hassoc (lt0 z) (pf1[F] g) (pf1[F] f))
      ∘∘ hcomp2 (lt1 g) (bi2id (a:=pf1[F] f))
      ∘∘ from (hassoc (pf1[G] g) (lt0 y) (pf1[F] f))
      ∘∘ hcomp2 (bi2id (a:=pf1[G] g)) (lt1 f)
      ∘∘ to (hassoc (pf1[G] g) (pf1[G] f) (lt0 x))
}.

Arguments lt0 {B B'} {F G} _ x.
Arguments lt1 {B B'} {F G} _ {x y} f.
Arguments lt1_natural {B B'} {F G} _ {x y f f'} μ.
Arguments lt_unit {B B'} {F G} _ x.
Arguments lt_comp {B B'} {F G} _ {x y z} g f.

(*
   本节说明 Lax 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class OplaxTransformation {B B' : Bicategory} (F G : Pseudofunctor B B') := {
  (* component 1-cells α_x : F x ~~> G x *)
  olt0 (x : @bi0cell B) : @bicat B' (pf0 F x) (pf0 G x);

  (* naturator 2-cells, in the oplax (reversed) orientation *)
  olt1 {x y : @bi0cell B} (f : @bicat B x y) :
    olt0 y ∘∘∘ pf1[F] f
      ~{ @bicat B' (pf0 F x) (pf0 G y) }~> pf1[G] f ∘∘∘ olt0 x;

  olt1_natural {x y : @bi0cell B} {f f' : @bicat B x y}
      (μ : f ~{ @bicat B x y }~> f') :
    olt1 f' ∘∘ hcomp2 (bi2id (a:=olt0 y)) (fmap[pf1[F]] μ)
      ≈ hcomp2 (fmap[pf1[G]] μ) (bi2id (a:=olt0 x)) ∘∘ olt1 f;

  olt_unit (x : @bi0cell B) :
    hcomp2 (to (@pf_id _ _ G x)) (bi2id (a:=olt0 x))
      ∘∘ olt1 (@bi1id B x)
      ∘∘ hcomp2 (bi2id (a:=olt0 x)) (from (@pf_id _ _ F x))
    ≈ from (hunit_left (olt0 x)) ∘∘ to (hunit_right (olt0 x));

  olt_comp {x y z : @bi0cell B} (g : @bicat B y z) (f : @bicat B x y) :
    hcomp2 (to (@pf_comp _ _ G x y z g f)) (bi2id (a:=olt0 x))
      ∘∘ olt1 (g ∘∘∘ f)
      ∘∘ hcomp2 (bi2id (a:=olt0 z)) (from (@pf_comp _ _ F x y z g f))
    ≈ from (hassoc (pf1[G] g) (pf1[G] f) (olt0 x))
      ∘∘ hcomp2 (bi2id (a:=pf1[G] g)) (olt1 f)
      ∘∘ to (hassoc (pf1[G] g) (olt0 y) (pf1[F] f))
      ∘∘ hcomp2 (olt1 g) (bi2id (a:=pf1[F] f))
      ∘∘ from (hassoc (olt0 z) (pf1[F] g) (pf1[F] f))
}.

Arguments olt0 {B B'} {F G} _ x.
Arguments olt1 {B B'} {F G} _ {x y} f.
Arguments olt1_natural {B B'} {F G} _ {x y f f'} μ.
Arguments olt_unit {B B'} {F G} _ x.
Arguments olt_comp {B B'} {F G} _ {x y z} g f.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Pseudonatural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) := {
  pn_iso {x y : @bi0cell B} (f : @bicat B x y) : IsIsomorphism (lt1 σ f)
}.

Arguments pn_iso {B B' F G σ} _ {x y} f.

(** Inhabitation witness. *)

(*
   本节说明双范畴、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Program Definition triv_setoid : Setoid unit := {| equiv := fun _ _ => True |}.

(* 相关说明。 （已译） *)
Definition Trivial_Bicategory : Bicategory.
Proof.
  unshelve refine (Build_Bicategory'
    unit                            (* bi0cell *)
    (fun _ _ => unit)               (* bi1cell *)
    (fun _ _ _ _ => unit)           (* bi2cell *)
    (fun _ => tt)                   (* bi1id *)
    (fun _ _ _ _ => triv_setoid)    (* bi2homset *)
    (fun _ _ _ => tt)               (* bi2id *)
    (fun _ _ _ _ _ _ _ => tt)       (* vcompose *)
    _ _ _ _                         (* vcompose_respects, bi2id_left/right, vcompose_assoc *)
    _                               (* hcompose *)
    _ _ _                           (* hunit_left, hunit_right, hassoc *)
    _ _ _                           (* hunit_left/right/hassoc naturality *)
    _ _).                           (* triangle, pentagon *)
  (*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  all: try (repeat intro; exact I).
  - (* hcompose : the horizontal-composition functor *)
    intros x y z.
    unshelve eapply Build_Functor.
    + exact (fun _ => tt).
    + exact (fun _ _ _ => tt).
    + repeat intro; exact I.
    + repeat intro; exact I.
    + repeat intro; exact I.
  - (* hunit_left *)
    intros x y f.
    unshelve eapply Build_Isomorphism; try exact tt; exact I.
  - (* hunit_right *)
    intros x y f.
    unshelve eapply Build_Isomorphism; try exact tt; exact I.
  - (* hassoc *)
    intros w x y z h g f.
    unshelve eapply Build_Isomorphism; try exact tt; exact I.
Defined.

(*
   本节说明双范畴、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Trivial_LaxTransformation :
  LaxTransformation (Identity_Pseudofunctor Trivial_Bicategory)
                    (Identity_Pseudofunctor Trivial_Bicategory) := {|
  lt0 := fun _ => tt;
  lt1 := fun _ _ _ => tt
|}.

(* Its naturators are (trivially) invertible, so it is pseudonatural. *)
Program Definition Trivial_Pseudonatural :
  Pseudonatural Trivial_LaxTransformation := {|
  pn_iso := fun _ _ _ => {| two_sided_inverse := tt |}
|}.

(* 相关说明。 （已译） *)
Program Definition Trivial_OplaxTransformation :
  OplaxTransformation (Identity_Pseudofunctor Trivial_Bicategory)
                      (Identity_Pseudofunctor Trivial_Bicategory) := {|
  olt0 := fun _ => tt;
  olt1 := fun _ _ _ => tt
|}.

