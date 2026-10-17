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
   The lax 变换 class, at full strength.  Its data are the component

   本节说明相关定义、性质与动机。 1-cells [lt0] naturator 2-cells [lt1]; its laws are naturality naturator 2-cells [lt1_自然], unit coherence [lt_unit], 复合 coherence [lt_comp].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class LaxTransformation {B B' : Bicategory} (F G : Pseudofunctor B B') := {
  (* component 1-cells α_x : F x ~~> G x *)
  lt0 (x : @bi0cell B) : @bicat B' (pf0 F x) (pf0 G x);

  (* naturator 2-cells, in the lax orientation *)
  lt1 {x y : @bi0cell B} (f : @bicat B x y) :
    pf1[G] f ∘∘∘ lt0 x
      ~{ @bicat B' (pf0 F x) (pf0 G y) }~> lt0 y ∘∘∘ pf1[F] f;

  (* the naturator is natural in f: for a 2-cell μ : f ⟹ f', the square built
     from lt1 f, lt1 f' and the whiskerings of G μ and F μ commutes. *)
  lt1_natural {x y : @bi0cell B} {f f' : @bicat B x y}
      (μ : f ~{ @bicat B x y }~> f') :
    lt1 f' ∘∘ hcomp2 (fmap[pf1[G]] μ) (bi2id (a:=lt0 x))
      ≈ hcomp2 (bi2id (a:=lt0 y)) (fmap[pf1[F]] μ) ∘∘ lt1 f;

  (* unit coherence: the naturator at the identity 1-cell, conjugated by the
     unit isos pf_id of F and G, agrees with the comparison of the two unitors
     on the component 1-cell. *)
  lt_unit (x : @bi0cell B) :
    hcomp2 (bi2id (a:=lt0 x)) (to (@pf_id _ _ F x))
      ∘∘ lt1 (@bi1id B x)
      ∘∘ hcomp2 (from (@pf_id _ _ G x)) (bi2id (a:=lt0 x))
    ≈ from (hunit_right (lt0 x)) ∘∘ to (hunit_left (lt0 x));

  (*
   复合 coherence: the naturator at a 复合 g ∘∘∘ f, conjugated by

   本节说明相关定义、性质与动机。 the compositors pf_comp F G, agrees pasting two naturators lt1 g lt1 f re-bracketed 结合子 B'.

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
   The oplax 变换 class: the dual of [LaxTransformation], with every

   本节说明相关定义、性质与动机。 naturator 2-cell reversed. The naturator now points olt1 f : olt0 y ∘∘∘ pf1[F] f ⟹ pf1[G] f ∘∘∘ olt0 x, three coherence axioms are mirror images lax ones (the unit 复合 laws associators inverted unitor comparison reversed).

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
   A lax 变换 is *pseudonatural* when every naturator 2-cell is

   本节说明相关定义、性质与动机。 invertible. This is mixin over [LaxTransformation]: it exposes, each 1-cell f, witness that [lt1 σ f] is 同构 hom-范畴 B', hence two-sided inverse its 消去 laws via [IsIsomorphism].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Pseudonatural {B B' : Bicategory} {F G : Pseudofunctor B B'}
      (σ : LaxTransformation F G) := {
  pn_iso {x y : @bi0cell B} (f : @bicat B x y) : IsIsomorphism (lt1 σ f)
}.

Arguments pn_iso {B B' F G σ} _ {x y} f.

(** Inhabitation witness. *)

(*
   To witness that the 变换 classes are inhabited "closed under the

   本节说明相关定义、性质与动机。 global context", we exhibit them terminal 双范畴: one 0-cell, one 1-cell, one 2-cell, codiscrete 2-cell setoid which every 2-cell equation holds.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The codiscrete setoid on [unit]: any two elements are related. *)
Program Definition triv_setoid : Setoid unit := {| equiv := fun _ _ => True |}.

(* The terminal bicategory.  All data are the unique inhabitant [tt]; every law
   is an equation in the codiscrete hom-setoid, hence holds. *)
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
   本节说明相关定义、性质与动机。 the codiscrete equations, two whiskering naturalities two. coherence laws all reduce [True];

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
   The identity lax 变换 on the terminal 双范畴 (via the identity

   本节说明相关定义、性质与动机。 伪函子): all components naturators are unique [tt], all three coherence laws hold codiscrete setoid.

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

(* The oplax dual is inhabited on the same terminal bicategory. *)
Program Definition Trivial_OplaxTransformation :
  OplaxTransformation (Identity_Pseudofunctor Trivial_Bicategory)
                      (Identity_Pseudofunctor Trivial_Bicategory) := {|
  olt0 := fun _ => tt;
  olt1 := fun _ _ _ => tt
|}.

