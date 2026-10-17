Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

Section SemicocartesianMonoidal.

Context {C : Category}.

(*
   Wikipedia: no dedicated article; the dual notion is described under

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class SemicocartesianMonoidal `{@Monoidal C} := {
  (* the create / coprojection-from-unit map, the unique I ~> x *)
  generate {x} : I ~> x;

  (* uniqueness of maps out of I, i.e. I is initial (up to ≈) *)
  unit_initial {x} (f g : I ~> x) : f ≈ g;

  (* left  coprojection x ~> x ⨂ y: undo the right unitor, then create y *)
  embed_left  {x y} : x ~> x ⨂ y := id ⨂ generate ∘ unit_right⁻¹;
  (* right coprojection y ~> x ⨂ y: undo the left  unitor, then create x *)
  embed_right {x y} : y ~> x ⨂ y := generate ⨂ id ∘ unit_left⁻¹
}.

(* Creating before any map is creating: generate is natural, since both sides
   are maps I ~> B and I is initial. Dual of eliminate_comp. *)

Corollary generate_comp `{@Monoidal C} `{@SemicocartesianMonoidal _} `{f : A ~> B} :
  f ∘ generate ≈ generate.
Proof. intros; apply unit_initial. Qed.

End SemicocartesianMonoidal.

Require Import Category.Structure.Initial.

(*
   https://en.wikipedia.org/wiki/Cartesian_monoidal_category : a cocartesian

   本节说明幺半结构、幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition SemicocartesianMonoidal_Initial `{@Monoidal C}
        `{@SemicocartesianMonoidal C _} : @Initial C := {|
  terminal_obj := @I C _;
  one := @generate _ _ _;
  one_unique := @unit_initial _ _ _
|}.

Import EqNotations.

(*
   本节说明幺半结构、幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Initial_SemicocartesianMonoidal `{M : @Monoidal C}
        `{T : @Initial C} (Heq : @initial_obj C T = @I C M) :
  @SemicocartesianMonoidal C _ := {|
  generate := fun x => _ (@zero C T x);
  unit_initial := fun x f g => _ (@zero_unique C T x) f g
|}.
Next Obligation. rewrite Heq in x0; apply x0. Defined.
