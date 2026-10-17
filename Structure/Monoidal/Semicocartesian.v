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

(* The two directions below witness that "semicocartesian monoidal" and "the
   unit I is initial" are the same condition, packaged as an Initial structure
   on I and as a SemicocartesianMonoidal structure respectively. Cf. Wikipedia,
   https://en.wikipedia.org/wiki/Cartesian_monoidal_category : a cocartesian
   monoidal category has "the monoidal structure given by the coproduct and
   unit the initial object."

   Semicocartesian monoidal ==> I is an initial object, with generate as the
   unique arrow and unit_initial as its uniqueness proof. *)

Program Definition SemicocartesianMonoidal_Initial `{@Monoidal C}
        `{@SemicocartesianMonoidal C _} : @Initial C := {|
  terminal_obj := @I C _;
  one := @generate _ _ _;
  one_unique := @unit_initial _ _ _
|}.

Import EqNotations.

(* Conversely, a monoidal category whose initial object 0 coincides with the
   unit object I (the hypothesis Heq : 0 = I) is semicocartesian monoidal:
   transport the unique arrow `zero` along Heq to obtain generate, and
   transport zero_unique to obtain unit_initial. *)

Program Definition Initial_SemicocartesianMonoidal `{M : @Monoidal C}
        `{T : @Initial C} (Heq : @initial_obj C T = @I C M) :
  @SemicocartesianMonoidal C _ := {|
  generate := fun x => _ (@zero C T x);
  unit_initial := fun x f g => _ (@zero_unique C T x) f g
|}.
Next Obligation. rewrite Heq in x0; apply x0. Defined.
