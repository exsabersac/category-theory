Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Section SemicartesianMonoidal.

Context {C : Category}.

(*
   Wikipedia: no dedicated article; the notion is described under

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class SemicartesianMonoidal `{@Monoidal C} := {
  (* 相关说明。 （已译） *)
  eliminate {x} : x ~> I;

  (* uniqueness of maps into I, i.e. I is terminal (up to ≈) *)
  unit_terminal {x} (f g : x ~> I) : f ≈ g;

  (* left  projection x ⨂ y ~> x: discard y, then the right unitor *)
  proj_left  {x y} : x ⨂ y ~> x := unit_right ∘ id ⨂ eliminate;
  (* right projection x ⨂ y ~> y: discard x, then the left  unitor *)
  proj_right {x y} : x ⨂ y ~> y := unit_left  ∘ eliminate ⨂ id
}.

(* 相关说明。 （已译） *)

Corollary eliminate_comp `{@Monoidal C} `{@SemicartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

End SemicartesianMonoidal.

Require Import Category.Structure.Terminal.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Semicartesian monoidal ==> I 终对象, eliminate the
 唯一箭头 unit_terminal uniqueness 证明. （已译） *)

Program Definition SemicartesianMonoidal_Terminal `{@Monoidal C}
        `{@SemicartesianMonoidal C _} : @Terminal C := {|
  terminal_obj := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.

Import EqNotations.

(*
   本节说明幺半结构、幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Terminal_SemicartesianMonoidal `{M : @Monoidal C}
        `{T : @Terminal C} (Heq : 1 = @I C M) :
  @SemicartesianMonoidal C _ := {|
  eliminate := fun x => rew Heq in one;
  unit_terminal := fun x f g =>
    _ (one_unique (rew <- Heq in f) (rew <- Heq in g))
|}.
Next Obligation.
  unfold eq_rect_r, eq_rect, eq_sym in x.
  destruct Heq.
  assumption.
Defined.
