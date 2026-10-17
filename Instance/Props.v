Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The category PROP of propositions *)

(*
 nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Heyting_algebra

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Props : Category := {|
  obj     := Prop;                         (* objects are propositions *)
  hom     := Basics.impl;                  (* P ~> Q is the implication P → Q *)
  (*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  homset  := fun P Q => {| equiv := fun f g => True |};
  id      := fun _ x => x;                 (* identity implication P → P *)
  compose := fun _ _ _ g f x => g (f x)    (* transitivity of implication *)
|}.

(* Terminal object: True is the top proposition, with `I : True` giving the
   unique map P ~> True (every P implies True). *)
#[export]
Program Instance Props_Terminal : @Terminal Props := {
  terminal_obj := True;                    (* 1 = True *)
  one := fun _ _ => I                       (* ! : P → True *)
}.

(* Initial object: False is the bottom proposition; ex falso quodlibet gives
   the unique map False ~> P (False implies every P). *)
#[export]
Program Instance Props_Initial : @Initial Props := {
  terminal_obj := False;                   (* 0 = False (terminal in Props^op) *)
  one := fun _ _ => False_rect _ _          (* ¡ : False → P, by ex falso *)
}.

(* Product: conjunction. P ∧ Q is the meet, with proj1/proj2 the projections
   and conj the pairing of two implications. *)
#[export]
Program Instance Props_Cartesian : @Cartesian Props := {
  product_obj := and;                      (* P × Q = P ∧ Q *)
  fork := fun _ _ _ f g x => conj (f x) (g x);  (* ⟨f, g⟩ : R → P ∧ Q *)
  exl  := fun _ _ p => proj1 p;            (* first projection  P ∧ Q → P *)
  exr  := fun _ _ p => proj2 p             (* second projection P ∧ Q → Q *)
}.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Props_Cocartesian : @Cocartesian Props := {
  product_obj := or;                       (* P + Q = P ∨ Q *)
  fork := fun _ _ _ f g x =>               (* copairing [f, g] : P ∨ Q → R *)
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun _ _ p => or_introl p;        (* left injection  P → P ∨ Q *)
  exr  := fun _ _ p => or_intror p         (* right injection Q → P ∨ Q *)
}.

(* Exponential: implication. Q ^ P = P → Q, and exp_iso is the currying
   bijection Hom(R ∧ P, Q) ≅ Hom(R, P → Q) witnessing (- ∧ P) ⊣ (P → -). *)
#[export]
Program Instance Props_Closed : @Closed Props _ := {
  exponent_obj := Basics.impl;             (* Q ^ P = P → Q *)
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.
