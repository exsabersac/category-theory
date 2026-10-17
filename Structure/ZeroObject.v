Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Zero objects and zero morphisms *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class ZeroObject (C : Category) := {
  zero_terminal : @Terminal C;
  zero_initial  : @Initial C;

  (*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  zero_coincide : @initial_obj C zero_initial ≅ @terminal_obj C zero_terminal
}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition zero_obj {C : Category} `{Z : @ZeroObject C} : C :=
  @terminal_obj C zero_terminal.

(* The zero morphism x ~> y: into 1, across the coincidence iso, out of 0. *)
Definition zero_mor {C : Category} `{Z : @ZeroObject C} {x y : C} : x ~> y :=
  @zero C (@zero_initial C Z) y
    ∘ from (@zero_coincide C Z)
    ∘ @one C (@zero_terminal C Z) x.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zero_mor_left {C : Category} `{Z : @ZeroObject C} {x y z : C}
  (f : y ~> z) :
  f ∘ @zero_mor C Z x y ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite !comp_assoc.
  now rewrite (@zero_comp C (@zero_initial C Z) y z f).
Qed.

(* Precomposition absorbs: 0 ∘ f ≈ 0.  Dually, after reassociation the
   composite one ∘ f is a morphism into the terminal object, so [one_comp]
   collapses it to one. *)
Lemma zero_mor_right {C : Category} `{Z : @ZeroObject C} {x y z : C}
  (f : x ~> y) :
  @zero_mor C Z y z ∘ f ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite <- !comp_assoc.
  now rewrite (@one_comp C (@zero_terminal C Z) x y f).
Qed.

(* Any morphism factoring through the zero object is the zero morphism:
   the leg into 1 is unique by [one_unique], and the leg out of 0 is
   unique by [zero_unique]. *)
Lemma zero_mor_unique {C : Category} `{Z : @ZeroObject C} {x y : C}
  (g : x ~> @terminal_obj C (@zero_terminal C Z))
  (h : @initial_obj C (@zero_initial C Z) ~> y) :
  (h ∘ from (@zero_coincide C Z)) ∘ g ≈ zero_mor.
Proof.
  unfold zero_mor.
  rewrite (@one_unique C (@zero_terminal C Z) x g
             (@one C (@zero_terminal C Z) x)).
  rewrite (@zero_unique C (@zero_initial C Z) y h
             (@zero C (@zero_initial C Z) y)).
  reflexivity.
Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition zero_object_unique {C : Category} (Z1 Z2 : ZeroObject C) :
  @terminal_obj C (@zero_terminal C Z1) ≅ @terminal_obj C (@zero_terminal C Z2) :=
  terminal_unique (@zero_terminal C Z1) (@zero_terminal C Z2).

(* The same statement read through the chosen initial objects. *)
Program Definition zero_object_unique_initial {C : Category}
      (Z1 Z2 : ZeroObject C) :
  @initial_obj C (@zero_initial C Z1) ≅ @initial_obj C (@zero_initial C Z2) :=
  initial_unique (@zero_initial C Z1) (@zero_initial C Z2).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zero_object_unique_compat {C : Category} (Z1 Z2 : ZeroObject C) :
  to (@zero_coincide C Z2) ∘ to (zero_object_unique_initial Z1 Z2)
    ≈ to (zero_object_unique Z1 Z2) ∘ to (@zero_coincide C Z1).
Proof. apply (@zero_unique C (@zero_initial C Z1)). Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary zero_object_arrow_unique {C : Category} (Z1 Z2 : ZeroObject C)
      (f g : @terminal_obj C (@zero_terminal C Z1)
               ~> @terminal_obj C (@zero_terminal C Z2)) : f ≈ g.
Proof. apply (@one_unique C (@zero_terminal C Z2)). Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition terminal_initial_arrow_iso {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) :
  @terminal_obj C T ≅ @initial_obj C I := {|
  to   := f;
  from := @one C T (@initial_obj C I)
|}.
Next Obligation. apply (@zero_unique C I). Qed.
Next Obligation. apply (@one_unique C T). Qed.

(* The same fact as a predicate on the given morphism. *)
Program Definition terminal_initial_arrow_is_iso {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) : IsIsomorphism f := {|
  two_sided_inverse := @one C T (@initial_obj C I)
|}.
Next Obligation. apply (@zero_unique C I). Qed.
Next Obligation. apply (@one_unique C T). Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ZeroObject_from_arrow {C : Category}
  (T : @Terminal C) (I : @Initial C)
  (f : @terminal_obj C T ~> @initial_obj C I) : ZeroObject C := {|
  zero_terminal := T;
  zero_initial  := I;
  zero_coincide := iso_sym (terminal_initial_arrow_iso T I f)
|}.
