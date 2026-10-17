Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   初始对象 `0` 是这样的对象：对每个对象 `x` 配备态射 `zero : 0 ~> x`（文献写作 `¡`），
   服从普遍映射性质：该态射唯一，任意两态射 `0 ~> x` 相等（zero_unique）。这恰是终对象
   的对偶：C 中的初始对象是 C^op 中的终对象，所有箭头反向。`one : x ~> 1` 的对偶是
   `zero : 0 ~> x`。既初始又终结的对象是零对象。 *)

(* 初始对象从何而来，以及用途为何

   Wikipedia: https://en.wikipedia.org/wiki/Universal_property
   nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   nLab:      https://ncatlab.org/nlab/show/empty+type

   初始对象是最纯粹的普遍性质种：对象不由任何内部结构刻画，而仅由其与其他一切的关系刻画。
   此类普遍映射性质由 Pierre Samuel 于 1948 年为拓扑构造提出，随后被 Bourbaki 广泛使用，
   比 Kan 1958 年独立引入密切相关的伴随函子概念早十年（Wikipedia, "Universal property"）。
   初始对象是整个余极限理论的空情形——空图的余极限，等价于零元余积——这正是
   Structure/Cocartesian.v 的单位律 [coprod_zero_l] 与 [coprod_zero_r] 把 0 展示为余积单位的原因。
   任意两初始对象由唯一同构同构，而每个普遍构造共有的这种唯一同构下的唯一性，使我们可以说
   「那个」初始对象（Milewski, "Products and Coproducts", 2015）。 *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

(* The initial object `0` itself (terminal in C^op).         *)
Definition initial_obj : C := @terminal_obj _ I.

(* The unique 态射 `¡ : 0 ~> x` (`one` C^op). （已译） *)
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

(* Uniqueness: any two morphisms out of `0` are equivalent.   *)
Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
  @one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

(* Postcomposing the unique morphism `0 ~> x` is again unique (dual of
   one_comp): any `f ∘ zero` is forced to equal `zero` by zero_unique. *)
Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≈ zero.
Proof. apply (@one_comp _ T). Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition initial_unique {C : Category} (I1 I2 : @Initial C) :
  @initial_obj C I1 ≅ @initial_obj C I2 := {|
  to   := @zero C I1 (@initial_obj C I2);
  from := @zero C I2 (@initial_obj C I1)
|}.
Next Obligation. apply (@zero_unique C I2). Qed.
Next Obligation. apply (@zero_unique C I1). Qed.

(* And it arrow between them, so 同构 canonical --
 "unique 同构" half Mac Lane's statement, dual to
 [terminal_arrow_unique]. （已译） *)
Corollary initial_arrow_unique {C : Category} (I1 I2 : @Initial C)
      (f g : @initial_obj C I1 ~> @initial_obj C I2) : f ≈ g.
Proof. apply (@zero_unique C I1). Qed.

(*
   本节说明同构、始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsInitialObj {C : Category} (c : C) : Type :=
  @IsTerminalObj (C^op) c.

Definition is_initial_zero {C : Category} {c : C} (H : IsInitialObj c)
  {x : C} : c ~> x := @is_terminal_one (C^op) c H x.

Definition is_initial_unique {C : Category} {c : C} (H : IsInitialObj c)
  {x : C} (f g : c ~> x) : f ≈ g := @is_terminal_unique (C^op) c H x f g.

Definition Initial_from_IsInitialObj {C : Category} {c : C}
  (H : IsInitialObj c) : @Initial C :=
  @Terminal_from_IsTerminalObj (C^op) c H.

Definition IsInitialObj_from_Initial {C : Category} (I : @Initial C) :
  IsInitialObj (@initial_obj C I) :=
  @IsTerminalObj_from_Terminal (C^op) I.

(* Riehl, CTiC, Exercise 1.6.ii(i), initial half. [Isomorphism_Opposite]
 (Construction/Opposite.v) re-reads C-同构 C^op, and
 [Terminal_iso] at C^op whole 证明. （已译） *)
Definition Initial_iso {C : Category} (I : @Initial C) (y : C)
  (i : @initial_obj C I ≅ y) : @Initial C :=
  @Terminal_iso (C^op) I y (Isomorphism_Opposite i).

(* The transported structures choose new 对象 definitionally, which
 what makes them usable transports rather than bare existence
 statements. （已译） *)
Corollary Terminal_iso_obj {C : Category} (T : @Terminal C) (y : C)
  (i : @terminal_obj C T ≅ y) : @terminal_obj C (Terminal_iso T y i) = y.
Proof. reflexivity. Qed.

Corollary Initial_iso_obj {C : Category} (I : @Initial C) (y : C)
  (i : @initial_obj C I ≅ y) : @initial_obj C (Initial_iso I y i) = y.
Proof. reflexivity. Qed.

(* The dual [terminal_unique_up_to_unique_iso]: two initial 对象 are
 connected exactly one 同构. （已译） *)
Program Definition initial_unique_up_to_unique_iso {C : Category}
  (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ≅ @initial_obj C I2 => True) := {|
  unique_obj := initial_unique I1 I2;
  unique_property := I
|}.
Next Obligation.
  split.
  - apply (@zero_unique C I1).
  - apply (@zero_unique C I2).
Qed.

Program Definition initial_hom_unique {C : Category} (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ~> @initial_obj C I2 => True) := {|
  unique_obj := @zero C I1 (@initial_obj C I2);
  unique_property := I
|}.
Next Obligation. apply (@zero_unique C I1). Qed.

(*
   本节说明同构、始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma iso_initial_arrow_unique {C : Category} `{I : @Initial C} {y z : C}
      (i : y ≅ @initial_obj C I) (p q : y ~> z) : p ≈ q.
Proof.
  rewrite <- (id_right p), <- (id_right q).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite (@zero_unique C I z (p ∘ from i) (q ∘ from i)).
Qed.
