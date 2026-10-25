Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   初始对象 `0`：对每个 `x` 恰有一个态射 `zero : 0 ~> x`（文献常写 `¡`）。
   这是终对象的对偶：C 的初始对象 = C^op 的终对象（箭头全反向）。
   An initial object `0` has a unique arrow `0 ~> x` for every `x`.
   Dual of terminal: Initial C := Terminal (C^op).
*)

(*
   关于初始对象 / On initial objects

   Wikipedia: https://en.wikipedia.org/wiki/Universal_property
   nLab:      https://ncatlab.org/nlab/show/empty+type

   Haskell 对照：Void / Data.Void ——「没有值」；从 Void 到任意类型恰有一个函数
   `absurd`。初始对象 = 范畴版的 Void。
   Haskell analogy: Void — unique map `Void -> a` (`absurd`).
*)

(*
   【Initial 记号与字段展开】/ Notation & field walkthrough

   1) 本文件不重写 Class：Notation "'Initial' C" := (@Terminal (C^op))。
      在对偶范畴里把终对象当初始对象用——箭头方向自动翻转。
      No new Class: Initial C is Terminal on C^op (arrows reverse).

   2) 导出名字 / Exported names (dual of Terminal's fields)
      - initial_obj / 0  —— 对象 0（= C^op 里的 terminal_obj）
      - zero {x}        —— ¡ : 0 ~> x（= C^op 里的 one）
      - zero_unique     —— 任意两出射箭头 ≈（= one_unique）

   3) 阅读提示：先懂 Terminal.v，再把「进 1」改成「出 0」即可。
      Read Terminal first; flip "into 1" to "out of 0".
*)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

(* 初始对象 0（C^op 中的终对象）/ initial object 0 *)
Definition initial_obj : C := @terminal_obj _ I.

(* 唯一箭头 ¡ : 0 ~> x / unique arrow out of 0 *)
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

(* 出射唯一性 / uniqueness of arrows out of 0 *)
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

(* 两初始对象间的唯一同构 / Unique iso between initials *)
Program Definition initial_unique {C : Category} (I1 I2 : @Initial C) :
  @initial_obj C I1 ≅ @initial_obj C I2 := {|
  to   := @zero C I1 (@initial_obj C I2);
  from := @zero C I2 (@initial_obj C I1)
|}.
Next Obligation. apply (@zero_unique C I2). Qed.
Next Obligation. apply (@zero_unique C I1). Qed.

(* 两初始对象间任意两箭头相等（对偶 terminal_arrow_unique）
   / Any two arrows between initials agree *)
Corollary initial_arrow_unique {C : Category} (I1 I2 : @Initial C)
      (f g : @initial_obj C I1 ~> @initial_obj C I2) : f ≈ g.
Proof. apply (@zero_unique C I1). Qed.

(* 谓词形式：「c 是初始对象」/ Predicate: c is initial *)
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

(* 沿同构搬运 Initial（对偶 Terminal_iso）/ Transport Initial along iso *)
Definition Initial_iso {C : Category} (I : @Initial C) (y : C)
  (i : @initial_obj C I ≅ y) : @Initial C :=
  @Terminal_iso (C^op) I y (Isomorphism_Opposite i).

(* 搬运后 definitionally 选中新对象 / Transported structure picks new obj *)
Corollary Terminal_iso_obj {C : Category} (T : @Terminal C) (y : C)
  (i : @terminal_obj C T ≅ y) : @terminal_obj C (Terminal_iso T y i) = y.
Proof. reflexivity. Qed.

Corollary Initial_iso_obj {C : Category} (I : @Initial C) (y : C)
  (i : @initial_obj C I ≅ y) : @initial_obj C (Initial_iso I y i) = y.
Proof. reflexivity. Qed.

(* 唯一同构下唯一（对偶）/ Unique up to unique iso (dual) *)
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

(* 若 y ≅ 0，则 y ~> z 的任意两箭头相等 / If y ≅ 0, arrows y~>z unique *)
Lemma iso_initial_arrow_unique {C : Category} `{I : @Initial C} {y z : C}
      (i : y ≅ @initial_obj C I) (p q : y ~> z) : p ≈ q.
Proof.
  rewrite <- (id_right p), <- (id_right q).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite (@zero_unique C I z (p ∘ from i) (q ∘ from i)).
Qed.
