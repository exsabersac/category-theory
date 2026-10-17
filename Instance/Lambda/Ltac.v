From Coq Require Import Utf8.
From Coq Require Import Program.

(*
   本文件给出 λ 演算相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Local Set Warnings "-deprecated-notation".

(*
   本节说明 Ltac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac reduce_jmeq :=
  repeat match goal with
  | [ H : ∀ _: _, _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl JMeq_refl)

  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl)
  end.

(*
   本节说明 Ltac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac reduce :=
  reduce_jmeq;
  repeat (match goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          | [ H : { _ : _ | _ } |- _ ] => destruct H
          | [ H : { _ : _ & _ } |- _ ] => destruct H
          end; subst).

(*
   本节说明 Ltac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac inv H := inversion H; subst; clear H; reduce.

(*
   本节说明 Ltac 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac equality := intuition congruence.
