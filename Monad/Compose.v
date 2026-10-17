Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Distributive.

Generalizable All Variables.

(* * * The 复合 单子 M ◯ N 分配律 （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_law_between_monads

   本文件给出复合相关构造（伴随/函子/单子等的复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonadCompose.

Context {C : Category}.
Context `{@Monoidal C}.

Context {M : C ⟶ C}.
Context {O : @Monad C M}.

Context {N : C ⟶ C}.
Context `{@StrongFunctor C _ N}.
Context `{@LaxMonoidalFunctor C C _ _ N}.

#[local] Obligation Tactic := idtac.

#[export] Program Instance Monad_Compose `{!Monad_Distributive M N} :
  @Monad _ (M ◯ N) := {
  ret  := fun _ => ret[M] ∘ pure[N];
  join := fun _ => join[M] ∘ fmap[M] mprod
}.
Next Obligation.
  simpl; intros.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  rewrite <- !comp_assoc.
  rewrite <- fmap_pure.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- comp_assoc with (f := join[M]).
  rewrite <- comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := fmap[M] mprod).
  rewrite <- join_fmap_fmap.
  rewrite comp_assoc.
  rewrite comp_assoc with (f := join[M]).
  rewrite comp_assoc with (f := join[M]).
  rewrite <- join_fmap_join.
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite comp_assoc.
  rewrite <- mprod_fmap_join_fmap_mprod.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- join_fmap_ret.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite mprod_fmap_pure.
  reflexivity.
Qed.
Next Obligation.
  simpl; intros.
  rewrite <- mprod_pure.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret; cat.
Qed.
Next Obligation.
  simpl; intros.
  rewrite comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@mprod_fmap_fmap _ _ _ _ _ _ _ _ x).
  simpl in X.
  rewrite X.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.

End MonadCompose.
