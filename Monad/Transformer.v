Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** * Monad transformers. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Monad_transformer

   本文件给出单子相关定义或实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Transformer.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{@Monad C M}.
Context {T : (C ⟶ C) → (C ⟶ C)}.
Context `{@Monad C (T M)}.

Class MonadTransformer := {
  lift {a} : M a ~> T M a;

  lift_return {a} : lift ∘ @ret C M _ a ≈ ret;
  lift_bind {a b} (f : a ~> M b) :
    lift ∘ join ∘ fmap f ≈ join ∘ fmap (lift ∘ f) ∘ lift
}.

End Transformer.

Arguments MonadTransformer {_ _ _} T {_}.

(******************************************************************************
 * Species 1: Identity transformations.
 ******************************************************************************)

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition IdentityT {C : Category} (M : C ⟶ C) : C ⟶ C := {|
  fobj := fobj[M];
  fmap := fun _ _ => fmap[M]
|}.
Next Obligation. apply fmap_comp. Qed.

Program Definition IdentityT_Monad {C : Category} (M : C ⟶ C) `{@Monad C M} :
  @Monad C (@IdentityT C M) := {|
  ret  := fun _ => ret[M];
  join := fun _ => join[M]
|}.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.

#[export]
Program Instance IdentityT_MonadTransformer {C : Category} (M : C ⟶ C) `{@Monad C M} :
  @MonadTransformer C M _ (@IdentityT C) (IdentityT_Monad M) := {
  lift := fun _ => id
}.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(******************************************************************************
 * Species 2: Constant mapping transformations.
 ******************************************************************************)

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition ConstT {C : Category} (K M : C ⟶ C) : C ⟶ C := {|
  fobj := fobj[K];
  fmap := fun _ _ => fmap[K]
|}.
Next Obligation. apply fmap_comp. Qed.

Program Definition ConstT_Monad {C : Category} (K M : C ⟶ C) `{@Monad C K} :
  @Monad C (@ConstT C K M) := {|
  ret  := fun _ => ret[K];
  join := fun _ => join[K]
|}.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.

(* This is not a valid monad transformer, since there cannot be a morphism
   [M A ~> K A]. *)
Fail Definition ConstT_MonadTransformer {C : Category} (K M : C ⟶ C)
        `{@Monad C K} `{@Monad C M} :
  @MonadTransformer C M _ (@ConstT C K) (ConstT_Monad K M) := {|
  lift := fun _ => _
|}.
