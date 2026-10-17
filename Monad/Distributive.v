Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Strong.

Generalizable All Variables.

(** * Distributive law for composing monads *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_law_between_monads

   本文件给出 Beck 分配律：使两单子可复合为单子的额外数据。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MonadDistributive.

Context {C : Category}.
Context `{@Monoidal C}.

Context {M : C ⟶ C}.
Context {O : @Monad C M}.

Context {N : C ⟶ C}.
Context `{@StrongFunctor C _ N}.
Context `{@LaxMonoidalFunctor C C _ _ N}.

Class Monad_Distributive := {
  (* The swap/product operation pushing the inner N past the outer M. *)
  mprod {A} : N (M (N A)) ~> M (N A);

  (* Naturality of mprod: it is a natural transformation N ◯ M ◯ N ⟹ M ◯ N. *)
  mprod_fmap_fmap {A B} (f : A ~> B) :
    @mprod B ∘ fmap[N] (fmap[M ◯ N] f) ≈ fmap[M ◯ N] f ∘ @mprod A;
  (* Left unit: mprod absorbs the inner unit pure[N]. *)
  mprod_pure {A} : @mprod A ∘ pure[N] ≈ id;
  (* Right unit: applied to the stacked unit ret[M] ∘ pure[N], mprod is ret[M]. *)
  mprod_fmap_pure {A} : @mprod A ∘ fmap[N] (ret[M] ∘ pure[N]) ≈ ret[M];
  (* Associativity: mprod commutes with the composite multiplication
     join[M] ∘ fmap[M] mprod, so the induced join on M ◯ N is associative. *)
  mprod_fmap_join_fmap_mprod {A} :
    @mprod A ∘ fmap[N] (join[M] ∘ fmap[M] (@mprod A))
      ≈ join[M] ∘ fmap[M] (@mprod A) ∘ @mprod (M (N A))
}.

End MonadDistributive.

Arguments Monad_Distributive {C _} M {_} N {_ _}.
