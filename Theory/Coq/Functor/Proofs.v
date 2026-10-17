Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Functor.

Generalizable All Variables.

(** Lawfulness of the Coq [Functor] instances, via categorical endofunctors *)

(*
 nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   本文件给出相应结构的证明。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition EndoFunctor := @AFunctor Coq Coq.

(* Every lawful endofunctor on Coq is trivially an instance of
   [Category.Theory.Coq.Functor.Functor]: forgetting the laws keeps [fmap]. *)
Definition EndoFunctor_Functor (F : Type → Type)
  `(H : EndoFunctor F) : Functor F := {|
  fmap := λ _ _ f, fmap[H] f;
|}.

Coercion EndoFunctor_Functor : EndoFunctor >-> Functor.

Definition IsFunctor `(Functor F) : Type := EndoFunctor F.

Import FunctorNotations.

(* We can define this instance by appealing to the general [Id] functor. All
   that is required is for the object and function mappings to coincide. *)
Definition Identity_IsFunctor : IsFunctor Identity_Functor :=
  ToAFunctor Id.

Program Definition arrow_IsFunctor {x} : IsFunctor (arrow_Functor x) := {|
  a_fmap := arrow_Functor x;
|}.
Next Obligation.
  proper.
  extensionality r.
  now rewrite H.
Qed.

(* If [F] and [G] are both functors in Coq, we know that the composition is
   also a valid functor, and so we can map [Compose_Functor] directly to this
   composition. *)
Definition Compose_IsFunctor `(HF : EndoFunctor F) `(HG : EndoFunctor G) :
  IsFunctor (@Compose_Functor _ HF _ HG) :=
  ToAFunctor (Compose (FromAFunctor HF) (FromAFunctor HG)).

Corollary compose_fmap  `{Functor F} `{Functor G} {x y} (f : x → y) :
  fmap[F ∘ G]%prg f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.
