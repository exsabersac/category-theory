Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.
Require Export Category.Theory.Coq.Functor.

Generalizable All Variables.

(** Lawfulness of the Coq [Functor] instances, via categorical endofunctors / 通过范畴自函子验证 Coq [Functor] 实例的合法性 *)

(*
nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   The bare [Theory.Coq.Functor.Functor] class carries only [fmap], with no
   laws.  A Coq functor is lawful exactly when it satisfies the two functor
   laws: identity [fmap id ≈ id] and composition
   [fmap (g ∘ f) ≈ fmap g ∘ fmap f] (Wikipedia), equivalently when its object
   map and [fmap] form an endofunctor on the category [Coq] in the categorical
   sense, preserving identities [F id = id] and composition [F (g ∘ f) = F g ∘
   F f] (nLab).

   This file packages “lawful” as [EndoFunctor F := AFunctor Coq Coq F] and
   [IsFunctor], and exhibits witnesses that the identity, reader/arrow, and
   composite [Functor] instances are lawful, plus the [compose_fmap]
   characterisation of [fmap] for a composite.  The proofs that rely on
   [functional_extensionality_dep] (e.g. [arrow_IsFunctor]) inherit it from
   the applied/Coq layer; that axiom is expected here, not a regression.

--------
nLab: https://ncatlab.org/nlab/show/functor
   维基百科: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   空的 [Theory.Coq.Functor.Functor] 类仅携带 [fmap]，而没有任何定律。Coq 函子恰好在满足两个函子定律时才是合法的：恒等 [fmap id ≈ id] 和复合 [fmap (g ∘ f) ≈ fmap g ∘ fmap f]（维基百科），等价于当其对象映射和 [fmap] 在范畴意义上在范畴 [Coq] 上形成一个自函子，同时保持恒等 [F id = id] 和复合 [F (g ∘ f) = F g ∘ F f]（nLab）。

   此文件将“合法”打包为 [EndoFunctor F := AFunctor Coq Coq F] 和 [IsFunctor]，并展示了恒等、reader/箭头和复合 [Functor] 实例是合法的见证，以及复合的 [compose_fmap] 表征 [fmap]。依赖于 [functional_extensionality_dep] 的证明（例如 [arrow_IsFunctor]）从应用/Coq 层继承该特性；该公理在此处是预期的，而非回归。
*)

Definition EndoFunctor := @AFunctor Coq Coq.

(*
Every lawful endofunctor on Coq is trivially an instance of
   [Category.Theory.Coq.Functor.Functor]: forgetting the laws keeps [fmap].

--------
Coq 上的每一个合法的 endofunctor 都显然是 [Category.Theory.Coq.Functor.Functor] 的一个实例：忘记这些法则就保留了 [fmap]。
*)
Definition EndoFunctor_Functor (F : Type → Type)
  `(H : EndoFunctor F) : Functor F := {|
  fmap := λ _ _ f, fmap[H] f;
|}.

Coercion EndoFunctor_Functor : EndoFunctor >-> Functor.

Definition IsFunctor `(Functor F) : Type := EndoFunctor F.

Import FunctorNotations.

(*
We can define this instance by appealing to the general [Id] functor. All
   that is required is for the object and function mappings to coincide.

--------
我们可以通过调用通用的 [Id] 函子来定义这个实例。所需的只是对象映射和函数映射相一致。
*)
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

(*
If [F] and [G] are both functors in Coq, we know that the composition is
   also a valid functor, and so we can map [Compose_Functor] directly to this
   composition.

--------
如果 [F] 和 [G] 都是 Coq 中的函子，我们知道它们的组合也是一个有效的函子，因此我们可以直接将 [Compose_Functor] 映射到这个组合上。
*)
Definition Compose_IsFunctor `(HF : EndoFunctor F) `(HG : EndoFunctor G) :
  IsFunctor (@Compose_Functor _ HF _ HG) :=
  ToAFunctor (Compose (FromAFunctor HF) (FromAFunctor HG)).

Corollary compose_fmap  `{Functor F} `{Functor G} {x y} (f : x → y) :
  fmap[F ∘ G]%prg f = fmap[F] (fmap[G] f).
Proof. reflexivity. Qed.
