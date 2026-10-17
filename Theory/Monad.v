Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   范畴 C 上的单子是配备两个自然变换的自函子 M : C ⟶ C：单位 ret（η : Id ⟹ M）
   与乘法 join（μ : M ○ M ⟹ M），满足结合律 join ∘ fmap join ≈ join ∘ join
   （μ ∘ Mμ ≈ μ ∘ μM）以及两条单位律 join ∘ fmap ret ≈ id（μ ∘ Mη ≈ id）与
   join ∘ ret ≈ id（μ ∘ ηM ≈ id）。等价地，单子是自函子范畴 [C, C] 中以复合为张量的
   幺半对象。

   这是 join/return 呈现。其基于 bind 的改写下文记为 [bind]，带常用 Haskell 记号
   m >>= f 与 f >> g。η 与 μ 的自然性方块显式保留为定律 [fmap_ret] 与 [join_fmap_fmap]
   （许多处理把它们折入「η 与 μ 是自然变换」）。 *)

(* 单子从何而来，以及用途为何

   nLab:  https://ncatlab.org/nlab/show/monad
   nLab:  https://ncatlab.org/nlab/show/monad+(in+computer+science)
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Moggi, "Notions of computation and monads", Information and
          Computation 93(1), 1991

   概念比名称早十年。Godement 在 "Topologie algébrique et théorie des faisceaux"
   （Hermann, 1958）附录中引入它，作为层典范松弛分解背后的装置；该时代称为
   「标准构造」的抽象概念由 Huber（"Homotopy theory in general categories",
   Mathematische Annalen 144, 1961）研究，他因观察「每个伴随 F ⊣ U 赋予复合
   U ◯ F 以单子结构」而受赞誉——本库实现为 Monad/Adjunction.v 的 [Adjunction_Monad]。
   每个单子是否如此产生，同年被肯定回答两次：Kleisli（"Every standard construction
   is induced by a pair of adjoint functors", Proceedings of the AMS 16(3), 1965）
   从自由代数重建伴随，Eilenberg 与 Moore（同上）从全部代数重建，并顺带创造「triple」
   一词。两种分解此处都有——Monad/Kleisli.v 与 Monad/Kleisli/Adjunction.v，以及
   Monad/Algebra.v 的 [TAlgebra] 与 Monad/Eilenberg/Moore/Adjunction.v——在诱导给定
   单子的伴随中，前者初始、后者终结。Beck 单子性定理随后刻画哪些函子在等价下是
   来自代数的遗忘函子（Monad/Monadicity/Beck.v）。名称「monad」本身是 Bénabou 的
   （"Introduction to bicategories", Springer LNM 47, 1967），文首幺半对象注记——
   Mac Lane 的口号「单子只是自函子范畴中的幺半群」（"Categories for the Working
   Mathematician", 1971）——由 Monad/Monoid.v 的 [Monoid_Monad] 证明为真正等价。

   更正 (#468)。上文「真正等价」是同一自函子上两种结构的逻辑等价（↔），无宇宙层级变化；
   它不是范畴等价。计算侧读法经 Moggi（1991）进入编程：计算的「概念」是单子，
   return/bind 呈现（下文 [bind]）成为 Haskell 等语言的效应接口；Theory/Coq/Monad.v
   承载面向程序员的那一层。 *)

Section Monad.

Context `{M : C ⟶ C}.

Class Monad := {
  ret {x}  : x ~> M x;          (* unit η : Id    ⟹ M *)
  join {x} : M (M x) ~> M x;    (* mult μ : M ○ M ⟹ M *)

  (* naturality of the unit η: ret ∘ f ≈ fmap f ∘ ret *)
  fmap_ret {x y} (f : x ~> y) : ret ∘ f ≈ fmap f ∘ ret;

  (* associativity μ ∘ Mμ ≈ μ ∘ μM *)
  join_fmap_join {x} : join ∘ fmap (@join x) ≈ join ∘ join;
  (* left unit law μ ∘ Mη ≈ id *)
  join_fmap_ret  {x} : join ∘ fmap (@ret x) ≈ id;
  (* right unit law μ ∘ ηM ≈ id *)
  join_ret       {x} : join ∘ @ret (M x) ≈ id;

  (* naturality of the multiplication μ: join ∘ fmap (fmap f) ≈ fmap f ∘ join *)
  join_fmap_fmap {x y} (f : x ~> y) :
    join ∘ fmap (fmap f) ≈ fmap f ∘ join
}.

End Monad.

Arguments Monad {C} M.

Notation "ret[ M ]" := (@ret _ M _ _)
  (at level 9, format "ret[ M ]") : category_scope.
Notation "join[ M ]" := (@join _ M _ _)
  (at level 9, format "join[ M ]") : category_scope.

Section MonadLib.

Context `{@Monad C M}.

Definition bind {x y : C} (f : x ~> M y) : M x ~> M y :=
  join ∘ fmap[M] f.

End MonadLib.

Notation "m >>= f" := (bind f m) (at level 42, right associativity) : morphism_scope.
Notation "f >> g" := (f >>= fun _ => g)%morphism
  (at level 81, right associativity) : morphism_scope.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

(* nLab: https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   A comonad is the formal dual of a monad: a counit ε : M ⟹ Id and a
   comultiplication δ : M ⟹ M ○ M satisfying the dual coassociativity and
   counit laws. Since duality is C^op^op = C by reflexivity here, it is
   obtained for free as a monad on the opposite category. *)

Definition Comonad `{M : C ⟶ C} := @Monad (C^op) (M^op).
