Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   A monad on a category C is an endofunctor M : C ⟶ C equipped with two
   natural transformations: a unit ret (η : Id ⟹ M) and a multiplication
   join (μ : M ○ M ⟹ M), satisfying the associativity law join ∘ fmap join ≈
   join ∘ join (μ ∘ Mμ ≈ μ ∘ μM) and the two unit laws join ∘ fmap ret ≈ id
   (μ ∘ Mη ≈ id) and join ∘ ret ≈ id (μ ∘ ηM ≈ id). Equivalently, a monad is
   a monoid object in the endofunctor category [C, C] with composition as the
   tensor.

   This is the join/return presentation. Its bind-based reformulation is
   recorded below as [bind], with the usual Haskell notations m >>= f and
   f >> g. The naturality squares for η and μ are kept explicit as the laws
   [fmap_ret] and [join_fmap_fmap] (in many treatments these are folded into
   "η and μ are natural transformations").

--------
nLab: https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   范畴 C 上的单子是配备两个自然变换的自函子 M : C ⟶ C：单位 ret（η : Id ⟹ M）
   与乘法 join（μ : M ○ M ⟹ M），满足结合律 join ∘ fmap join ≈ join ∘ join
   （μ ∘ Mμ ≈ μ ∘ μM）以及两条单位律 join ∘ fmap ret ≈ id（μ ∘ Mη ≈ id）与
   join ∘ ret ≈ id（μ ∘ ηM ≈ id）。等价地，单子是自函子范畴 [C, C] 中以复合为张量的
   幺半对象。

   这是 join/return 呈现。其基于 bind 的改写下文记为 [bind]，带常用 Haskell 记号
   m >>= f 与 f >> g。η 与 μ 的自然性方块显式保留为定律 [fmap_ret] 与 [join_fmap_fmap]
   （许多处理把它们折入「η 与 μ 是自然变换」）。
*)

(*
Where monads come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/monad
   nLab:  https://ncatlab.org/nlab/show/monad+(in+computer+science)
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Moggi, "Notions of computation and monads", Information and
          Computation 93(1), 1991

   The concept predates its name by a decade.  Godement introduced it in
   the appendix of "Topologie algébrique et théorie des faisceaux"
   (Hermann, 1958) as the device behind the canonical flabby resolution
   of a sheaf; the abstract notion, known in that era as the "standard
   construction", was studied by Huber ("Homotopy theory in general
   categories", Mathematische Annalen 144, 1961), who is credited with
   the observation that every adjunction F ⊣ U endows the composite
   U ◯ F with monad structure — realized in this library as
   [Adjunction_Monad] in Monad/Adjunction.v.  Whether every monad so
   arises was answered affirmatively twice in the same year: Kleisli
   ("Every standard construction is induced by a pair of adjoint
   functors", Proceedings of the AMS 16(3), 1965) rebuilt the adjunction
   from the free algebras, and Eilenberg and Moore (op. cit.) from all
   algebras, coining "triple" along the way.  Both resolutions are
   present here — Monad/Kleisli.v with Monad/Kleisli/Adjunction.v, and
   [TAlgebra] of Monad/Algebra.v with Monad/Eilenberg/Moore/Adjunction.v
   — and among the adjunctions inducing a given monad the first is
   initial, the second terminal.  Beck's monadicity theorem then
   characterizes which functors are, up to equivalence, forgetful
   functors from algebras (Monad/Monadicity/Beck.v).  The name "monad"
   itself is Bénabou's ("Introduction to bicategories", Springer LNM 47,
   1967), and the monoid-object remark of the header above — Mac Lane's
   slogan that a monad is just a monoid in the category of endofunctors
   ("Categories for the Working Mathematician", 1971) — is proved as a
   genuine equivalence by [Monoid_Monad] in Monad/Monoid.v.

   CORRECTION (#468).  The "genuine equivalence" above is a logical
   equivalence (↔) of the two structures on one endofunctor, with no
   morphisms on either side.  The statement about categories is
   Monad/Morphism/Monoid.v's [Monads_Mon_Equivalence]: Monad/Morphism.v's
   category [Monads C] of monads on C and their morphisms is equivalent to
   Mac Lane's Mon_{C^C}, Theory/Algebra/Monoid/Hom.v's [Mon] at the
   composition tensor of Structure/Monoidal/Compose.v.

   Two further readings organize the mathematics.  As an algebraic
   theory in packaged form, a monad carries its variety of algebras
   with it: Linton ("Some aspects of equational categories", La Jolla
   1965 conference proceedings, Springer 1966) proved finitary monads
   on Set equivalent to Lawvere theories, the thread taken up in
   Theory/Lawvere/Monad.v, while non-finitary monads reach further —
   the algebras of the ultrafilter monad are exactly the compact
   Hausdorff spaces (Manes, "A triple theoretic construction of compact
   algebras", Springer LNM 80, 1969).  As a generalized closure
   operator — on a poset category a monad is precisely one, the unit
   giving extensivity and [join] idempotency — the concept categorifies
   to the idempotent monads of reflective subcategories in
   Construction/Reflective/Idempotent.v.

   CORRECTION (#463).  The closure-operator reading above was asserted
   here without proof; Instance/Poset.v cited this file for it.  It is
   proved at Instance/Proset/Monad.v ([closure_of_monad],
   [closure_monad], [talgebra_iff_closed]), and it is sharper than the
   sentence says: [join] gives only T(Tx) ≤ Tx, and idempotency up to ≅
   also uses [ret] at Tx.  Structure/Thin/Monad.v's [thin_join_IsIso]
   makes that so in any thin category, and [thin_IdempotentMonad] makes
   every monad on a thin category an [IdempotentMonad] of
   Construction/Reflective/Idempotent.v, where idempotency is a
   hypothesis.  The equation T(Tx) = Tx needs antisymmetry, taken as a
   hypothesis in [closure_idem_eq].  The dual, a comonad on a preorder as
   an interior operator, is Instance/Proset/Monad/Interior.v.

   Computationally, a value of type M x is a computation that may
   perform effects while producing an x.  Moggi (LICS 1989; op. cit.
   1991) interpreted the effects of programming languages — state,
   exceptions, nondeterminism, continuations — as strong monads on a
   cartesian closed category, the strength hypothesis being the reason
   Monad/Strong.v exists; Wadler ("The essence of functional
   programming", POPL 1992) carried the discipline into Haskell, where
   effects coexist with purity.  Under this reading [ret] embeds a pure
   value, [bind] sequences two effectful steps, and programs x ~> M y
   compose as morphisms of the Kleisli category.  The bind presentation
   is equivalent to the join/return one used in this file (Manes,
   "Algebraic Theories", Springer 1976; Moggi 1991, Def. 1.2), and is
   the surface syntax elaborated Haskell-style in
   Instance/Coq/Monad.v.

--------
单子从何而来，以及用途为何

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
   承载面向程序员的那一层。
*)

Section Monad.

Context `{M : C ⟶ C}.

Class Monad := {
  ret {x}  : x ~> M x;          (* unit η : Id    ⟹ M / 单位 η : Id ⟹ M *)
  join {x} : M (M x) ~> M x;    (* mult μ : M ○ M ⟹ M / 乘 μ : M ○ M ⟹ M *)

  (* naturality of the unit η: ret ∘ f ≈ fmap f ∘ ret / 单位 η 的自然性：ret ∘ f ≈ fmap f ∘ ret *)
  fmap_ret {x y} (f : x ~> y) : ret ∘ f ≈ fmap f ∘ ret;

  (* associativity μ ∘ Mμ ≈ μ ∘ μM / 结合律 μ ∘ Mμ ≈ μ ∘ μM *)
  join_fmap_join {x} : join ∘ fmap (@join x) ≈ join ∘ join;
  (* left unit law μ ∘ Mη ≈ id / 左单位律 μ ∘ Mη ≈ id *)
  join_fmap_ret  {x} : join ∘ fmap (@ret x) ≈ id;
  (* right unit law μ ∘ ηM ≈ id / 右单位律 μ ∘ ηM ≈ id *)
  join_ret       {x} : join ∘ @ret (M x) ≈ id;

  (* naturality of the multiplication μ: join ∘ fmap (fmap f) ≈ fmap f ∘ join / 乘法 μ 的自然性：join ∘ fmap (fmap f) ≈ fmap f ∘ join *)
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

(*
nLab: https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   A comonad is the formal dual of a monad: a counit ε : M ⟹ Id and a
   comultiplication δ : M ⟹ M ○ M satisfying the dual coassociativity and
   counit laws. Since duality is C^op^op = C by reflexivity here, it is
   obtained for free as a monad on the opposite category.

--------
nLab: https://ncatlab.org/nlab/show/comonad
   维基百科: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   上下文函子（comonad）是单子（monad）的形式对偶：一个余单位 ε : M ⟹ Id 和一个共乘 δ : M ⟹ M ○ M，满足对偶的结合律和余单位律。由于对偶性在此处为自反性 C^op^op = C，因此它作为对立范畴上的单子可以直接获得。
*)

Definition Comonad `{M : C ⟶ C} := @Monad (C^op) (M^op).
