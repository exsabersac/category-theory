Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Theory.Lawvere.Sets.

Generalizable All Variables.

(**
* The finitary-monad connection, hypothesis-scoped

    nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
    nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

    Classically the underlying-set functor [ev1 T : Models T Sets ⟶ Sets]
    has a left adjoint — the free-model functor — whose existence is a
    consequence of the general adjoint functor theorem (Adjunction/GAFT.v
    is the in-tree source of that argument).  Constructing that left
    adjoint here would need the solution-set work for [Models T Sets],
    which is out of scope for this file; following the SAFT precedent the
    left adjoint enters as DATA: a functor [L] together with an adjunction
    [L ⊣ ev1 T].

    Given that data, everything downstream is direct instantiation of the
    Phase-14 monadicity spine at the adjunction [adj : L ⊣ ev1 T], with
    the binders of Monad/Comparison.v matched as C := Models T Sets,
    D := Sets, F := L, U := ev1 T:

    - [Lawvere_Monad] : the transparently packaged induced monad
      [Adjunction_Induced_Monad adj] on [Sets], with carrier [ev1 T ◯ L],
      ret = η and join = U ε F;

    - [Lawvere_EM_Comparison] : the Eilenberg–Moore comparison functor
      [EM_Comparison adj] from [Models T Sets] into the algebras of that
      monad;

    - [Lawvere_crude_monadicity] : under exactly the crude-monadicity
      hypotheses of Monad/Monadicity/Crude.v — [Models T Sets] has
      coequalizers of reflexive pairs, [ev1 T] preserves them, and
      [ev1 T] reflects isomorphisms — the comparison is an equivalence
      of categories, so [Models T Sets] is monadic over [Sets].

    The full finitary-monad ⟷ Lawvere-theory EQUIVALENCE (that the
    induced monad is finitary, and that every finitary monad on [Sets]
    arises this way from a theory, naturally in both directions) is
    deferred (ledger 2).

--------
* 有限单子连接，假设范围

nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
维基百科: https://en.wikipedia.org/wiki/Lawvere_theory

从经典上讲，基础集合函子[ev1 T : Models T Sets ⟶ Sets]具有一个左伴随——自由模型函子——其存在是一般伴随定理的结果（Adjunction/GAFT.v是该论证的内树源）。在这里构造该左伴随需要为[Models T Sets]进行解集工作，这超出了此文件的范围；按照SAFT的先例，左伴随以DATA的形式出现：一个函子[L]及其伴随[L ⊣ ev1 T]。

给定这些数据，下游的所有内容都是在伴随 [adj : L ⊣ ev1 T] 上直接实例化 Phase-14 单子脊，其中 Monad/Comparison.v 的绑定器匹配为 C := Models T Sets, D := Sets, F := L, U := ev1 T:

- [Lawvere_Monad]：透明封装的诱导单子  
  [Adjunction_Induced_Monad adj] 在 [Sets] 上，载体为 [ev1 T ◯ L]，  
  ret = η， join = U ε F；

- [Lawvere_EM_Comparison]：Eilenberg–Moore 比较函子 [EM_Comparison adj] 从 [Models T Sets] 进入该 monad 的代数；

- [Lawvere_crude_monadicity]：在 Monad/Monadicity/Crude.v 的完全粗单子性假设下 —— [Models T Sets] 有自反对的余等化子，[ev1 T] 保持它们，并且 [ev1 T] 反映同构 —— 比较是范畴的一个等价，因此 [Models T Sets] 在 [Sets] 上是单子的。

完全有限单子 ⟷ 劳维理论等价（即所诱导的单子是有限的，并且 [Sets] 上的每个有限单子自然地都以这种方式从一个理论中产生，两者方向均然）被推迟（账本 2）。
*)

Section LawvereMonad.

Context (T : LawvereTheory).
Context (L : Sets ⟶ Models T Sets).
Context (adj : L ⊣ ev1 T).

(**
The induced monad on [Sets]: ret = η, join = U ε F, packaged
    transparently by [Adjunction_Induced_Monad].

--------
在 [Sets] 上诱导的单子：ret = η，join = U ε F，由 [Adjunction_Induced_Monad] 透明打包。
*)

Definition Lawvere_Monad : @Monad Sets (ev1 T ◯ L) :=
  Adjunction_Induced_Monad adj.

(** The Eilenberg–Moore comparison functor at this adjunction. / 此伴随下的 Eilenberg–Moore 比较函子。 *)

Definition Lawvere_EM_Comparison :
  Models T Sets ⟶ @EilenbergMoore Sets (ev1 T ◯ L) Lawvere_Monad :=
  EM_Comparison adj.

(**
** Scoped monadicity

    The crude-monadicity hypotheses of Monad/Monadicity/Crude.v,
    re-exposed verbatim at this adjunction.

--------
** 作用域单子性

    Monad/Monadicity/Crude.v 中的粗单子性假设，
    在此伴随处逐字重新呈现。
*)

Context (RC : HasReflexiveCoequalizers (Models T Sets)).
Context (pres : PreservesReflexiveCoequalizers (ev1 T)).
Context (refl : ReflectsIsos (ev1 T)).

Corollary Lawvere_crude_monadicity :
  EquivalenceOfCategories Lawvere_EM_Comparison.
Proof using RC pres refl.
  exact (crude_monadicity adj RC pres refl).
Defined.

End LawvereMonad.

