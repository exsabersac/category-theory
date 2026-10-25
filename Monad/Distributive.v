Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Functor.Strong.

Generalizable All Variables.

(** * Distributive law for composing monads  / * 组成单子的分配律*)

(*
nLab: https://ncatlab.org/nlab/show/distributive+law
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_law_between_monads

   Monads do not compose in general: for a monad M and a functor N there is no
   canonical monad structure on M ◯ N. A distributive law supplies the missing
   coherence. In its full Beck (1969) form a distributive law of N over M is a
   natural transformation N ◯ M ⟹ M ◯ N satisfying four laws (compatibility
   with the two units and the two multiplications), under which the composite
   carries a monad structure.

   The structure recorded here is the weaker [mprod]/swap presentation of Jones
   and Duponcheel ("Composing Monads", Yale tech report YALEU/DCS/RR-1004,
   1993), which is exactly the half of a distributive law needed to make M ◯ N
   a monad and is consumed as such in [Monad.Compose]. Rather than a bare swap
   N ◯ M ⟹ M ◯ N, the data is a single operation

       mprod : N (M (N A)) ~> M (N A)

   that pushes the inner N past the outer M, collapsing one layer. M is a full
   monad while N need only be a strong lax monoidal functor (so it has a unit
   [pure] but not necessarily a multiplication). The composite M ◯ N then has
   unit ret[M] ∘ pure[N] (both units stacked) and multiplication
   join[M] ∘ fmap[M] mprod, and the four laws below are precisely what make
   those satisfy the monad axioms; see [Monad.Compose]. 

--------
nLab：https://ncatlab.org/nlab/show/distributive+law
 维基百科：https://en.wikipedia.org/wiki/Distributive_law_between_monads

一般而言，单子不组合：对于单子 M 和函子 N 来说，不存在
 M ◯ N 上的规范单子结构。分配律提供了缺失的内容
 连贯性。 在完整的 Beck (1969) 形式中，N 对 M 的分配律是
 自然变换 N ◯ M ⟹ M ◯ N 满足四个定律（相容性
 具有两个单位和两个乘法），其中复合
 带有 monad 结构。

这里记录的结构是Jones的较弱的[mprod]/swap演示
 和 Duponcheel（“组合 Monads”，耶鲁大学技术报告 YALEU/DCS/RR-1004，
 1993），这正是使 M ◯ N 所需的分配律的一半
 一个 monad，并在 [Monad.Compose] 中被消耗。 而不是裸露的交换
 N ◯ M ⟹ M ◯ N，数据为单次操作

mprod : N (M (NA)) ~> M (NA)

将内部 N 推过外部 M，从而塌陷一层。 M 是一个完整的
 monad 而 N 只需是一个强松散的幺半群函子（所以它有一个单位
 [pure] 但不一定是乘法）。 复合 M ◯ N 则有
 单位 ret[M] ∘ pure[N] （两个单位堆叠）和乘法
 join[M] ∘ fmap[M] mprod，下面的四个定律正是使
 那些满足单子公理； 参见 [Monad.Compose]。 
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
  (* The swap/product operation pushing the inner N past the outer M.  / 交换/乘积操作将内部 N 推过外部 M。*)
  mprod {A} : N (M (N A)) ~> M (N A);

  (* Naturality of mprod: it is a natural transformation N ◯ M ◯ N ⟹ M ◯ N.  / mprod 的自然性：它是自然变换 N ◯ M ◯ N ⟹ M ◯ N。*)
  mprod_fmap_fmap {A B} (f : A ~> B) :
    @mprod B ∘ fmap[N] (fmap[M ◯ N] f) ≈ fmap[M ◯ N] f ∘ @mprod A;
  (* Left unit: mprod absorbs the inner unit pure[N].  / 左单元：mprod 吸收内部单元 pure[N]。*)
  mprod_pure {A} : @mprod A ∘ pure[N] ≈ id;
  (* Right unit: applied to the stacked unit ret[M] ∘ pure[N], mprod is ret[M].  / 右单元：应用于堆叠单元 ret[M] ∘ pure[N]，mprod 为 ret[M]。*)
  mprod_fmap_pure {A} : @mprod A ∘ fmap[N] (ret[M] ∘ pure[N]) ≈ ret[M];
  (*
Associativity: mprod commutes with the composite multiplication
     join[M] ∘ fmap[M] mprod, so the induced join on M ◯ N is associative. 

--------
结合性：mprod 与复合乘法可交换
 join[M] ∘ fmap[M] mprod，因此 M ◯ N 上的诱导连接是关联的。 
*)
  mprod_fmap_join_fmap_mprod {A} :
    @mprod A ∘ fmap[N] (join[M] ∘ fmap[M] (@mprod A))
      ≈ join[M] ∘ fmap[M] (@mprod A) ∘ @mprod (M (N A))
}.

End MonadDistributive.

Arguments Monad_Distributive {C _} M {_} N {_ _}.
