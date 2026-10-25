Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.

Generalizable All Variables.

(**
* Monadicity: sanity witnesses

    nLab:      https://ncatlab.org/nlab/show/monadic+adjunction
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    The smallest example of a monadic adjunction is the identity adjunction
    Id ⊣ Id on any category C ([Adjunction_Id] of Adjunction/Compose.v,
    which reuses [adj_id] of Instance/Adjoints.v).  Its induced monad is
    the identity monad T = Id ◯ Id, whose unit and multiplication are both
    identities, and its Eilenberg–Moore category C^T is equivalent to C
    itself: the algebra unit law ν ∘ η ≈ id forces every structure map
    ν : T a ~> a to be the identity ([identity_alg_id]), so an object of
    C^T is an object of C carrying an essentially unique algebra, and any
    C-arrow is a homomorphism between any two identity-monad algebras
    ([identity_alg_hom_commutes]).

    Concretely, the Eilenberg–Moore comparison functor
    K = [EM_Comparison Adjunction_Id] : C ⟶ C^T of Monad/Comparison.v is
    an equivalence of categories ([identity_monadic]) with quasi-inverse
    the forgetful functor [EM_Forget].  The unit cell Id[C] ≈ U^T ◯ K is
    [EM_Comparison_Forget] read backwards (its components are identity
    isomorphisms), and the counit cell K ◯ U^T ≈ Id[C^T] is assembled by
    hand from isomorphisms whose underlying arrows are identities.  In
    the vocabulary of Monad/Comparison.v this exhibits Id[C] as a monadic
    functor ([Identity_Monadic]) — the basic sanity witness for the crude
    monadicity theorem of Monad/Monadicity/Crude.v, checked here directly
    rather than through that theorem's coequalizer machinery. 

--------
* Monadicity：理智见证人

nLab：https://ncatlab.org/nlab/show/monadic+adjunction
 维基百科：https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

单子附加的最小例子是恒等附加
 Id ⊣ 任何类别 C 上的 Id（Adjunction/Compose.v 的 [Adjunction_Id]，
 它重用了 Instance/Adjoints.v 的 [adj_id]）。 其诱导单子是
 恒等单子 T = Id ◯ Id，其单位和乘法均为
 恒等式，其 Eilenberg–Moore 范畴 C^T 等价于 C
 本身：代数单位律 ν ∘ η ≈ id 强制每个结构图
 ν : T a ~> a 为恒等式 ([identity_alg_id])，因此对象
 C^T 是 C 的一个对象，带有本质上唯一的代数，并且任何
 C-arrow 是任意两个恒等单代数之间的同态
 ([identity_alg_hom_commutes])。

具体来说，Eilenberg–Moore 比较函子
 K = [EM_Comparison Adjunction_Id] : Monad/Comparison.v 的 C ⟶ C^T 是
 类别 ([identity_monadic]) 与拟逆的等价
 健忘的函子 [EM_Forget]。 晶胞 Id[C] ≈ U^T ◯ K 为
 [EM_Comparison_Forget] 向后读取（其组件是恒等
 同构），并且单位单元 K ◯ U^T ≈ Id[C^T] 的组装方式为
 来自同构的手，其基本箭头是恒等式。 在
 Monad/Comparison.v 的词汇表将 Id[C] 展示为 Monadic
 函子 ([Identity_Monadic]) — 原油的基本理智见证
 Monad/Monadicity/Crude.v的一元性定理，直接查看这里
 而不是通过该定理的协均衡器机制。 
*)

Section IdentityMonadic.

Context {C : Category}.

Local Notation A  := (@Adjunction_Id C).
Local Notation T  := (Id[C] ◯ Id[C]).
Local Notation HM := (Adjunction_Induced_Monad A).
Local Notation EM := (@EilenbergMoore C T HM).
Local Notation K  := (EM_Comparison A).
Local Notation UT := (@EM_Forget C T HM).

(**
Every algebra for the identity monad has identity structure map: the
    unit of the induced monad is the unit of [Adjunction_Id], which is the
    identity ([adj_id_unit]), so the algebra unit law ν ∘ η ≈ id collapses
    to ν ≈ id. 

--------
恒等单子的每个代数都有恒等结构图：
 诱导单子的单位是 [Adjunction_Id] 的单位，即
 恒等式 ([adj_id_unit])，因此代数单位律 ν ∘ η ≈ id 崩溃
 到 ν ≈ id。 
*)

Lemma identity_alg_id {a : C} (ν : @TAlgebra C T HM a) :
  t_alg[ν] ≈ id[a].
Proof.
  assert (Hret : @ret C T HM a ≈ id[a]) by reflexivity.
  rewrite <- (@t_id C T HM a ν), Hret.
  now rewrite id_right.
Qed.

(**
Consequently every C-arrow intertwines any two identity-monad algebra
    structures: both structure maps are identities, and fmap[T] is the
    identity on morphisms. 

--------
因此，每个 C 箭头都与任意两个恒等单子代数交织在一起
 结构：两个结构图都是恒等式，fmap[T] 是
 态射上的恒等式。 
*)

Lemma identity_alg_hom_commutes {a b : C}
  (ν : @TAlgebra C T HM a) (ρ : @TAlgebra C T HM b) (f : a ~{C}~> b) :
  f ∘ t_alg[ν] ≈ t_alg[ρ] ∘ fmap[T] f.
Proof.
  rewrite (identity_alg_id ν), (identity_alg_id ρ).
  rewrite id_left, id_right.
  reflexivity.
Qed.

(**
The counit isomorphism K (U^T (a, ν)) ≅ (a, ν) of the equivalence: in
    both directions the underlying arrow is the identity of the carrier,
    which is a homomorphism by the previous lemma. 

--------
等价的单位同构 K (U^T (a, ν)) ≅ (a, ν) ： 在
 两个方向下面的箭头是承运人的身份，
 这是前一个引理的同态。 
*)

Definition identity_counit_to (X : EM) :
  fobj[K ◯ UT] X ~{EM}~> X :=
  @Build_TAlgebraHom C T HM (Id[C] (`1 X)) (`1 X)
    (EM_Comparison_Algebra A (`1 X)) (`2 X)
    id
    (identity_alg_hom_commutes (EM_Comparison_Algebra A (`1 X)) (`2 X) id).

Definition identity_counit_from (X : EM) :
  X ~{EM}~> fobj[K ◯ UT] X :=
  @Build_TAlgebraHom C T HM (`1 X) (Id[C] (`1 X))
    (`2 X) (EM_Comparison_Algebra A (`1 X))
    id
    (identity_alg_hom_commutes (`2 X) (EM_Comparison_Algebra A (`1 X)) id).

Lemma identity_counit_to_from (X : EM) :
  identity_counit_to X ∘ identity_counit_from X ≈ id.
Proof.
  cbn.
  now rewrite id_left.
Qed.

Lemma identity_counit_from_to (X : EM) :
  identity_counit_from X ∘ identity_counit_to X ≈ id.
Proof.
  cbn.
  now rewrite id_left.
Qed.

Definition identity_counit_iso (X : EM) :
  @Isomorphism EM (fobj[K ◯ UT] X) X :=
  @Build_Isomorphism EM (fobj[K ◯ UT] X) X
    (identity_counit_to X) (identity_counit_from X)
    (identity_counit_to_from X) (identity_counit_from_to X).

(**
The counit cell of the equivalence: comparing after forgetting is the
    identity of C^T.  Naturality holds on underlying arrows, where all the
    iso components are identities. 

--------
等价的元胞：遗忘后的比较是
 C^T 的身份。 自然性存在于潜在的箭头上，所有的
 iso 组件是身份。 
*)

Theorem identity_equivalence_counit : K ◯ UT ≈ Id[EM].
Proof.
  exists identity_counit_iso.
  intros X Y f; cbn.
  cat.
Qed.

(**
The unit cell: forgetting after comparing is U = Id[C] on the nose —
    this is [EM_Comparison_Forget] at the identity adjunction, read
    backwards. 

--------
晶胞：比较完忘记了是U=Id[C]在鼻子上——
 这是身份附加处的 [EM_Comparison_Forget]，请阅读
 向后。 
*)

Theorem identity_equivalence_unit : Id[C] ≈ UT ◯ K.
Proof.
  symmetry.
  exact (EM_Comparison_Forget A).
Qed.

(**
The identity-monad witness: the Eilenberg–Moore comparison functor of
    the identity adjunction is an equivalence of categories, quasi-inverse
    the forgetful functor. 

--------
身份单子见证者：Eilenberg-Moore 比较函子
 恒等附加是范畴的等价，拟逆
 健忘的函子。 
*)

Definition identity_monadic : EquivalenceOfCategories K :=
  @Build_EquivalenceOfCategories C EM K UT
    identity_equivalence_counit
    identity_equivalence_unit.

End IdentityMonadic.

(**
Packaged in the vocabulary of Monad/Comparison.v: the identity functor
    is monadic. 

--------
封装在 Monad/Comparison.v 的词汇中：恒等函子
 是一元的。 
*)

Definition Identity_Monadic {C : Category} : Monadic Id[C] :=
  (Id[C]; (Adjunction_Id; identity_monadic)).
