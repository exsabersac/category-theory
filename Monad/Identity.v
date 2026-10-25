Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.

Generalizable All Variables.

(** * The identity monad  / * 身份单子*)

(*
Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §VI.3, book p. 144 (PDF p. 153), read from the page image: the
     discrete-space adjunction ⟨D, G, η, …⟩ : Set ⇀ Top "defines on Set
     the monad I = ⟨I, 1, 1⟩ which is the identity (identity functor,
     identity as unit and as multiplication).  The I-algebras in Set are
     just the sets" (catalog id maclane:VI.3:remark1).
   nLab: https://ncatlab.org/nlab/show/monad
   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category

   BACKGROUND.  The identity functor, with the identity as unit and as
   multiplication, is a monad on every category, and an adjunction whose unit
   is the identity induces a monad isomorphic to it: the unit's naturality
   gives T f ≈ f, and a triangle identity makes the multiplication U ε F ≈ the
   identity too; in Mac Lane's example these hold on data at [eq_refl].  An
   algebra for it is an arrow h : a → a with h ∘ id ≈ id, so h ≈ id and the
   action law holds of itself: Mac Lane's "the I-algebras in Set are just the
   sets", here at any category and up to ≈.  The monad matters because it is
   induced by adjunctions of very different kinds.  Mac Lane's example on p.
   144 is the discrete-space adjunction, whose right adjoint is not monadic
   (Instance/Top/Monadicity.v); the adjunction Id ⊣ Id, whose right adjoint is
   monadic (Monad/Monadicity/Examples.v's [identity_monadic]), induces a monad
   with functor Id ◯ Id whose unit and multiplication are [id] at [eq_refl]
   (control C55 of Test/ProbeMonadicity469.v), isomorphic to this one (no
   constant states that isomorphism).  So an induced monad does not determine
   whether its right adjoint is monadic.

   WHY A NEW CONSTANT.  Before this file the tree had three identity
   monads of Theory/Monad.v's class [Monad] (a fourth, Theory/Coq/
   Monad.v's [Identity_Monad], is of the programming class there), and
   none serves a statement over an arbitrary category that must compile
   on every supported version.
     - Monad/Strong.v's [Id_Monad] is a [#[local] Program Instance] inside
       the section of the identity strong monad.  Its universe list has
       three levels on Rocq 9.1.1, five on Coq 8.20.1 and seventeen on
       8.19.2 (#467's measurement, recorded in the header of Monad/
       Eilenberg/Moore/Limit/Examples.v), so no explicit instance of it
       compiles on all three versions.
     - Monad/Eilenberg/Moore/Limit/Examples.v's [IdSM] gives every field,
       but on [Sets] only, inside an examples file.
     - [Adjunction_Induced_Monad Adjunction_Id], the monad behind
       [identity_monadic], has the functor Id ◯ Id, not Id.
   [IdMonad C] follows [IdSM]'s pattern at an arbitrary category: the
   constructor [Build_Monad] with every field given, the laws closed by
   [reflexivity], [id_left] and [id_right], with no rewriting.

   WHAT IS HERE.
     - [IdMonad C : Monad Id[C]], with the readbacks [IdMonad_fobj],
       [IdMonad_fmap], [IdMonad_ret] and [IdMonad_join].
     - [IdMonad_alg_id]: the structure map of every algebra is ≈ id.
     - [IdMonad_EM_equivalence]: the forgetful functor of the
       Eilenberg-Moore category of [IdMonad C] is an equivalence of
       categories, with the free-algebra functor [EM_Free] as its
       quasi-inverse.  The counit [IdMonad_EM_counit] has the identity
       isomorphisms [iso_id] as components; the unit's component at an
       algebra (a, h), [IdMonad_EM_unit_iso], is the identity arrow of a,
       read as an algebra map (a, h) → (a, id) and back
       ([IdMonad_EM_unit_iso_id]).

   STRENGTHS.  By [eq_refl]: [IdMonad_fobj], [IdMonad_fmap],
   [IdMonad_ret], [IdMonad_join] and [IdMonad_EM_unit_iso_id].  Up to ≈:
   [IdMonad_alg_id] and the two cells of [IdMonad_EM_equivalence], in
   Theory/Functor.v's [Functor_Setoid].  The equivalence is not an
   isomorphism of categories: an algebra remembers its structure map h,
   which is ≈ id and need not be id.  For [IdSM] on [Sets] that is #467's
   [A_id_ne_A_true] (two different algebras on one carrier), the reason
   the forgetful functor there is not injective on objects; it is not
   restated here for [IdMonad].  Four proofs end [Defined] (counted by
   token).  Two are load-bearing, measured by closing each alone [Qed] in
   a copy of this file followed by Instance/Top/Monadicity.v: [IdMonad]
   ([IdMonad_ret] is then refused) and [IdMonad_EM_unit_iso]
   ([IdMonad_EM_unit] and [IdMonad_EM_unit_iso_id]: the proof of the
   first stops with "Unable to unify", and the readback is refused).  The
   two cells [IdMonad_EM_counit] and [IdMonad_EM_unit] are [Defined] by
   the data convention only.

   UNIVERSES, read off [About].  [IdMonad@{o h}] and
   [IdMonad_alg_id@{o h}]: constraint list empty.  The four readbacks
   bind [@{o h | +}]: empty on 9.1.1; the [+] is for the level of [eq],
   which Coq 8.19.2 and 8.20.1 bound below by o ([IdMonad_fobj]) or h
   (the other three), as #468 measured for its own readbacks.  The
   Eilenberg-Moore constants bind [@{o h s e}] with h < s, o <= e and
   h <= e, plus the bounds o <= Projections.u0 and h <= Projections.u1
   of the sigma projections, whence the [+]: exactly the block of
   [EilenbergMoore@{e o s h}], their first carrier.  [Compose] and
   [Functor_Setoid] take s for their own strict level, so no constant
   here adds a level.  No [Set] and no equation occur.

   NOT DELIVERED.  The identity monad is the initial object of [Monads C]
   (Monad/Morphism.v): the unit of any monad is the unique morphism of
   monads out of it.  That is not stated.  The Kleisli category of
   [IdMonad C] is not built, and [Id_Monad] and [IdSM] are not rewired
   onto [IdMonad]. 

--------
Mac Lane，“工作数学家的类别”，第二版。 （GTM 5），
 §VI.3，书页。 144（PDF第153页），从页面图像中读取：
 离散空间附加 ⟨D, G, η, …⟩ : Set ⇀ Top “在 Set 上定义
 单子 I = ⟨I, 1, 1⟩ 这是恒等（恒等函子，
 作为单位和乘法的同一性）。 Set 中的 I 代数是
 只是套装”（目录 ID maclane:VI.3:remark1）。
 nLab：https://ncatlab.org/nlab/show/monad
 nLab：https://ncatlab.org/nlab/show/Eilenberg-Moore+category

背景。 恒等函子，以恒等为单位，
 乘法，是每个范畴上的一个单子，也是一个单位的附属词
 同一性是否会引发与其同构的单子：单位的自然性
 给出 T f ≈ f，三角形恒等式使得乘法 U ε F ≈
 身份也是如此； 在 Mac Lane 的示例中，这些数据保存在 [eq_refl] 处。 安
 它的代数是一个箭头 h : a → a 且 h ∘ id ≈ id，因此 h ≈ id 并且
 作用定律本身成立：Mac Lane 的“Set 中的 I 代数只是
 集”，这里是任何类别，最多 ≈。 单子很重要，因为它是
 由非常不同种类的附加物引起。 Mac Lane 的例子见第 17 页。 
144 是离散空间伴随，其右伴随不是一元的
 （实例/顶部/Monadicity.v）； 伴随词 Id ⊣ Id，其右伴随词是
 monadic (Monad/Monadicity/Examples.v's [identity_monadic])，诱导一个 monad
 函子 Id ◯ Id，其单位和乘法为 [id] at [eq_refl]
 （Test/ProbeMonadicity469.v 的对照 C55），与此同构（无
 常数表示同构）。 所以诱导单子并不能决定
 它的右伴随是否是一元的。

为什么是一个新常数。 在此文件之前，树具有三个身份
 Theory/Monad.v 类 [Monad] 的单子（第四个，Theory/Coq/
 Monad.v 的 [Identity_Monad]，属于那里的编程类），并且
 none 对必须编译的任意类别提供声明
 在每个受支持的版本上。 
- Monad/Strong.v 的 [Id_Monad] 是一个 [#[local] 程序实例]里面
 恒等强单子的部分。 它的宇宙列表有
 Rocq 9.1.1 为 3 个级别，Coq 8.20.1 为 5 个级别，Coq 8.20.1 为 17 个级别
 8.19.2（#467的测量，记录在Monad/的头中
 Eilenberg/Moore/Limit/Examples.v)，因此没有明确的实例
 在所有三个版本上编译。 
- Monad/Eilenberg/Moore/Limit/Examples.v 的 [IdSM] 给出了每个字段，
 但仅在 [Sets] 上，位于示例文件内。 
- [Adjunction_Induced_Monad Adjunction_Id]，背后的单子
 [identity_monadic]，具有函子 Id ◯ Id，而不是 Id。 
[IdMonad C] 在任意类别上遵循 [IdSM] 的模式：
 构造函数 [Build_Monad] 给定每个字段，法则闭合为
 [reflexivity]、[id_left] 和 [id_right]，无需重写。

这里有什么。 
- [IdMonad C : Monad Id[C]]，带有回读 [IdMonad_fobj]，
 [IdMonad_fmap]、[IdMonad_ret] 和 [IdMonad_join]。 
- [IdMonad_alg_id]：每个代数的结构图都是 ≈ id。 
- [IdMonad_EM_equivalence]：健忘函子
 [IdMonad C] 的 Eilenberg-Moore 类别等价于
 类别，以自由代数函子 [EM_Free] 作为其
 拟逆。 [IdMonad_EM_counit] 单位具有标识
 同构 [iso_id] 作为组件； 该单元的组件在
 代数 (a, h)，[IdMonad_EM_unit_iso]，是 a 的恒等箭头，
 读作代数映射 (a, h) → (a, id) 并返回
 ([IdMonad_EM_unit_iso_id])。

优势。 通过 [eq_refl]：[IdMonad_fobj]、[IdMonad_fmap]、
 [IdMonad_ret]、[IdMonad_join] 和 [IdMonad_EM_unit_iso_id]。 直到 ≈：
 [IdMonad_alg_id] 和 [IdMonad_EM_equivalence] 的两个单元，在
 Theory/Functor.v 的 [Functor_Setoid]。 等价不是
 范畴的同构：代数记住它的结构图 h，
 它 ≈ id 并且不必是 id。 对于 [Sets] 上的 [IdSM]，即 #467
 [A_id_ne_A_true]（一个载体上有两个不同的代数），原因
 健忘函子在对象上不具有单射性； 它不是
 此处针对 [IdMonad] 进行了重述。 四张样张结束[Defined]（按
 令牌）。 两个是承重的，通过将每个单独的 [Qed] 关闭来测量
 此文件的副本，后跟 Instance/Top/Monadicity.v：[IdMonad]
 （[IdMonad_ret] 随后被拒绝）和 [IdMonad_EM_unit_iso]
 （[IdMonad_EM_unit] 和 [IdMonad_EM_unit_iso_id]：证明
 首先以“无法统一”停止，并且回读被拒绝）。 的
 两块电池 [IdMonad_EM_counit] 和 [IdMonad_EM_unit] 是 [Defined]
 仅数据约定。

宇宙，读出 [About]。 [IdMonad@{o h}] 和
 [IdMonad_alg_id@{o h}]：约束列表为空。 四次复习
 绑定 [@{o h | +}]：9.1.1 上为空； [+] 适用于 [eq] 的级别，
 其中 Coq 8.19.2 和 8.20.1 以下由 o ([IdMonad_fobj]) 或 h 绑定
 （其他三个），正如 #468 对其自己的读回所测量的那样。 的
 Eilenberg-Moore 常数将 [@{o h s e}] 与 h < s、o <= e 结合
 h <= e，加上边界 o <= Projections.u0 和 h <= Projections.u1
 西格玛投影，因此 [+]：正是
 [EilenbergMoore@{e o s h}]，他们的第一台载体。 [Compose] 和
 [Functor_Setoid] 以 s 为自己的严格级别，因此没有常数
 这里增加了一个层次。 没有 [Set]，也没有方程式出现。

未交付。 身份单子是 [Monads C] 的初始对象
 (Monad/Morphism.v)：任何单子的单位都是唯一的态射
 从中剔除单子。 没有说明这一点。 Kleisli范畴
 [IdMonad C] 未构建，[Id_Monad] 和 [IdSM] 未重新接线
 到 [IdMonad] 上。 
*)

(** ** The monad ⟨I, 1, 1⟩  / ** 单子 ⟨I, 1, 1⟩*)

Definition IdMonad@{o h | } (C : Category@{o h h}) : @Monad C Id[C].
Proof.
  unshelve refine (@Build_Monad C Id[C] (fun x => id) (fun x => id)
                     _ _ _ _ _); intros; simpl.
  - transitivity f; [ apply id_left | symmetry; apply id_right ].
  - reflexivity.
  - apply id_left.
  - apply id_left.
  - transitivity f; [ apply id_left | symmetry; apply id_right ].
Defined.

Example IdMonad_fobj@{o h | +} (C : Category@{o h h}) (x : C) :
  fobj[Id[C]] x = x := eq_refl.

Example IdMonad_fmap@{o h | +} (C : Category@{o h h}) (x y : C)
  (f : x ~> y) : fmap[Id[C]] f = f := eq_refl.

Example IdMonad_ret@{o h | +} (C : Category@{o h h}) (x : C) :
  @ret C Id[C] (IdMonad@{o h} C) x = id := eq_refl.

Example IdMonad_join@{o h | +} (C : Category@{o h h}) (x : C) :
  @join C Id[C] (IdMonad@{o h} C) x = id := eq_refl.

(** ** Its algebras are the objects  / ** 它的代数是对象*)

Lemma IdMonad_alg_id@{o h | } (C : Category@{o h h}) (a : C)
  (A : @TAlgebra C Id[C] (IdMonad@{o h} C) a) : t_alg[A] ≈ id.
Proof.
  transitivity (t_alg[A] ∘ id); [ symmetry; apply id_right | ].
  exact (@t_id C Id[C] (IdMonad@{o h} C) a A).
Qed.

Definition IdMonad_EM_counit@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)
    ◯ @EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C) ≈ Id[C].
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  transitivity (id ∘ f); [ symmetry; apply id_left | ].
  symmetry; apply id_right.
Defined.

Definition IdMonad_EM_unit_iso@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  @Isomorphism (@EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C))
    X (fobj[@EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C)
             ◯ @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)] X).
Proof.
  unshelve econstructor.
  - unshelve refine (@Build_TAlgebraHom C Id[C] (IdMonad@{o h} C)
                       (`1 X) (`1 X) (`2 X) _ id _); simpl.
    transitivity (t_alg[`2 X]); [ apply id_left | ].
    transitivity (@id C (`1 X)); [ exact (IdMonad_alg_id C _ (`2 X)) | ].
    symmetry; apply id_left.
  - unshelve refine (@Build_TAlgebraHom C Id[C] (IdMonad@{o h} C)
                       (`1 X) (`1 X) _ (`2 X) id _); simpl.
    transitivity (@id C (`1 X)); [ apply id_left | ].
    transitivity (t_alg[`2 X]);
      [ symmetry; exact (IdMonad_alg_id C _ (`2 X)) | ].
    symmetry; apply id_right.
  - simpl; apply id_left.
  - simpl; apply id_left.
Defined.

Example IdMonad_EM_unit_iso_id@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h})
  (X : @EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)) :
  (t_alg_hom[to (IdMonad_EM_unit_iso@{o h s e} C X)],
   t_alg_hom[from (IdMonad_EM_unit_iso@{o h s e} C X)]) = (id, id)
  := eq_refl.

Definition IdMonad_EM_unit@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  Id[@EilenbergMoore@{e o s h} C Id[C] (IdMonad@{o h} C)]
    ≈ @EM_Free@{o h s e} C Id[C] (IdMonad@{o h} C)
        ◯ @EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C).
Proof.
  exists (IdMonad_EM_unit_iso C).
  intros X Y f; simpl.
  transitivity (id ∘ t_alg_hom[f]); [ symmetry; apply id_left | ].
  symmetry; apply id_right.
Defined.

Definition IdMonad_EM_equivalence@{o h s e | h < s, o <= e, h <= e +}
  (C : Category@{o h h}) :
  EquivalenceOfCategories (@EM_Forget@{o h s e} C Id[C] (IdMonad@{o h} C)) :=
  @Build_EquivalenceOfCategories _ _ _ _
    (IdMonad_EM_counit@{o h s e} C) (IdMonad_EM_unit@{o h s e} C).
