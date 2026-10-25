Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Fractions.
Require Import Category.Construction.Fractions.Weak.
Require Import Category.Construction.Groupoid.Core.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(*
   * * Riehl 4.1.15: the adjoint triple [Fractions ⊣ Incl ⊣ Core]

   nLab:      https://ncatlab.org/nlab/show/core
   nLab:      https://ncatlab.org/nlab/show/localization
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid
   Book: Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
   printed p. 137 (PDF pp. 157-158) — the inclusion of groupoids
   into categories has adjoints on both sides, the left one the
   category of fractions and the right one the core
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §IV.1 — adjunctions from universal arrows
   Paper: Brown, From groups to groupoids: a brief survey, Bulletin of the
   London Mathematical Society 19, 1987

   WHAT IS DELIVERED.  Both halves of Riehl's example, over ONE ambient
   category, as two [Adjunction] records bundled into one statement:

   [Fractions_Incl_Adjunction : Adjunction FractionsF Grpd_Incl]
   [Incl_Core_Adjunction      : Adjunction Grpd_Incl  Core]
   [riehl_4_1_15              : AdjointTriple FractionsF Grpd_Incl Core]

   The right-hand half is [Construction/Groupoid/Core.v]'s, unchanged and
   unmoved; only the left-hand half is new, and the ambient is [Cat] for
   both, so no strictification and no comparison functor stands between
   them.  [Instance/Grpd.v]'s header said the left half "remains prose",
   and [Construction/Fractions.v]'s said the triple "is NOT assembled over
   one ambient here".  Both are superseded by this file, and both have been
   corrected in place in those headers — Instance/Grpd.v's sentence now
   points here, and Construction/Fractions.v keeps its account of the gap
   as the record of what closing it cost, since its strict statements
   remain the sharper reading and are not weakened.

   HOW THE LEFT HALF IS BUILT, AND WHAT THE GAP WAS.  The route is the
   library's standard one — a universal arrow at every object, then
   [Theory/Universal/Arrow.v]'s [AdjunctionFromUniversalArrows], which
   builds a LEFT adjoint and is therefore the RIGHT direction for this
   half (it is the wrong direction for [Incl ⊣ Core], which is why
   [Construction/Groupoid/Core.v] took the hom-setoid route instead).  The
   single obstruction was the strength of the `∃!` clause:
   [universal_arrow_from_UMP] wants it at the ambient's hom-setoid, [Grpd]
   inherits [Cat]'s [Functor_Setoid], and [Fractions_UMP_groupoid] supplied
   it at [Functor_StrictEq_Setoid].  Existence transferred along
   [strict_equiv_implies_fun_equiv]; uniqueness did not, and
   [Construction/Fractions/Weak.v] reproves it against natural isomorphism.
   With [Fractions_UMP_weak] in hand this file is assembly: the universal
   arrow is [FractionsProj C] with the weak [Unique] record handed straight
   across, the sigma of [Grpd]'s homs contributing a [(L; I)] on the way in
   and a destructuring on the way out, since [Grpd]'s [shom] is [True].

   THE LEFT ADJOINT IS THE LOCALIZATION, ON THE NOSE AND ON MORPHISMS.
   [FractionsF : Cat ⟶ Grpd] is the functor
   [AdjunctionFromUniversalArrows] generates, and it is not merely
   isomorphic to the category of fractions: [FractionsF_obj] checks
   [fobj[FractionsF] C = (Fractions C; Fractions_IsGroupoid C)] at
   [eq_refl].  On morphisms the identification is up to `≈` and cannot be
   better, since the localization of a functor is itself only determined up
   to natural isomorphism: [FractionsF_fmap] identifies [fmap[FractionsF] F]
   with [FractionsMap F], the lift of [FractionsProj D ◯ F] along the
   projection.  [Fractions_unit_is_proj] reads the unit off as
   [FractionsProj C], which is what makes the adjunction the localization
   rather than some other left adjoint.

   FUNCTORIALITY OF [Fractions] IN [C] was listed as not delivered by
   [Construction/Fractions.v] and is delivered here, twice over: as
   [FractionsF]'s own functor laws, and — read back through
   [FractionsF_fmap] — as [FractionsMap_id] and [FractionsMap_comp] on the
   hand-written lift.  Naturality of the hom-set bijection in [C] and in
   [D], also listed as not delivered there, is the [Adjunction] record's
   [to_adj_nat_l] and [to_adj_nat_r].

   WHAT IS NOT DELIVERED.  The triple is not shown to make [Grpd]
   reflective and coreflective in [Cat] in the sense of
   [Construction/Reflective.v]; that file's [Reflective] is stated over an
   inclusion of its own and connecting it to [Grpd_Incl] is separate work.
   Nothing here computes [Fractions C] for any concrete [C], so the
   left adjoint is exhibited but no localization is evaluated; and the
   monad [Grpd_Incl ◯ FractionsF] and comonad [Grpd_Incl ◯ Core] the two
   adjunctions generate are not named. 

   --------
   * * Riehl 4.1.15：伴随三重 [Fractions ⊣ Incl ⊣ Core]

   nLab：       https://ncatlab.org/nlab/show/core
   nLab：       https://ncatlab.org/nlab/show/localization
   维基百科：  https://en.wikipedia.org/wiki/Groupoid
   书籍：Riehl，《上下文中的范畴论》，第2版，§4.1，例4.1.15，
   印刷页137 (PDF 第157-158页) — 群类包含到范畴中在两边都有伴随，左边是分数范畴，右边是核心
   书籍：Mac Lane，《工作数学家的范畴论》，第2版，GTM 5，§IV.1 — 来自泛箭的伴随关系
   论文：Brown，《从群到群类：简要综述》，伦敦数学学会公告 19, 1987

   提供内容。将 Riehl 例子中的两部分，在同一个环境范畴中，作为两个 [Adjunction] 记录打包在同一个陈述中：

   [Fractions_Incl_Adjunction : Adjunction FractionsF Grpd_Incl]
   [Incl_Core_Adjunction      : Adjunction Grpd_Incl  Core]
   [riehl_4_1_15              : AdjointTriple FractionsF Grpd_Incl Core]右半部分属于 [Construction/Groupoid/Core.v]，保持不变且未移动；只有左半部分是新的，两者的环境都是 [Cat]，因此它们之间没有严格化，也没有比较函子。[Instance/Grpd.v] 的标题说左半部分“保持散文”，而 [Construction/Fractions.v] 的标题说三元组“在这里不是在一个环境上组装的”。这两个都被本文件取代，并且都已经在各自的标题中就地修正——Instance/Grpd.v 的句子现在指向这里，而 Construction/Fractions.v 保留了其对间隙的记载，作为关闭它的成本记录，因为它的严格陈述依然是更精确的解读，并且没有被削弱。左半部分如何构建，以及间隙是什么。路径是图书馆的标准路径——在每个对象上一个通用箭头，然后是 [Theory/Universal/Arrow.v] 的 [AdjunctionFromUniversalArrows]，它构建一个 LEFT 伴随，因此对于这一半是 RIGHT 方向（对于 [Incl ⊣ Core] 来说方向是错误的，这就是 [Construction/Groupoid/Core.v] 改为使用 hom-setoid 路径的原因）。唯一的阻碍是 `∃!` 条款的强度：[universal_arrow_from_UMP] 需要它在环境的 hom-setoid 上，[Grpd] 继承 [Cat] 的 [Functor_Setoid]，而 [Fractions_UMP_groupoid] 在 [Functor_StrictEq_Setoid] 提供了它。存在性沿着 [strict_equiv_implies_fun_equiv] 转移；唯一性没有，[Construction/Fractions/Weak.v] 针对自然同构重新证明了它。手握 [Fractions_UMP_weak]，这个文件就是汇编：通用箭头是 [FractionsProj C]，弱 [Unique] 记录直接传递，[Grpd] 的同态的西格玛在进入时贡献了 [(L; I)]，离开时进行了解构，因为 [Grpd] 的 [shom] 是 [True]。左伴随函子是在对象和态射上的局部化。
   [FractionsF : Cat ⟶ Grpd] 是函子
   [AdjunctionFromUniversalArrows] 生成的，它不仅仅是同构于分式范畴：[FractionsF_obj] 检查
   [fobj[FractionsF] C = (Fractions C; Fractions_IsGroupoid C)] 在
   [eq_refl] 上。在态射上，这个识别是到 `≈` 为止的，不能更精确，因为函子的局部化本身仅在自然同构下确定：[FractionsF_fmap] 识别 [fmap[FractionsF] F]
   与 [FractionsMap F] ，即 [FractionsProj D ◯ F] 沿投影的提升。[Fractions_unit_is_proj] 读出单元为 [FractionsProj C] ，这正是使得伴随成为局部化而不是其他某些左伴随的原因。[Fractions] 在 [C] 中的函子性被列为未交付，由 [Construction/Fractions.v] 交付，并在此呈现两次：作为 [FractionsF] 自身的函子定律，以及——通过 [FractionsF_fmap] 追溯——作为手写提升上的 [FractionsMap_id] 和 [FractionsMap_comp]。在 [C] 和 [D] 中，同样列为未交付的 Hom 集合双射的自然性，是 [Adjunction] 记录的 [to_adj_nat_l] 和 [to_adj_nat_r]。未交付的内容。该三重体并未显示使 [Grpd] 在 [Cat] 中反射且共反射，在 [Construction/Reflective.v] 的意义上；该文件的 [Reflective] 是基于其自身的包含而声明的，将其连接到 [Grpd_Incl] 是单独的工作。这里没有为任何具体的 [C] 计算 [Fractions C]，因此展示了左伴随函子，但没有评估任何局部化；并且两个伴随生成的单子 [Grpd_Incl ◯ FractionsF] 和余单子 [Grpd_Incl ◯ Core] 并未命名。
*)

(* * ** The object map: a localization is a groupoid / * ** 对象映射：一个定位是一个群 *)

(*
 [Construction/Fractions.v]'s [Fractions_IsGroupoid] is exactly the
 membership proof [Grpd] asks for, so the object map needs no work.  Note
 that this is a PAIR, per [Instance/Grpd.v]: the chosen inverse-assigning
 function is data. 

 --------
 [Construction/Fractions.v] 的 [Fractions_IsGroupoid] 正是 [Grpd] 所要求的成员证明，所以对象映射不需要任何操作。注意，根据 [Instance/Grpd.v]，这这是一个 PAIR：所选择的逆分配函数是数据。
*)

Definition frac_grpd (C : Category) : Grpd :=
  (Fractions C; Fractions_IsGroupoid C).

(*
   * ** The universal arrow

   [FractionsProj C : C ~{Cat}~> Grpd_Incl (frac_grpd C)] is universal from
   [C] to the inclusion.  The `∃!` is [Fractions_UMP_weak] at the target's
   own groupoid witness; the only manipulation is the sigma of [Grpd]'s
   homs, whose second component is [True]. 

   --------
   * ** 通用箭头

   [FractionsProj C : C ~{Cat}~> Grpd_Incl (frac_grpd C)] 从 [C] 到包含是通用的。`∃!` 是在目标自身的群体见证下的 [Fractions_UMP_weak]；唯一的操作是 [Grpd] 的同态的西格玛，其第二个分量是 [True]。
*)

Definition Fractions_universal_arrow (C : Cat) : UniversalArrow C Grpd_Incl.
Proof.
  unshelve eapply (universal_arrow_from_UMP C Grpd_Incl (frac_grpd C)
                     (FractionsProj C)).
  intros d' f.
  unshelve eapply Build_Unique.
  - exact (unique_obj (Fractions_UMP_weak (`2 d') f); I).
  - exact (unique_property (Fractions_UMP_weak (`2 d') f)).
  - intros [L HL] HF.
    exact (uniqueness (Fractions_UMP_weak (`2 d') f) L HF).
Defined.

(* * ** The left adjoint, and the adjunction / * ** 左伴随，以及伴随关系 *)

Definition FractionsF : Cat ⟶ Grpd :=
  LeftAdjointFunctorFromUniversalArrows Grpd_Incl Fractions_universal_arrow.

(*
 The generated functor's object map is the category of fractions itself,
 not a copy of it. 

 --------
 生成的函子对象映射是分数范畴本身，而不是它的一个副本。
*)

Example FractionsF_obj (C : Cat) : fobj[FractionsF] C = frac_grpd C := eq_refl.

Definition Fractions_Incl_Adjunction : Adjunction FractionsF Grpd_Incl :=
  AdjunctionFromUniversalArrows Grpd_Incl Fractions_universal_arrow.

(*
 The unit is the projection, up to `≈` -- the two differ only by the
 [Id] that [AdjunctionFromUniversalArrows] leaves in front of the
 universal arrow.  This is the counterpart of
 [Construction/Groupoid/Core.v]'s [core_counit_is_ForgetCore]. 

 --------
 该单元是投影，直到 `≈` -- 两者仅在 [AdjunctionFromUniversalArrows] 留在通用箭头前面的 [Id] 上有所不同。这是 [Construction/Groupoid/Core.v] 的 [core_counit_is_ForgetCore] 的对应物。
*)

Example Fractions_unit_is_proj (C : Cat) :
  @equiv _ (@Functor_Setoid C (Fractions C))
    (@unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C)
    (FractionsProj C).
Proof. apply fun_equiv_id_left. Qed.

(*
   * ** Functoriality of the localization, read on the hand-written lift

   [FractionsMap F] is the functor a reader would write down: lift
   [FractionsProj D ◯ F] along the projection out of [C], which is legal
   because [Fractions D] is a groupoid.  It agrees with the generated
   [fmap[FractionsF]] up to `≈`, and that is the sharpest available reading
   — [Cat]'s hom-setoid identifies functors only up to natural isomorphism,
   so no [eq_refl] is on offer here, unlike on objects. 

   --------
   * ** 局部化的函子性，在手写提升上阅读

   [FractionsMap F] 是读者会写下的函子：沿着从 [C] 出来的投影提升 [FractionsProj D ◯ F] ，这是合法的，因为 [Fractions D] 是一个群体。它和生成的 [fmap[FractionsF] 在 `≈` 上一致，这是可得的最精确的阅读——[Cat] 的 Hom-集合体仅在自然同构意义下识别函子，所以在这里没有 [eq_refl] 可用，不像在对象上那样。
*)

Definition FractionsMap {C D : Category} (F : C ⟶ D) : Fractions C ⟶ Fractions D :=
  FractionsLift (FractionsProj D ◯ F)
    (fun x y f => Fractions_IsGroupoid D _ _ (fmap[FractionsProj D ◯ F] f)).

Lemma FractionsF_fmap {C D : Cat} (F : C ~{Cat}~> D) :
  @equiv _ (@Functor_Setoid (Fractions C) (Fractions D))
    (`1 (fmap[FractionsF] F)) (FractionsMap F).
Proof.
  apply (uniqueness (ump_universal_arrows (Fractions_universal_arrow C)
                      (d:=frac_grpd D) (FractionsProj D ◯ F))
           (FractionsMap F; I)).
  exact (FractionsLift_factors_weak (Fractions_IsGroupoid D)
           (FractionsProj D ◯ F)).
Qed.

(*
 The two functor laws, transported onto [FractionsMap].  These are the
 "functoriality of [Fractions] in [C]" that [Construction/Fractions.v]
 listed as not delivered. 

 --------
 将两个函子定律，传递到 [FractionsMap]。这些是 [Construction/Fractions.v] 列为未实现的 [Fractions] 在 [C] 中的“函子性”。
*)

Corollary FractionsMap_id (C : Cat) :
  @equiv _ (@Functor_Setoid (Fractions C) (Fractions C))
    (FractionsMap (Id[C])) (Id[Fractions C]).
Proof.
  rewrite <- (FractionsF_fmap (Id[C])).
  exact (@fmap_id Cat Grpd FractionsF C).
Qed.

Corollary FractionsMap_comp {C D E : Cat} (G : D ~{Cat}~> E) (F : C ~{Cat}~> D) :
  @equiv _ (@Functor_Setoid (Fractions C) (Fractions E))
    (FractionsMap (G ◯ F)) (FractionsMap G ◯ FractionsMap F).
Proof.
  rewrite <- (FractionsF_fmap (G ◯ F)).
  rewrite <- (FractionsF_fmap G), <- (FractionsF_fmap F).
  exact (@fmap_comp Cat Grpd FractionsF C D E G F).
Qed.

(*
   * ** The triple

   A bundling record: an adjoint triple is a pair of adjunctions sharing
   their middle functor.  It is defined here because this is its first use
   in the tree — [Instance/Top/Forgetful.v]'s
   [discrete_forget_indiscrete_triple] is a tuple of transposition
   isomorphisms rather than of [Adjunction] records, because the universe
   stratification there makes the records unformable, so it cannot use
   this shape. 

   --------
   * ** 三重体

   一个捆绑记录：伴随三重体是一对共享其中间函子的伴随。之所以在这里定义它，是因为这是它在树中的首次使用——[Instance/Top/Forgetful.v] 的 [discrete_forget_indiscrete_triple] 是一组换位同构的元组，而不是 [Adjunction] 记录的元组，因为那里宇宙分层使得这些记录无法形成，所以不能使用这种形式。
*)

Record AdjointTriple {A B : Category}
  (L : A ⟶ B) (M : B ⟶ A) (R : A ⟶ B) : Type := {
  triple_left  : Adjunction L M;
  triple_right : Adjunction M R
}.

(*
 Riehl §4.1, Example 4.1.15, in one statement and over one ambient. 

 --------
 Riehl §4.1，例 4.1.15，在一个陈述中并且在一个环境上。
*)

Definition riehl_4_1_15 : AdjointTriple FractionsF Grpd_Incl Core :=
  {| triple_left  := Fractions_Incl_Adjunction;
     triple_right := Incl_Core_Adjunction |}.
