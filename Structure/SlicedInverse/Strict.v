Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Structure.SlicedInverse.

(*
   * * Sliced adjoint inverses, the strict half: the bridge to
   left-adjoint-left-inverses, and the dual of Proposition V.9.1 as a
   left-adjoint-right-inverse statement

   nLab: https://ncatlab.org/nlab/show/quotient+space
   nLab: https://ncatlab.org/nlab/show/topological+concrete+category

   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   GTM 5, Springer 1998, SS IV.4 (printed p. 94, the
   left-adjoint-left-inverse; p. 95, Exercise 3, the
   left-adjoint-right-inverse) and SS V.9, read from the page
   images: the quotient construction (book pp. 133-134, PDF
   pp. 142-143; catalog id maclane:V.9:construction3) and the one
   sentence stating the dual of Proposition 1 (book p. 134, PDF
   p. 143), the first clause of maclane:V.9:remark2, #458's
   catalog item.  The book numbers neither; the catalog ids are
   names, not book numbering.

   ** Background

   Mac Lane names an adjoint pair by which functor is the inverse and on
   which side.  In SS IV.4 a left adjoint [F] of [G] whose counit is the
   identity is a LEFT-ADJOINT-LEFT-INVERSE of [G]
   (Adjunction/LeftInverse.v), and a left adjoint [T] of [S] whose unit
   is the identity is a LEFT-ADJOINT-RIGHT-INVERSE of [S]
   (Theory/Equivalence/Strict.v).  SS V.9 adds the
   RIGHT-ADJOINT-RIGHT-INVERSE: the subspace topology is one for the
   sliced forgetful functor, and Proposition 1 builds equalizers from
   them (Structure/SlicedInverse.v, whose header carries the background
   essay).  Its dual -- one sentence of the book, “Now Proposition 1 was
   proved just from the axioms for a category, so its dual is also
   true” -- builds coequalizers from sliced left-adjoint-right-inverses,
   of which the quotient, or final, topology is the example (nLab,
   “quotient space”; Instance/Top/Subspace.v's [quotient_LARI]).

   Two of those names are one notion seen from its two ends.  “[S ⊣ R]
   with counit the identity” says that [R] is a
   right-adjoint-right-inverse of [S] AND that [S] is a
   left-adjoint-left-inverse of [R]; the library's two records differ
   only in which functor is the parameter.  This file makes that exact,
   and states the dual of Proposition 1 over the tree's existing
   [LeftAdjointRightInverse].  It is a satellite because its two donors
   are the only consumers of 14 modules (see Route and cost).

   ** What is delivered

   - [rari_lali : RightAdjointRightInverse S → LeftAdjointLeftInverse
   (rari_right P)] and [lali_rari : LeftAdjointLeftInverse R →
   RightAdjointRightInverse (lali_left P)], field for field, with
   [rari_lali_left] and [lali_rari_right] reading the moved functor
   back, and [rari_lali_rari] and [lali_rari_lali] stating both round
   trips as the identity.
   - [coequalizers_from_sliced_LARI]: the dual of Proposition 1, as the
   catalog's maclane:V.9:remark2 spells it out -- a faithful [G],
   coequalizers downstairs and a left-adjoint-right-inverse of every
   [Cosliced G a] give coequalizers upstairs.  It is
   Structure/SlicedInverse.v's [coequalizers_from_sliced_left_adjoints]
   applied to [lari_left] and [lari_adj]; the fields [lari_obj] and
   [lari_unit] do not occur in its body, so the right-inverse clause is
   not used, exactly as for Proposition 1.
   - What the clause buys, dually: [lari_preserves], [G] of the lifted
   coequalizer is a coequalizer of [fmap[G] f] and [fmap[G] g] (its
   object is [Q] up to the Leibniz [lari_under], its arrow [q] up to
   that cast, [lari_arrow_under]), assembled by
   [IsCoequalizer_transport]; [coequalizers_from_sliced_LARI_preserved]
   states it for every coequalizer the book form builds.
   - [prop1_dual_needs_faithfulness]: the dual with the faithfulness
   hypothesis deleted is refuted at [Erase Parallel : Parallel ⟶ _1],
   the main file's countermodel read in coslices.  Every coslice of
   [Parallel] has the initial object [(a; id)], the functor constant at
   it is a left-adjoint-right-inverse of each
   [Cosliced (Erase Parallel) a] ([erase_coslice_LARI]), [_1] has
   coequalizers ([One_HasCoequalizers]), and the parallel pair has no
   coforking arrow ([parallel_pair_uncoforked],
   [Parallel_no_coequalizers]); [cosliced_LARI_without_faithfulness]
   packages the four facts.

   ** Strengths

   Holding at [eq_refl], as [Example]s: [rari_lali_left],
   [lali_rari_right], the two round trips [rari_lali_rari] and
   [lali_rari_lali] (record eta, the records having primitive
   projections), [coequalizers_from_sliced_LARI_obj] and
   [coequalizers_from_sliced_LARI_arrow] (the coequalizer built is
   [lari_left (L y)] of the downstairs one, on the nose), and
   [lari_coeq_obj] and [lari_coeq_arrow] (the pointwise form).  Eight in
   all.  Leibniz but not [eq_refl]: [lari_under], from the field
   [lari_obj], and [coslice_id_cast_1], the coslice twin of the main
   file's [slice_id_cast_1], by [destruct].  Up to [≈]:
   [lari_arrow_under].  The four [Defined]
   ([IsCoequalizer_transport], the second obligation of
   [One_HasCoequalizers], [erase_coslice_adj], [erase_coslice_LARI])
   carry data and are kept [Defined] by the data convention; flipped to
   [Qed] in a scratch copy together with the main file's six, both files
   compile, so none is load-bearing.

   ** Universes, measured by About on every constant

   Every constant over two categories binds them at one hom level,
   [Category@{oA h h}] and [Category@{oX h h}] (or [oC]), in the binder;
   the identification is the records' own (a functor in each direction,
   and [Adjunction]'s block) and the main file's, and is inherited.
   Across the 39 constants of this file (Print Module and every
   [Program] obligation) the About log has zero word-bounded [Set] and no
   block carries an equation; in every block whose constant binds
   categories, each strict bound relates a hom level to an auxiliary
   universe that no category binder names.  [One_HasCoequalizers] is
   annotated [@{o h}] for the reason the main file measured for
   [One_HasEqualizers], and reads [HasCoequalizers@{o h} _1@{o h h}].
   [prop1_dual_needs_faithfulness] quantifies over
   [A : Category@{u4 u5 u5}] and [X : Category@{u2 u5 u5}] with the one
   strict bound [u5 < u3].  The main file's identification of the two
   slice-auxiliary universes holds here too: [coequalizers_from_sliced_LARI]
   reads [Cosliced@{oA h oX h u3 u3 u6 u7}], and the refutation
   [Cosliced@{u4 u5 u2 u5 u3 u3 u u1}].

   ** Route and cost

   Closure: 56 [Category.*] modules excluding this file ([Print
   Libraries] on its [Require] list).  Without
   Theory/Equivalence/Strict.v and Adjunction/LeftInverse.v the same list
   gives 42, Structure/SlicedInverse.v and its own closure; so the two
   donors cost 14, the figure the main file's header measures from its
   side (41 to 55).  Dropping each [Require] alone:
   Structure/SlicedInverse.v costs 5, Theory/Equivalence/Strict.v 2
   (Adjunction/LeftInverse.v, which it requires, is required here too),
   and the other thirteen 0.  [IsCoequalizer_transport] is rebuilt
   rather than consumed: Monad/Monadicity/Beck.v's
   [coequalizer_along_iso] moves an [IsCoequalizer] along an isomorphism
   of apexes (closed, [Defined]) and would serve through
   Construction/Quotient.v's [id_cast_iso], but requiring Beck.v would
   add 12 modules (56 to 68), measured the same way.  [lari_under] is
   stated
   as [Q = G (...)] rather than in [rari_over]'s orientation because the
   unit, not the counit, is the transported identity here, and
   [lari_unit] already carries the [eq_sym].

   ** Prior art, measured

   Theory/Equivalence/Strict.v's own NOT DELIVERED list includes “no
   comparison of [LeftAdjointRightInverse] with Adjunction/LeftInverse.v's
   [LeftAdjointLeftInverse] beyond naming the pair”; that remains true --
   the comparison made here is between the new
   [RightAdjointRightInverse] and [LeftAdjointLeftInverse], the two
   records that are one notion.  Collisions: see the main file.

   ** NOT DELIVERED

   - No comparison of [LeftAdjointRightInverse] with the other two
   records (it is a different notion: the UNIT is the identity).
   - No concrete witness in this file: the quotient topology is
   Instance/Top/Subspace.v's [quotient_LARI], at [Cosliced PForget X],
   and the coequalizers it gives are that file's
   [PTop_HasCoequalizers], built by [coequalizers_from_sliced_LARI].
   - No transport of the right-inverse clause's consequences along the
   bridges (e.g. [lali_Full] and [lali_Faithful] of
   Adjunction/LeftInverse.v read as statements about [rari_right]);
   they apply through [rari_lali] but are not restated. 

   --------
   * * 切片伴随逆，严格一半：通向左伴随左逆的桥梁，以及命题 V.9.1 的对偶作为左伴随右逆的陈述

   nLab: https://ncatlab.org/nlab/show/quotient+space
   nLab: https://ncatlab.org/nlab/show/topological+concrete+category书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，GTM 5，Springer 1998，第IV.4节（印刷页第94页，左伴随左逆；第95页，练习3，左伴随右逆）和第V.9节，从页面图像阅读：商构造（书页133-134，PDF页142-143；目录ID maclane:V.9:construction3）以及一句话说明命题1的对偶（书页134，PDF页143），maclane:V.9:remark2的第一条，#458的目录项。书中没有标注编号；目录ID是名称，不是书本编号。

   ** 背景麦克莱恩通过哪个函子是逆函子以及在什么时候来命名一个伴随对。在 SS IV.4 中，一个左伴随 [F] 对于 [G]，其余单位是恒等，是 [G] 的左伴随-左逆 (Adjunction/LeftInverse.v)，以及一个左伴随 [T] 对于 [S]，其单位是恒等，是 [S] 的左伴随-右逆 (Theory/Equivalence/Strict.v)。SS V.9 添加了右伴随-右逆：切片遗忘函子的一种子空间拓扑，并且命题 1 从它们构建了等化子 (Structure/SlicedInverse.v，其标题包含背景文章)。它的对偶——书中的一句话，“现在命题1仅从一个范畴的公理就已被证明，因此它的对偶也成立”——是从切片的左伴随右逆构建共等化子，其中商拓扑或终极拓扑就是一个例子（nLab，“商空间”；Instance/Top/Subspace.v的[quotient_LARI]）。这些名称中的两个是从两个端点看到的同一个概念。 “以单位元为恒等映射” 表示 [R] 是 [S] 的右伴随-右逆，而 [S] 是 [R] 的左伴随-左逆；库中的两个记录仅在参数是哪个函子上有所不同。此文件精确地表达了这一点，并陈述了树上现有 [LeftAdjointRightInverse] 的命题1的对偶。它是一个卫星文件，因为其两个捐赠者是14个模块的唯一使用者（见路线和成本）。

   ** 交付的内容是什么- [rari_lali：RightAdjointRightInverse S → LeftAdjointLeftInverse (rari_right P)] 和 [lali_rari：LeftAdjointLeftInverse R → RightAdjointRightInverse (lali_left P)]，字段对应字段，使用 [rari_lali_left] 和 [lali_rari_right] 将移动的函子读回，[rari_lali_rari] 和 [lali_rari_lali] 将两个往返都表示为恒等。- [coequalizers_from_sliced_LARI]：命题 1 的对偶，如目录中的 maclane:V.9:remark2 所述——一个忠实的 [G]，下方的余等化器以及每个 [Cosliced G a] 的左伴随-右逆给出上方的余等化器。它是 Structure/SlicedInverse.v 中的 [coequalizers_from_sliced_left_adjoints]，应用于 [lari_left] 和 [lari_adj]；字段 [lari_obj] 和 [lari_unit] 在其主体中未出现，因此未使用右逆条款，正如命题 1 所示。- 该条款购买的内容，双重地：升起的等化器的 [lari_preserves]、[G] 是 [fmap[G] f] 和 [fmap[G] g] 的等化器（它的对象是 [Q]，直到莱布尼茨 [lari_under]，它的箭头是 [q]，直到那个类型转换，[lari_arrow_under]），由 [IsCoequalizer_transport] 组装； [coequalizers_from_sliced_LARI_preserved] 表明它适用于书本形式构建的每个等化器。- [prop1_dual_needs_faithfulness]：删除忠实性假设的对偶在 [Erase Parallel : Parallel ⟶ _1] 被驳斥，主文件的反例在余切片中读取。每一个 [Parallel] 的余切片都有初始对象 [(a; id)]，对应常值函子是每一个 [Cosliced (Erase Parallel) a]（[erase_coslice_LARI]）的左伴随-右逆映射，[_1] 具有余等化子（[One_HasCoequalizers]），并且该平行对没有余叉箭头（[parallel_pair_uncoforked]，[Parallel_no_coequalizers]）；[cosliced_LARI_without_faithfulness] 打包了这四个事实。

   ** 强项在 [eq_refl] 持有，作为 [Example] 的：[rari_lali_left]，[lali_rari_right]，两个往返 [rari_lali_rari] 和 [lali_rari_lali]（记录 eta，记录具有原始投影），[coequalizers_from_sliced_LARI_obj] 和 [coequalizers_from_sliced_LARI_arrow]（建立的余等化器是 [lari_left (L y)] 的楼下那个，完全匹配），以及 [lari_coeq_obj] 和 [lari_coeq_arrow]（逐点形式）。总共八个。莱布尼茨但不是 [eq_refl]：[lari_under]，来自字段 [lari_obj]，以及 [coslice_id_cast_1]，主文件的 [slice_id_cast_1] 的余切孪生，由 [destruct] 得到。最多到 [≈]：[lari_arrow_under]。这四个 [Defined]（[IsCoequalizer_transport]，[One_HasCoequalizers] 的第二个义务，[erase_coslice_adj]，[erase_coslice_LARI]）携带数据，并根据数据约定保持 [Defined]；在一个临时副本中与主文件的六个一起翻转至 [Qed]，两个文件都能编译，因此没有一个是承重的。** 宇宙，通过每一个常数的约数进行测量每个跨越两个类别的常量在一个同态层级上绑定它们，[Category@{oA h h}] 和 [Category@{oX h h}]（或 [oC]）在绑定器中；
   识别是记录自身的（每个方向的函子，以及 [Adjunction] 的区块）和主文件的，并且是继承的。在该文件的 39 个常量中（打印模块和每个 [Program] 义务），关于日志没有零字界 [Set]，并且没有区块携带方程；在每个其常量绑定类别的区块中，每个严格绑定将同态层级关联到没有类别绑定器命名的辅助宇宙。[One_HasCoequalizers] 被注释为 [@{o h}]，原因是主文件为 [One_HasEqualizers] 测量，并读取 [HasCoequalizers@{o h} _1@{o h h}]。[prop1_dual_needs_faithfulness] 对 [A : Category@{u4 u5 u5}] 和 [X : Category@{u2 u5 u5}] 进行量化，带有一个严格绑定 [u5 < u3]。主文件对两个切片辅助宇宙的识别在这里也适用：[coequalizers_from_sliced_LARI] 读取 [Cosliced@{oA h oX h u3 u3 u6 u7}]，反驳 [Cosliced@{u4 u5 u2 u5 u3 u3 u u1}]。

   ** 路线和成本闭包：56 个 [Category.*] 模块，不包括此文件（其 [Require] 列表中的 [Print Libraries]）。如果没有 Theory/Equivalence/Strict.v 和 Adjunction/LeftInverse.v，相同的列表给出 42，Structure/SlicedInverse.v 及其自身的闭包；因此两个捐赠者的成本为 14，这是主文件的头从其侧面测量的数字（从 41 到 55）。单独删除每个 [Require]：Structure/SlicedInverse.v 的成本为 5，Theory/Equivalence/Strict.v 为 2（Adjunction/LeftInverse.v，它所需要的，这里也需要），其余十三个为 0。[IsCoequalizer_transport] 被重建而不是消耗：Monad/Monadicity/Beck.v 的 [coequalizer_along_iso] 沿着顶点的同构 (闭合，[Defined]) 移动 [IsCoequalizer]，并且可以通过 Construction/Quotient.v 的 [id_cast_iso] 服务，但需要 Beck.v 会增加 12 个模块（从 56 到 68），以相同方式测量。[lari_under] 被陈述为 [Q = G (...)] 而不是 [rari_over] 的方向，因为这里传递的身份是单位而不是余单位，并且 [lari_unit] 已经携带了 [eq_sym]。

   ** 先前技术，以测量方式Theory/Equivalence/Strict.v 自身的未交付列表包括“没有对 [LeftAdjointRightInverse] 与 Adjunction/LeftInverse.v 的 [LeftAdjointLeftInverse] 进行比较，除了命名这对”；这一点仍然成立——这里进行的比较是新 [RightAdjointRightInverse] 与 [LeftAdjointLeftInverse] 之间的比较，这两个记录是同一概念。冲突：参见主文件。

   ** 未交付- 没有将 [LeftAdjointRightInverse] 与其他两个记录进行比较（它是一个不同的概念：UNIT 是身份）。
   - 本文件中没有具体的证据：商拓扑是 Instance/Top/Subspace.v 中的 [quotient_LARI] ，位于 [Cosliced PForget X] ，它所给出的等化器是该文件中的 [PTop_HasCoequalizers]，由 [coequalizers_from_sliced_LARI] 构建。
   - 没有沿桥传递右逆条件的结果（例如，在 Adjunction/LeftInverse.v 中 [lali_Full] 和 [lali_Faithful] 被作为有关 [rari_right] 的陈述来读取）；它们通过 [rari_lali] 应用，但没有重述。
*)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** Right-adjoint-right-inverses ARE left-adjoint-left-inverses / * ** 右伴随-右逆就是左伴随-左逆 *)

(*
 The two records carry the same four fields; only the parameter moves,
 from the left adjoint to the right one. 

 --------
 这两条记录包含相同的四个字段；唯一的变化是参数从左伴随移到了右伴随。
*)
Definition rari_lali@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C}
  (P : RightAdjointRightInverse S) : LeftAdjointLeftInverse (rari_right P) :=
  {| lali_left := S; lali_adj := rari_adj P;
     lali_obj := rari_obj P; lali_counit := rari_counit P |}.

Definition lali_rari@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X}
  (P : LeftAdjointLeftInverse R) : RightAdjointRightInverse (lali_left P) :=
  {| rari_right := R; rari_adj := lali_adj P;
     rari_obj := lali_obj P; rari_counit := lali_counit P |}.

Example rari_lali_left@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_left (rari_lali P) = S := eq_refl.

Example lali_rari_right@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X} (P : LeftAdjointLeftInverse R) :
  rari_right (lali_rari P) = R := eq_refl.

(* Both round trips are the identity on the nose (record eta). / 两个往返在本质上都是恒等映射（记录 eta）。 *)
Example rari_lali_rari@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_rari (rari_lali P) = P := eq_refl.

Example lali_rari_lali@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} {R : A ⟶ X} (P : LeftAdjointLeftInverse R) :
  rari_lali (lali_rari P) = P := eq_refl.

(* * ** The dual of Proposition 1, over left-adjoint-right-inverses / * ** 命题1的对偶，关于左伴随右逆元 *)

(*
 Coequalizers from sliced left-adjoint-right-inverses, over
 Theory/Equivalence/Strict.v's [LeftAdjointRightInverse].  The
 right-inverse clause is not consulted: only [lari_left] and [lari_adj]
 occur in the body. 

 --------
 从切片左伴随右逆的余等化子，在 Theory/Equivalence/Strict.v 的 [LeftAdjointRightInverse] 上。右逆条款未被使用：在主体中只出现 [lari_left] 和 [lari_adj]。
*)
Definition coequalizers_from_sliced_LARI@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) :
  @HasCoequalizers A :=
  coequalizers_from_sliced_left_adjoints G
    (fun a => lari_left (L a)) (fun a => lari_adj (L a)).

Example coequalizers_from_sliced_LARI_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)
    = `1 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example coequalizers_from_sliced_LARI_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g))
    = `2 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* * ** What the right-inverse clause adds, dually / * ** 右逆元子句所增加的内容，对偶地 *)

Lemma coslice_id_cast_1@{o h +} {C : Category@{o h h}} {u : C}
  {p q : @Coslice C u} (e : p = q) :
  `1 (@id_cast (@Coslice C u) p q e)
    = @id_cast C (`1 p) (`1 q) (f_equal (@projT1 _ _) e).
Proof. destruct e; reflexivity. Qed.

(* A coequalizer moved along a Leibniz equation of apexes. / 一个余等化器沿着顶点的莱布尼茨方程移动。 *)
Definition IsCoequalizer_transport@{o h +} {C : Category@{o h h}}
  {a b : C} {f g : a ~> b} {q q' : C} {e : b ~> q} {e' : b ~> q'}
  (p : q = q') :
  e' ≈ id_cast p ∘ e → IsCoequalizer f g q e → IsCoequalizer f g q' e'.
Proof.
  destruct p; simpl; intros He E.
  rewrite id_left in He.
  unshelve econstructor.
  - rewrite He; exact (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (coeq_desc E h Hh)).
    + rewrite He; exact (unique_property (coeq_desc E h Hh)).
    + intros v Hv; apply (uniqueness (coeq_desc E h Hh)).
      rewrite <- He; exact Hv.
Defined.

Section LARIPreserves.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {Q : X} (q : G y ~> Q).
Context (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q).
Context (L : LeftAdjointRightInverse (Cosliced G y)).

Definition lari_universal :
  UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y) :=
  adj_unit_universal_op (lari_adj L) (Q; q).

Example lari_coeq_obj :
  cosliced_coeq_obj G q lari_universal = `1 (lari_left L (Q; q)) := eq_refl.

Example lari_coeq_arrow :
  cosliced_coeq_arrow G q lari_universal = `2 (lari_left L (Q; q)) := eq_refl.

(* The lifted object sits under Q: Leibniz, from the field [lari_obj]. / 被提升的物体位于 Q: 莱布尼茨，来自字段 [lari_obj] 下。 *)
Definition lari_under : Q = G (`1 (lari_left L (Q; q))) :=
  f_equal (@projT1 _ _) (eq_sym (lari_obj L (Q; q))).

Lemma lari_arrow_under :
  fmap[G] (`2 (lari_left L (Q; q))) ≈ id_cast lari_under ∘ q.
Proof using Type.
  pose proof (`2 (@unit _ _ _ _ (lari_adj L) (Q; q))) as H; simpl in H.
  rewrite H.
  apply compose_respects; [|reflexivity].
  transitivity (`1 (@id_cast (@Coslice X (G y)) _ _
                     (eq_sym (lari_obj L (Q; q))))).
  - exact (lari_unit L (Q; q)).
  - rewrite (coslice_id_cast_1 (eq_sym (lari_obj L (Q; q)))).
    reflexivity.
Qed.

(* G carries the lifted coequalizer onto a coequalizer of the images. / G 将提升的共同余子对象映射到像的共同余子对象上。 *)
Definition lari_preserves :
  IsCoequalizer (fmap[G] f) (fmap[G] g)
    (G (`1 (lari_left L (Q; q)))) (fmap[G] (`2 (lari_left L (Q; q)))) :=
  IsCoequalizer_transport lari_under lari_arrow_under E.

End LARIPreserves.

Definition coequalizers_from_sliced_LARI_preserved@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  IsCoequalizer (fmap[G] f) (fmap[G] g)
    (G (`1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)))
    (fmap[G] (`1 (`2 (@coeq A (coequalizers_from_sliced_LARI G L)
                         x y f g)))) :=
  lari_preserves G f g _ (`2 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))
    (L y).

(* * ** Faithfulness cannot be dropped from the dual either / * ** 忠诚也不能从双重关系中被丢掉 *)

Lemma parallel_pair_uncoforked {q : Parallel} (e : ParY ~{Parallel}~> q) :
  e ∘ par_arrow_one ≈ e ∘ par_arrow_two → False.
Proof.
  destruct q, e as [b h].
  - destruct (ParHom_Y_X_absurd _ h).
  - inversion h; subst. simpl. discriminate.
Qed.

Definition Parallel_no_coequalizers : @HasCoequalizers Parallel → False :=
  fun H =>
    parallel_pair_uncoforked
      (`1 (`2 (@coeq Parallel H _ _ par_arrow_one par_arrow_two)))
      (cofork (`2 (`2 (@coeq Parallel H _ _ par_arrow_one par_arrow_two)))).

Program Definition One_HasCoequalizers@{o h} :
  @HasCoequalizers _1@{o h h} := {|
  coeq := fun x y f g => (y; (id; {| cofork := _; coeq_desc := _ |}))
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation.
  intros x y f g z h Hh.
  exists h.
  - destruct h; reflexivity.
  - intros v _; destruct h, v; reflexivity.
Defined.

Lemma coslice_one_hom_eq@{o h +} (u : _1@{o h h})
  (x y : @Coslice _1@{o h h} u) (f g : x ~> y) : f ≈ g.
Proof. destruct f as [[] ?], g as [[] ?]; reflexivity. Qed.

Section EraseCoslice.

Context (a : Parallel).

#[local] Notation B := (Erase Parallel).

(*
 The left adjoint of [Cosliced B a] is constant at the initial object
 (a; id) of the coslice under [a]. 

 --------
 [Cosliced B a] 的左伴随在 [a] 下的余切中的初始对象 (a; id) 处是常数。
*)
Program Definition erase_coslice_left :
  @Coslice _1 (B a) ⟶ @Coslice Parallel a := {|
  fobj := fun _ => (a; id);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; intros ? ? ?; reflexivity. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

Program Definition erase_coslice_hom_iso (c : @Coslice _1 (B a))
  (h : @Coslice Parallel a) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice Parallel a) (erase_coslice_left c) h;
       is_setoid := @homset (@Coslice Parallel a) (erase_coslice_left c) h |}
    {| carrier := @hom (@Coslice _1 (B a)) c (Cosliced B a h);
       is_setoid := @homset (@Coslice _1 (B a)) c (Cosliced B a h) |} := {|
  to := {| morphism := fun _ => (ttt; _) |};
  from := {| morphism := fun _ => (`2 h; _) |}
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; exact (symmetry (@id_right Parallel _ _ (`2 h))). Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; intros [[] Hv]; reflexivity. Qed.
Next Obligation.
  intros; intros [v Hv].
  change (`2 h ≈ v).
  rewrite Hv; apply id_right.
Qed.

Definition erase_coslice_adj : erase_coslice_left ⊣ Cosliced B a.
Proof.
  unshelve eapply
    (@Build_Adjunction' _ _ erase_coslice_left (Cosliced B a)
       erase_coslice_hom_iso).
  - intros x y z f g; simpl.
    reflexivity.
  - intros x y z f g; simpl.
    reflexivity.
Defined.

Definition erase_coslice_LARI : LeftAdjointRightInverse (Cosliced B a).
Proof.
  unshelve refine {| lari_left := erase_coslice_left;
                     lari_adj := erase_coslice_adj |}.
  - intros [[] []]; reflexivity.
  - intros c; apply coslice_one_hom_eq.
Defined.

End EraseCoslice.

Definition cosliced_LARI_without_faithfulness :
  (∀ a : Parallel, LeftAdjointRightInverse (Cosliced (Erase Parallel) a))
  * @HasCoequalizers _1
  * (Faithful (Erase Parallel) → False)
  * (@HasCoequalizers Parallel → False) :=
  (erase_coslice_LARI, One_HasCoequalizers, Erase_Parallel_not_faithful,
   Parallel_no_coequalizers).

(* The dual with the faithfulness hypothesis deleted is false. / 删除了忠诚假设的对偶是错误的。 *)
Definition prop1_dual_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasCoequalizers X →
     (∀ a : A, LeftAdjointRightInverse (Cosliced G a)) →
     @HasCoequalizers A)
  → False :=
  fun P => Parallel_no_coequalizers
             (P Parallel _1 (Erase Parallel) One_HasCoequalizers
                erase_coslice_LARI).
