(**
* Coproducts as the left adjoint of the diagonal functor

    Mac Lane, "Categories for the Working Mathematician", §IV.1, p. 84, and
    Awodey, "Category Theory", §9.3, p. 225, are cited BY LOCATION ONLY: the
    printed text at those two locations was not consulted while this file was
    written, and both locations are the ones recorded in issue
    jwiegley/category-theory#351, which this file answers.

    The tree already carries the other half of the triple: the binary product
    bifunctor is a RIGHT adjoint of the binary diagonal
    [Δ = Diagonal_Product C : C ⟶ C ∏ C], namely
    Adjunction/Diagonal/Product.v's [Diagonal_Product_Adjunction], over the
    bifunctor Functor/Product/Internal.v with its notation [×(C)]
    (Functor/Product/Internal.v).  Here the coproduct bifunctor [+(C)] is
    built and shown to be a LEFT adjoint of that same diagonal, with the
    statement read in [C] itself: no [^op] occurs in the type of
    [Diagonal_Coproduct_Adjunction].  The unit and counit of the adjunction
    are then named and identified -- the pair of injections, and the folding
    map [id ▽ id].

    ON THE DUALITY ROUTE.  Structure/Cocartesian.v defines [Cocartesian C]
    to BE [@Cartesian (C^op)], so the product adjunction taken at [C^op] and
    pushed through Adjunction/Opposite.v's [Opposite_Adjunction] is already
    a term, of type [×(C^op)^op ⊣ (Diagonal_Product C^op)^op].  Two
    observations about that term were checked at the Rocq prompt while this
    file was prepared; they are not re-checked by the build.  Its right-hand
    endpoint is already the covariant one: [Opposite_Functor (Diagonal_Product
    (Opposite C))] and [Diagonal_Product C] are equal by [reflexivity], at
    Leibniz equality.  Its left-hand endpoint is not: [Opposite_Functor
    (×(Opposite C))] and [+(C)] do not unify: ascribing the whole record is
    rejected with a bare top-level type mismatch (no field is named), and
    comparing the two functor records shows [fobj] and [fmap] converging while
    all three opaque [Program]-obligation fields ([fmap_respects], [fmap_id],
    [fmap_comp]) differ.  So the coproduct bifunctor has
    to be given directly on either route, and the dualized term reaches the
    covariant statement by re-assembling Theory/Adjunction.v's
    [Adjunction] class field by field (a [Build_Adjunction] with five
    projections, which does typecheck, since no field of that class mentions
    [fmap_respects]).  The route taken below gives the two transposes
    directly, mirroring Adjunction/Diagonal/Product.v field for field; the
    statement, the transposes and the identification lemmas are then all read
    in [C], and the obligations close by the coproduct laws of
    Structure/Cocartesian.v.

    NOT TO BE CONFUSED WITH Functor/Coproduct.v's [CoproductFunctor], which
    is the fold out of the coproduct CATEGORY [C ∐ C]; the bifunctor here has
    the product category [C ∏ C] as its domain. 

--------
* 余积作为对角函子的左伴随

Mac Lane，“工作数学家的类别”，§IV.1，p。 84、和
 Awodey，“范畴论”，§9.3，p。 225，仅按地点引用：
 当该文件被查阅时，没有查阅这两个位置的打印文本
 书面的，并且两个位置都是在问题中记录的位置
 jwiegley/category-theory#351，这个文件回答了这个问题。

树已经携带了三元组的另一半：二元乘积
 双函子是二元对角线的右伴随
 [Δ = Diagonal_Product C : C ⟶ C ∏ C]，即
 Adjunction/Diagonal/Product.v 的 [Diagonal_Product_Adjunction]，
 bifunctor Functor/Product/Internal.v 及其符号 [×(C)]
 （函子/产品/内部.v）。 这里的联积双函子 [+(C)] 是
 构建并显示为同一对角线的左伴随，其中
 在 [C] 本身中读取的语句：类型中没有出现 [^op]
 [Diagonal_Coproduct_Adjunction]。 附加词的单位和单位
 然后命名并识别——注射对和折叠
 地图 [id ▽ id]。

在二元路线上。 Structure/Cocartesian.v 定义 [Cocartesian C]
 为 [@Cartesian (C^op)]，因此 [C^op] 采取的产品附加和
 通过 Adjunction/Opposite.v 的 [Opposite_Adjunction] 已经推出
 [×(C^op)^op ⊣ (Diagonal_Product C^op)^op] 类型的术语。 两个
 在 Rocq 提示符下检查了对该术语的观察结果，而这
 文件已准备好； 它们不会被构建重新检查。 它的右手
 端点已经是协变端点：[Opposite_Functor (Diagonal_Product
 (C))] 和 [Diagonal_Product C] 等于 [reflexivity]，在
 莱布尼茨平等。
它的左端点不是：[Opposite_Functor
 (×(C 相反))] 和 [+(C)] 不统一：将整个记录归因于
 因顶级类型不匹配而被拒绝（没有命名字段），并且
 比较两个函子记录表明 [fobj] 和 [fmap] 收敛，而
 所有三个不透明 [Program] 义务字段（[fmap_respects]、[fmap_id]、
 [fmap_comp]) 有所不同。 所以联积双函子有
 直接在任一路径上给出，并且对偶项达到
 通过重新组装 Theory/Adjunction.v 的协变语句
 [Adjunction] 逐个字段进行分类（[Build_Adjunction] 有五个
 投影，它会进行类型检查，因为该类没有任何字段提到
 [fmap_respects]）。
下面采取的路线给出了两个转置
 直接，镜像 Adjunction/Diagonal/Product.v 字段到字段； 的
 语句、转置和识别引理都会被读取
 在 [C] 中，以及与以下联积定律相关的义务
 结构/Cocartesian.v.

不要与 Functor/Coproduct.v 的 [CoproductFunctor] 混淆，它
 是联产品 CATEGORY [C ∐ C] 的折叠； 这里的双函子有
 产品类别 [C ∏ C] 作为其域。 
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.

Generalizable All Variables.

(** ** The coproduct bifunctor  / ** 余积双函子*)

(**
[+(C) : C ∏ C ⟶ C], the dual of Functor/Product/Internal.v's [×(C)].
    On a pair of morphisms it is the copairing of the two injections after
    each component. 

--------
[+(C) : C ∏ C ⟶ C]，Functor/Product/Internal.v 的 [×(C)] 的双重版本。 
对于一对态射，它是在
 每个组件。 
*)
#[export]
Program Instance InternalCoproductFunctor `(C : Category) `{@Cocartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p + snd p;
  fmap := fun _ _ p => (inl ∘ fst p) ▽ (inr ∘ snd p)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  (*
[merge_comp] (Structure/Cocartesian.v) reads
     [(g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h]: the common factor stands on the LEFT,
     the mirror of [fork_comp]'s right one.  The script below therefore uses
     [comp_assoc] forward before [inl_merge]/[inr_merge]; the corresponding
     step of Functor/Product/Internal.v uses it backwards. 

--------
[merge_comp]（Structure/Cocartesian.v）读取
 [(g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h]：公因数位于左侧，
 [fork_comp] 右侧镜子。 因此下面的脚本使用
 [comp_assoc] 在 [inl_merge]/[inr_merge] 之前前进； 相应的
 Functor/Product/Internal.v 的步骤向后使用它。 
*)
  simpl in *.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge, inr_merge.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Notation "+( C )" := (@InternalCoproductFunctor C _)
  (at level 0, format "+( C )") : functor_scope.

(** ** The adjunction  / ** 附属物*)

(**
[+(C) ⊣ Δ].  The forward transpose splits a map out of a coproduct into
    its two restrictions, [f ↦ (f ∘ inl, f ∘ inr)]; the inverse copairs a pair
    of maps, [g ↦ fst g ▽ snd g].  Read in [C^op] these are the transposes of
    Adjunction/Diagonal/Product.v.

    The global obligation tactic of Lib/Tactics.v ([cat_simpl]) is left in
    force, as in the product file, and five scripts remain: the [Proper] of
    the inverse transpose, one round trip, and three of the four naturality
    squares.  Program re-runs the obligation tactic as obligations become
    unblocked, so these five scripts are not in bijection with the five fields
    of Theory/Adjunction.v.  The first three mirror
    Adjunction/Diagonal/Product.v with [merge] for [fork].
    The last two are [merge_comp] orientation steps, written out explicitly.
    [unmerge] (Structure/Cocartesian.v -- an unfold/simpl prefix followed
    by [repeat (rewrite <- !merge_comp; cat; rewrite <- !comp_assoc; cat)])
    closes the second of them but not the first: its final rewrite
    right-associates composites, the direction suited to [fork_comp]'s common
    RIGHT factor, while [merge_comp] factors on the LEFT.  Both are written
    out so the orientation is visible rather than split across two styles. 

--------
[+(C) ⊣ Δ]。 前向转置将余积中的映射拆分为
 它的两个限制，[f ↦ (f ∘ inl, f ∘ inr)]； 逆偶配对
 地图，[g ↦ fst g ▽ snd g]。 在 [C^op] 中读取这些是转置
 附加/对角线/乘积.v.

Lib/Tactics.v ([cat_simpl]) 的全局义务策略保留在
 强制，如产品文件中所示，还剩下五个脚本：[Proper]
 逆转置、一次往返和四种自然性中的三种
 正方形。 当义务变为时，程序重新运行义务策略
 畅通无阻，因此这五个脚本与五个字段不存在双射
 理论/附加.v。 前三镜
 Adjunction/Diagonal/Product.v 与 [merge] 适用于 [fork]。 
最后两个是 [merge_comp] 定向步骤，已明确写出。 
[unmerge]（Structure/Cocartesian.v——后面跟着一个展开/简化前缀
 由 [repeat (rewrite <- !merge_comp; cat; rewrite <- !comp_assoc; cat)] 提供）
 关闭第二个但不是第一个：它的最终重写
 右联复合材料，适合[fork_comp]通用方向
 右侧因子，而 [merge_comp] 左侧因子。 两个都写了
 以便方向可见，而不是分为两种样式。 
*)
#[export]
Program Instance Diagonal_Coproduct_Adjunction (C : Category) `{@Cocartesian C} :
  +(C) ⊣ Diagonal_Product C := {
  adj := fun _ _ =>
    {| to   := {| morphism := fun f => (f ∘ inl, f ∘ inr) |}
     ; from := {| morphism := fun f => fst f ▽ snd f |} |}
}.
(*
The inverse transpose respects the pairwise equivalence of [C ∏ C]
   (Construction/Product.v), by [merge_respects]
   (Structure/Cocartesian.v). 

--------
反转置遵循 [C ∏ C] 的成对等价性
 （建筑/产品.v），作者：[merge_respects]
 （结构/Cocartesian.v）。 
*)
Next Obligation. proper; apply merge_respects; auto. Qed.
(*
Round trip [(x ∘ inl) ▽ (x ∘ inr) ≈ x]: [merge_comp] factors [x] out,
   leaving [x ∘ (inl ▽ inr)], and [cat] finishes with [merge_inl_inr]
   (Structure/Cocartesian.v) and the identity law. 

--------
往返 [(x ∘ inl) ▽ (x ∘ inr) ≈ x]：[merge_comp] 将 [x] 分解，
 离开 [x ∘ (inl ▽ inr)]，[cat] 结束于 [merge_inl_inr]
 （Structure/Cocartesian.v）和恒等律。 
*)
Next Obligation. rewrite merge_comp; cat. Qed.
(*
Naturality in the [C ∏ C] argument: one equation per component, hence the
   [split], each an [inl_merge]/[inr_merge] step. 

--------
[C ∏ C] 论证的自然性：每个分量一个方程，因此
 [split]，每个 [inl_merge]/[inr_merge] 步骤。 
*)
Next Obligation. split; unmerge. Qed.
(*
[merge_comp] backwards on the right-hand side, then [comp_assoc] forward so
   that [inl_merge] and [inr_merge] apply under the composites. 

--------
[merge_comp] 在右侧向后，然后 [comp_assoc] 在右侧向前，这样
 [inl_merge] 和 [inr_merge] 适用于复合材料。 
*)
Next Obligation.
  rewrite <- merge_comp, !comp_assoc, inl_merge, inr_merge; reflexivity.
Qed.
(* This square is [merge_comp] itself.  / 这个方块就是 [merge_comp] 本身。*)
Next Obligation. apply merge_comp. Qed.

(**
** Unit and counit

    Theory/Adjunction.v defines [unit := ⌊id⌋] and [counit := ⌈id⌉] as
    plain MORPHISMS; the class at Theory/Adjunction.v carries no
    natural-transformation field, so the identifications below are single [≈]
    equations quantified over the object.  The notations [⌊-⌋], [⌈-⌉], [η] and
    [ε] are local to the section in Theory/Adjunction.v, so [unit] and
    [counit] are spelled out here with their four implicit arguments. 

--------
** 单位及单位

 Theory/Adjunction.v 将 [unit := ⌊id⌋] 和 [counit := ⌈id⌉] 定义为
 普通态射； Theory/Adjunction.v 中的课程没有
 自然变换场，因此下面的标识是单个 [≈]
 对对象进行量化的方程。 符号 [⌊-⌋]、[⌈-⌉]、[η] 和
 [ε] 对于 Theory/Adjunction.v 中的部分是本地的，因此 [unit] 和
 [counit] 在这里详细说明了它们的四个隐式参数。 
*)

(** The unit at [p = (a, b)] is the pair of injections into [a + b].  / [p = (a, b)] 中的单元是 [a + b] 中的一对注入。*)
Definition coproduct_unit (C : Category) `{@Cocartesian C} (p : C ∏ C) :
  p ~{C ∏ C}~> Diagonal_Product C (fst p + snd p) := (inl, inr).

(** The counit at [x] is the folding map [x + x ~> x].  / [x] 的单位是折叠图 [x + x ~> x]。*)
Definition coproduct_counit (C : Category) `{@Cocartesian C} (x : C) :
  x + x ~{C}~> x := id ▽ id.

Lemma coproduct_unit_is_unit (C : Category) `{@Cocartesian C} (p : C ∏ C) :
  @unit _ _ +(C) (Diagonal_Product C) (Diagonal_Coproduct_Adjunction C) p
    ≈ coproduct_unit C p.
Proof. unfold coproduct_unit; simpl; split; cat. Qed.

(**
The componentwise reading of the same equation: equivalence in [C ∏ C] is
    the pair of the two component equivalences (Construction/Product.v),
    so this and [coproduct_unit_is_unit] are one statement. 

--------
同一方程的按分量读取：[C ∏ C] 中的等价是
 两个等价组件对 (Construction/Product.v)，
 所以这和 [coproduct_unit_is_unit] 是一个声明。 
*)
Lemma coproduct_unit_components (C : Category) `{@Cocartesian C}
      (p : C ∏ C) :
  fst (@unit _ _ +(C) (Diagonal_Product C)
         (Diagonal_Coproduct_Adjunction C) p) ≈ inl ∧
  snd (@unit _ _ +(C) (Diagonal_Product C)
         (Diagonal_Coproduct_Adjunction C) p) ≈ inr.
Proof. simpl; split; cat. Qed.

(**
A definitional check, not a use of any coproduct law: [counit] is [⌈id⌉],
    which unfolds to [fst (id, id) ▽ snd (id, id)], so the two sides are
    convertible and [reflexivity] closes the goal. 

--------
定义性检查，而不是使用任何副积定律：[counit] 是 [⌈id⌉]，
 展开为 [fst (id, id) ▽ snd (id, id)]，所以两侧是
 敞篷车和 [reflexivity] 关闭了目标。 
*)
Lemma coproduct_counit_is_counit (C : Category) `{@Cocartesian C} (x : C) :
  @counit _ _ +(C) (Diagonal_Product C) (Diagonal_Coproduct_Adjunction C) x
    ≈ coproduct_counit C x.
Proof. unfold coproduct_counit; reflexivity. Qed.

(**
** Sanity: the adjunction at two concrete cocartesian categories

    Issue #351's work item 4 asks for a sanity example so that the prose
    promise in Adjunction/GAFT/Examples.v points at real code; the
    GAFT-side reconstruction itself remains not undertaken, as that file
    says.  These two instantiations also make the non-vacuity of the
    hypothesis class an in-tree, build-checked fact rather than an ad-hoc
    observation: [Coq] (Instance/Coq.v) and [Sets]
    (Instance/Sets/Cocartesian.v) both carry [Cocartesian] instances,
    and the adjunction specializes to each.  Importing concrete instances
    into an Adjunction/ file follows the precedent of Adjunction/GAFT/Sets.v. 

--------
** 理智：两个具体的协笛卡尔类别的附加

 问题 #351 的工作项 4 要求提供一个合理的示例，以便散文
 Adjunction/GAFT/Examples.v 中的 Promise 指向真实代码； 的
 GAFT 端重建本身仍未进行，因为该文件
 说。 这两个实例化也使得
 假设类是树内的、经过构建检查的事实，而不是临时的
 观察：[Coq]（实例/Coq.v）和[Sets]
 (Instance/Sets/Cocartesian.v) 都携带 [Cocartesian] 实例，
 并且附加物专门针对每个。 导入具体实例
 进入 Adjunction/ 文件遵循 Adjunction/GAFT/Sets.v 的先例。 
*)

Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cocartesian.

Example coq_coproduct_diagonal : +(Coq) ⊣ Diagonal_Product Coq :=
  Diagonal_Coproduct_Adjunction Coq.

Example sets_coproduct_diagonal : +(Sets) ⊣ Diagonal_Product Sets :=
  Diagonal_Coproduct_Adjunction Sets.
