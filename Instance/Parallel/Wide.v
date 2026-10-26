Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The wide walking parallel pair / * 宽阔的步行平行对 *)

(*
 nLab:      https://ncatlab.org/nlab/show/parallel+morphisms
 nLab:      https://ncatlab.org/nlab/show/wide+pullback
 Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

 This is the shape category of an ARBITRARY family of parallel arrows:
 two objects [ParX], [ParY], their identities, and one non-identity arrow
 [ParX ~> ParY] for each element of an index type [I],

 --- f i --->
 ParX                 ParY      (one arrow for every i : I)
 --- f j --->

 with no arrow [ParY ~> ParX] and no non-identity endomorphism, so that
 composition is forced.  A functor [WideParallel I ⟶ C] is exactly an
 [I]-indexed family of parallel morphisms in C; its limit is their wide
 equalizer and its colimit their wide coequalizer.  Mac Lane introduces
 the notion in passing: having presented the coequalizer as a universal
 arrow over the walking parallel pair, he remarks that coequalizers of an
 arbitrary set of parallel maps a → b are defined in the same way
 (Categories for the Working Mathematician, 2nd ed., §III.3, pp. 64-65).
 Wide equalizers are the shape Freyd's initial-object argument wants:
 there one equalizes ALL endomorphisms of a weakly initial object at once
 (Mac Lane §V.6).  Theory/WeaklyInitial.v reaches AN initial object by a
 product-plus-binary-equalizer detour, and Theory/WeaklyInitial/Wide.v
 runs the argument directly over this shape's equalizers instead — as an
 ADDITIVE second theorem, leaving the first untouched.  No passage
 between the two conclusions is established, so they are not identified.

 [Instance/Parallel.v]'s [Parallel] is the case I = 2, and the two files
 sit side by side rather than one replacing the other; the comparison
 [WideParallel_bool_Parallel] below relates them.

 NAMING.  The issue that motivated this file calls the shape [Parallel I].
 That name is already taken, by the two-arrow shape this generalizes, and
 this file Requires it (the comparison needs both); [WideParallel] is used
 instead.  The objects are NOT redeclared: [ParObj], [ParX] and [ParY] are
 imported from [Instance/Parallel.v], so “the same two objects” is a
 definitional fact rather than a convention.

 ENCODING, and why the obvious generalization is not the one taken.
 [Instance/Parallel.v] declares [ParHom : bool → ParObj → ParObj → Set],
 which invites the reading that its two non-identity arrows are already
 parameterized by an index type, so that the wide shape would be that file
 with [bool] replaced by [I].  That reading does not survive contact with
 the constructors: THREE of the four ([ParIdX], [ParIdY], [ParOne]) sit at
 the tag [true] and only [ParTwo] at [false].  The [bool] is a
 DISCRIMINATOR on the hom-set ParX ~> ParY that doubles as a dummy tag on
 the identities, not a free index; substituting an arbitrary [I] leaves
 the three identity-side constructors without a distinguished element of
 [I] to sit at, and the definition does not typecheck.  So the wide shape
 is a different encoding rather than a substitution instance, which is
 also why the comparison below has to be proved rather than observed.

 The encoding chosen here computes the hom-family by matching on the two
 objects,

 hom ParX ParX = poly_unit,  hom ParX ParY = I,
 hom ParY ParY = poly_unit,  hom ParY ParX = WParVoid,

 so that an arrow of the shape from ParX to ParY IS an index, on the nose
 ([wide_hom_XY], by [eq_refl]), and the arrow action of a diagram is
 literally the family ([awide_fmap_arr], by [eq_refl]).  [WParVoid] is a
 universe-polymorphic empty type declared here so that all four branches
 of the hom family are at one universe by construction; the tree carries
 no polymorphic empty type to reuse (searched: [Lib/], [Instance/Zero.v],
 which uses [Empty_set]).  It is NOT forced: rebuilding the shape with
 the standard [Set]-pinned [Empty_set] in that branch yields the same
 signature and a character-for-character identical constraint block, [Set]
 sitting below every [Type@{i}], so nothing is dragged down.  An earlier
 draft of this header claimed otherwise and was wrong.

 UNIVERSES, measured rather than assumed (reproduce with
 [Set Printing Universes. About WideParallel. About AWide.]):

 WideParallel@{i p} : Type@{i} → Category@{Set i p}
 ( * i p |= i <= Logic_lemmas.equality.u0, i <= eq_ind_r.u0, i <= p * )

 The two stdlib bounds are the ordinary price of an [eq]-valued hom-setoid
 in this tree and are NOT introduced here: [Instance/Discrete.v]'s
 [DiscreteCat@{o h p}] — the tree's other [Type]-parameterized shape with
 [eq] homs, and the one [Theory/WeaklyInitial.v] already consumes —-
 carries SIX such constraints ([o <= eq.u0], [o <= Logic_lemmas.equality.u0],
 [h <= eq_ind.u0], [h <= Logic_lemmas.equality.u0], [h <= eq_ind_r.u0],
 [h <= p]) where this carries three.  The object universe is [Set] because
 [ParObj] is, exactly as in the donor.

 AWide@{i k o h p} : ... → WideParallel@{i k} I ⟶ C   with, among others,
 i <= h

 i.e. the index universe must sit at or below the AMBIENT hom universe.
 That is not a choice made here either: every [Functor] in this library
 pins the codomain hom level at or above the domain's, through the
 [respectful] instance inside [fmap_respects] (the same fact
 [Instance/Top/Forgetful.v] runs into from the other side).  For the
 Freyd application the index IS a hom-type, so the bound is met with
 nothing to spare and nothing to pay.  The bound is guarded, not merely
 recorded: Test/ProbeWideParallel.v rejects [AWide] at an index universe
 declared strictly above the target's hom universe and accepts it
 strictly below.

 The comparison section carries one further identification, and getting
 it down to that took explicit binders.  [Functor_StrictEq_Setoid]
 identifies the HOM and PROOF universes of the two categories it
 compares, so

 AWide_bool_APair : ∀ {C : Category@{u1 u3 u3}} ...

 — [h = p] at the target, at a FREE level.  Written without universe
 annotations on [Wide_of_Par] and [Par_of_Wide], minimization pins the
 shape's hom universe at [Set] (because [bool] is a [Set]) and
 [Functor_StrictEq_Setoid] then drags the TARGET's hom and proof
 universes down with it, giving the strictly weaker
 [C : Category@{u1 Set Set}].  Both comparison functors therefore carry
 explicit binders — [Wide_of_Par@{i p u v}], [Par_of_Wide@{i p u v}] —
 which is the same FAMILY of hazard that
 Construction/Free/Quiver/Examples.v records for
 [Build_Quiver_Standard_Eq], though neither the cause nor the repair is
 the same one: there a MONOMORPHIC donor
 ([Corelib.Classes.CRelationClasses.eq_equivalence@{u}]) pins the PROOF
 universe and the repair is to spend [Lib/Setoid.v]'s polymorphic
 [eq_equivalence@{t u}], whereas here minimization at unannotated
 definitions pins the HOM universe and the repair is explicit binders.
 [WideParallel_bool_Parallel] is over
 [Isomorphism@{u1 u0 u0} (WideParallel@{u0 u0} bool) Parallel@{Set u0}],
 with [u0] free for the same reason.

 DEGENERATE INDICES.  At a one-element index the shape is the walking
 arrow [Instance/Two.v]'s [_2] (same two objects, one non-identity arrow);
 at the empty index it is the DISCRETE category on two objects, so a limit
 over it is a binary PRODUCT rather than anything equalizer-shaped.
 NEITHER identification is proved, here or anywhere below — both are
 stated as orientation.  What IS proved, in [Structure/Equalizer/Wide.v]
 and its dual, is the consequence that matters: the elementary wide
 (co)equalizer record and the (co)limit over this shape come apart at an
 empty index, so the round trips between them take a member of the family
 as an explicit hypothesis.

 NOT DELIVERED.  No presheaf reading of this shape (the donor's
 [Presheaf_Graph] has no wide counterpart here).  No identification of
 [WideParallel poly_unit] with [_2], and none of [WideParallel] at an empty
 index with a discrete category, hence no identification of a limit over
 the empty-index shape with a binary product.  No functoriality of
 [WideParallel] in [I] (a map I → J does induce an identity-on-objects
 functor, but nothing below needs it and no such functor is built).  No
 claim that [WideParallel bool] and [Parallel] are Leibniz-equal as
 [Category] records, or that their hom-families are convertible: both are
 REFUTED,
 in Test/ProbeWideParallel.v. 

 --------
 nLab:       https://ncatlab.org/nlab/show/parallel+morphisms 
 nLab:       https://ncatlab.org/nlab/show/wide+pullback 
 维基百科:  https://en.wikipedia.org/wiki/Equaliser_(mathematics) 

 这是一个任意平行箭头族的形状范畴：
 两个对象  [ParX] ,  [ParY] ，它们的恒等箭头，以及每个索引类型 [I] 的元素对应的一个非恒等箭头
 [ParX ~> ParY] ，

 --- f i --->
 ParX                 ParY      （每个 i : I 对应一个箭头）
 --- f j --->没有箭头 [ParY ~> ParX] 并且没有非恒等自同态，因此必须进行组合。函子 [WideParallel I ⟶ C] 恰好是 C 中以 [I] 为索引的平行态射族；它的极限是它们的广义等化器，而它的余极限是它们的广义余等化器。Mac Lane 顺便引入了这个概念：在将余等化器作为遍历平行对的泛箭呈现之后，他指出任意集合的平行映射 a → b 的余等化器以相同的方式定义（《为工作数学家而设的范畴论》，第2版，第III.3节，第64-65页）。广义等化器是 Freyd 的初始对象论证所需要的形状：在那里，一次性等化一个弱初始对象的所有自同态（Mac Lane §V.6）。Theory/WeaklyInitial.v 通过一个乘积加二元等化器的旁路达到一个初始对象，而 Theory/WeaklyInitial/Wide.v 则直接在这个形状的等化器上运行论证 — 作为一个附加的第二个定理，保持第一个定理不变。两者之间没有建立任何结论的传递，所以它们没有被认同。

 [Instance/Parallel.v] 的 [Parallel] 是 I = 2 的情况，这两个文件并排放置，而不是一个替代另一个；下面的比较 [WideParallel_bool_Parallel]  关联了它们。命名。激发此文件的原因是将该形状称为 [Parallel I]。这个名称已经被使用，由这个通用化的双箭头形状占用，并且此文件需要它（比较需要两者）；因此改用 [WideParallel]。这些对象没有重新声明：[ParObj]、[ParX] 和 [ParY] 是从 [Instance/Parallel.v] 导入的，所以“相同的两个对象”是一个定义性的事实而不是约定。编码，以及为什么显而易见的泛化不是采用的方式。[Instance/Parallel.v] 声明了 [ParHom : bool → ParObj → ParObj → Set]，这引发了这样的理解：它的两个非恒等箭头已经由一个索引类型参数化，因此宽形状将是将文件中的 [bool] 替换为 [I] 。这种理解在与构造函数接触时无法成立：四个中的三个（[ParIdX]、[ParIdY]、[ParOne]）位于标签 [true]，只有 [ParTwo] 位于 [false]。[bool] 是同态集 ParX ~> ParY 上的一个判别器，同时充当恒等箭头的虚拟标签，而非自由索引；替换任意 [I] 会导致三个恒等箭头端的构造函数没有特定的元素 [I] 来驻留，因此定义无法通过类型检查。所以宽形状是一种不同的编码，而不是替换实例，这也是下面的比较必须被证明而不是仅仅观察的原因。

 这里选择的编码通过匹配两个对象来计算同态族：

 hom ParX ParX = poly_unit,  hom ParX ParY = I,
 hom ParY ParY = poly_unit,  hom ParY ParX = WParVoid,因此，从 ParX 到 ParY 形状的箭头就是一个索引，完全准确（[wide_hom_XY]，由 [eq_refl]），而图的箭头作用就是字面上的族（[awide_fmap_arr]，由 [eq_refl]）。[WParVoid] 是在此声明的一个宇宙多态空类型，以便同源族的四个分支通过构造在同一个宇宙中；该树没有携带任何可重用的多态空类型（搜索：[Lib/], [Instance/Zero.v]，其中使用了 [Empty_set]）。这不是强制性的：在该分支中使用标准的 [Set] 固定 [Empty_set] 重新构建形状会得到相同的签名和字符对字符完全相同的约束块，[Set] 位于每个 [Type@{i}] 之下，因此没有任何内容被拖下去。该头文件的早期草稿声称情况不同，这是错误的。宇宙，测量而非假设（使用 [Set Printing Universes. About WideParallel. About AWide.] 复现）：

 WideParallel@{i p} : Type@{i} → Category@{Set i p}
 ( * i p |= i <= Logic_lemmas.equality.u0, i <= eq_ind_r.u0, i <= p * )

 这两个 stdlib 上界是该树中 [eq] 值同构集体的普通价格，并且此处未引入：[Instance/Discrete.v] 的
 [DiscreteCat@{o h p}] — 树中另一个 [Type] 参数化的形状，具有 [eq] 同态，而 [Theory/WeaklyInitial.v] 已经使用 —
 包含六个此类约束（[o <= eq.u0], [o <= Logic_lemmas.equality.u0], [h <= eq_ind.u0], [h <= Logic_lemmas.equality.u0], [h <= eq_ind_r.u0], [h <= p]），而此处包含三个。对象宇宙是 [Set]，因为 [ParObj] 正如在源处一样。

 AWide@{i k o h p} : ... → WideParallel@{i k} I ⟶ C 并且，其中之一为 i <= h也就是说，索引宇宙必须位于或低于 AMBIENT hom 宇宙。这里也不是可以选择的：这个库中的每一个 [Functor] 都通过 [fmap_respects] 内的 [respectful] 实例将陪域 hom 级别固定在至少与定义域相同的水平（相同的事实 [Instance/Top/Forgetful.v] 从另一边也会遇到）。对于 Freyd 应用，索引本身就是一个 hom 类型，所以界限正好满足，没有剩余，也无需补偿。这一界限是被保护的，而不仅仅是记录：Test/ProbeWideParallel.v 会拒绝在索引宇宙中声明严格高于目标 hom 宇宙的 [AWide]，并严格接受那些低于目标的。

 比较部分还有一个进一步的标识，而要做到这一点，需要显式绑定器。[Functor_StrictEq_Setoid] 识别它所比较的两个范畴的 HOM 和 PROOF 宇宙，因此AWide_bool_APair : ∀ {C : 类别@{u1 u3 u3}} ...—— [h = p] 在目标上，在一个 FREE 级别。未在 [Wide_of_Par] 和 [Par_of_Wide] 上写入宇宙注释，最小化固定了 [Set] 的 shape 的 hom 宇宙（因为 [bool] 是一个 [Set]），然后 [Functor_StrictEq_Setoid] 将目标的 hom 和证明宇宙也拉低，从而得到严格更弱的 [C : Category@{u1 Set Set}]。因此，这两个比较函子都携带显式绑定器——[Wide_of_Par@{i p u v}]、[Par_of_Wide@{i p u v}]——这与 Construction/Free/Quiver/Examples.v 为 [Build_Quiver_Standard_Eq] 记录的风险类别相同，尽管原因和修复方法都不同：在那里，一个单态捐赠者（[Corelib.Classes.CRelationClasses.eq_equivalence@{u}]）固定了证明宇宙，修复方法是使用 [Lib/Setoid.v] 的多态 [eq_equivalence@{t u}]，而这里在未注释定义上的最小化固定了 HOM 宇宙，修复方法是显式绑定器。[WideParallel_bool_Parallel] 在 [Isomorphism@{u1 u0 u0} (WideParallel@{u0 u0} bool) Parallel@{Set u0}] 上结束，[u0] 因相同原因是自由的。

 退化指标。在单元素指标处，该形状是行走箭头 [Instance/Two.v] 的 [_2]（相同的两个对象，一个非恒等箭头）；在空指标处，它是两个对象上的离散范畴，因此其上的极限是二元积，而不是任何等化器形状。在此或下面任何地方都没有证明任何一种同一性——两者都作为取向陈述。真正被证明的，在 [Structure/Equalizer/Wide.v] 及其对偶中，是重要的结论：基本的广义（共）等化器记录与该形状上的（共）极限在空指标处是分离的，因此它们之间的来回转换将族的一个成员作为明确假设。未交付。没有这种形状的前层读数（捐赠者的 [Presheaf_Graph] 在这里没有宽对等物）。[WideParallel poly_unit] 与 [_2] 没有被识别，也没有在空索引处与离散范畴的 [WideParallel]，因此没有将空索引形状的极限与二元积识别。[WideParallel] 在 [I] 中没有函子性（映射 I → J 确实会引起一个对象上同一的函子，但以下没有需要它，也没有构建这样的函子）。没有声称 [WideParallel bool] 和 [Parallel] 作为 [Category] 记录是莱布尼茨相等的，或者它们的 hom-族可以互换：两者都在 Test/ProbeWideParallel.v 中被驳斥。
*)

(** ** The shape / ** 形状 *)

(* A universe-polymorphic empty type, for the hom-set ParY ~> ParX. / 一个宇宙多态空类型，用于同态集合 ParY ~> ParX。 *)
Inductive WParVoid@{i} : Type@{i} := .

(*
 The hom-family of the wide shape, computed from the two objects.  Note
 [WParHom I ParX ParY] reduces to [I] itself. 

 --------
 宽形状的同族，由两个对象计算得出。注意 [WParHom I ParX ParY] 简化为 [I] 本身。
*)
Definition WParHom@{i} (I : Type@{i}) (x y : ParObj) : Type@{i} :=
  match x, y with
  | ParX, ParX => poly_unit@{i}
  | ParY, ParY => poly_unit@{i}
  | ParX, ParY => I
  | ParY, ParX => WParVoid@{i}
  end.

(* There is no arrow ParY ~> ParX; the analogue of the donor's [ParHom_Y_X_absurd]. / 没有箭头 ParY ~> ParX；供体的 [ParHom_Y_X_absurd] 的类似物。 *)
Lemma WParHom_Y_X_absurd@{i} {I : Type@{i}} : WParHom@{i} I ParY ParX → False.
Proof. intro e; destruct e. Qed.

Definition wpar_id@{i} {I : Type@{i}} (x : ParObj) : WParHom@{i} I x x :=
  match x with ParX => ttt | ParY => ttt end.

(*
 Composition is forced: an identity on either side returns the other
 argument, and the four object triples that would need an arrow
 ParY ~> ParX are refuted by its empty hom-set. 

 --------
 组合是强制的：任一方的恒等元返回另一个参数，而四个需要箭头 ParY ~> ParX 的对象三元组被其空同态集所否定。
*)
Definition wpar_compose@{i} {I : Type@{i}} {x y z : ParObj} :
  WParHom@{i} I y z → WParHom@{i} I x y → WParHom@{i} I x z :=
  match x, y, z
    return WParHom@{i} I y z → WParHom@{i} I x y → WParHom@{i} I x z with
  | ParX, ParX, ParX => fun _ _ => ttt
  | ParX, ParX, ParY => fun f _ => f
  | ParX, ParY, ParX => fun f _ => match f with end
  | ParX, ParY, ParY => fun _ g => g
  | ParY, ParX, ParX => fun _ g => match g with end
  | ParY, ParX, ParY => fun _ g => match g with end
  | ParY, ParY, ParX => fun f _ => match f with end
  | ParY, ParY, ParY => fun _ _ => ttt
  end.

(*
 The wide walking parallel pair on the index type [I].  Hom-equivalence is
 strict equality of indices, so distinct indices are distinct arrows and
 the shape is not thin unless [I] is subsingleton. 

 --------
 在索引类型 [I] 上的宽行走平行对。同余等价是索引的严格相等，所以不同的索引对应不同的箭头，并且除非 [I] 是单元素，否则该形状不是稀疏的。
*)
Program Definition WideParallel@{i p} (I : Type@{i}) : Category@{Set i p} := {|
  obj     := ParObj;
  hom     := WParHom@{i} I;
  homset  := fun x y =>
    {| equiv := @eq (WParHom@{i} I x y)
     ; setoid_equiv := @eq_equivalence@{i p} (WParHom@{i} I x y) |};
  id      := @wpar_id@{i} I;
  compose := @wpar_compose@{i} I
|}.
Next Obligation. destruct x, y; simpl in *; try destruct f; reflexivity. Qed.
Next Obligation. destruct x, y; simpl in *; try destruct f; reflexivity. Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  try destruct f; try destruct g; try destruct h; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  try destruct f; try destruct g; try destruct h; reflexivity.
Qed.

(* An arrow ParX ~> ParY of the shape IS an index, and the two endomorphism hom-sets are singletons. / 形状为 IS 的箭头 ParX ~> ParY 是一个指标，并且两个自同态 Hom 集都是单例。 *)
Example wide_hom_XY (I : Type) : (ParX ~{WideParallel I}~> ParY) = I := eq_refl.
Example wide_hom_XX (I : Type) :
  (ParX ~{WideParallel I}~> ParX) = poly_unit := eq_refl.
Example wide_hom_YY (I : Type) :
  (ParY ~{WideParallel I}~> ParY) = poly_unit := eq_refl.

(* * ** The diagram of a family of parallel arrows / * ** 一组平行箭头的示意图 *)

(* Object action: ParX ↦ x, ParY ↦ y. / 对象动作：ParX ↦ x，ParY ↦ y。 *)
Definition wdiag@{o h p} {C : Category@{o h p}} (x y : C) (p : ParObj) : C :=
  match p with ParX => x | ParY => y end.

(* Arrow action: the index i is sent to the member f i of the family. / 箭头操作：索引 i 被发送到族的成员 f i。 *)
Definition awide_fmap@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) {a b : ParObj} :
  WParHom@{i} I a b → wdiag@{o h p} x y a ~{C}~> wdiag@{o h p} x y b :=
  match a, b return WParHom@{i} I a b
                    → wdiag@{o h p} x y a ~{C}~> wdiag@{o h p} x y b with
  | ParX, ParX => fun _ => id[x]
  | ParY, ParY => fun _ => id[y]
  | ParX, ParY => fun i => fs i
  | ParY, ParX => fun e => match e with end
  end.

Lemma awide_fmap_id@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) (a : ParObj) :
  awide_fmap@{i o h p} fs (@wpar_id@{i} I a) ≈ id{C}.
Proof. destruct a; reflexivity. Qed.

Lemma awide_fmap_comp@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) (a b c : ParObj) :
  ∀ (f : WParHom@{i} I b c) (g : WParHom@{i} I a b),
    awide_fmap@{i o h p} fs (@wpar_compose@{i} I a b c f g)
      ≈ awide_fmap@{i o h p} fs f ∘ awide_fmap@{i o h p} fs g.
Proof.
  destruct a, b, c; intros f g; simpl in *;
  try destruct f; try destruct g; cat.
Qed.

(* The diagram of the family [fs], the wide analogue of [APair]. / 家族 [fs] 的示意图，[APair] 的宽广对应物。 *)
Program Definition AWide@{i k o h p}
  {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) : WideParallel@{i k} I ⟶ C := {|
  fobj := wdiag@{o h p} x y;
  fmap := fun a b m => awide_fmap@{i o h p} fs m;
  fmap_id := fun a => awide_fmap_id@{i o h p} fs a;
  fmap_comp := fun a b c f g => awide_fmap_comp@{i o h p} fs a b c f g
|}.

(* The arrow action is the family itself, definitionally. / 箭头动作本身就是家庭，从定义上来说。 *)
Example awide_fmap_arr {I : Type} {C : Category} {x y : C}
  (fs : I → x ~> y) (i : I) :
  fmap[AWide fs] (i : ParX ~{WideParallel I}~> ParY) = fs i := eq_refl.

Example awide_obj_X {I : Type} {C : Category} {x y : C} (fs : I → x ~> y) :
  fobj[AWide fs] ParX = x := eq_refl.
Example awide_obj_Y {I : Type} {C : Category} {x y : C} (fs : I → x ~> y) :
  fobj[AWide fs] ParY = y := eq_refl.

(* * ** Comparison with the two-arrow shape / * ** 与双箭头形状的比较 *)

(*
 The two comparison functors are the identity on objects; all the content
 is in the hom-sets, where a [Parallel] arrow ParX ~> ParY is a dependent
 pair whose bool tag decides between the two generators, and a
 [WideParallel bool] arrow ParX ~> ParY is that bool itself. 

 --------
 这两个比较函子在对象上是恒等的；所有内容都在 Hom 集中，其中一个 [Parallel] 箭头 ParX ~> ParY 是一个依赖对，其布尔标签决定使用两个生成器中的哪一个，而一个 [WideParallel bool] 箭头 ParX ~> ParY 是该布尔值本身。
*)

Definition wide_of_par_map@{i u v} {a b : ParObj} :
  (a ~{Parallel@{u v}}~> b) → WParHom@{i} bool a b :=
  match a, b return (a ~{Parallel@{u v}}~> b) → WParHom@{i} bool a b with
  | ParX, ParX => fun _ => ttt
  | ParY, ParY => fun _ => ttt
  | ParX, ParY => fun h => ``h
  | ParY, ParX => fun h => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
  end.

Definition par_of_wide_map@{i u v} {a b : ParObj} :
  WParHom@{i} bool a b → (a ~{Parallel@{u v}}~> b) :=
  match a, b return WParHom@{i} bool a b → (a ~{Parallel@{u v}}~> b) with
  | ParX, ParX => fun _ => (true; ParIdX)
  | ParY, ParY => fun _ => (true; ParIdY)
  | ParX, ParY => fun c => if c then (true; ParOne) else (false; ParTwo)
  | ParY, ParX => fun e => match e with end
  end.

Program Definition Wide_of_Par@{i p u v} :
  Parallel@{u v} ⟶ WideParallel@{i p} bool := {|
  fobj := fun p => p;
  fmap := fun a b h => wide_of_par_map@{i u v} h
|}.
Next Obligation.
  proper.
  destruct x, y; simpl in *; try assumption; try reflexivity;
  destruct (ParHom_Y_X_absurd _ e).
Qed.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  destruct x, y, z, f, g;
  pose proof (ParHom_inv _ _ _ X0) as HX0;
  pose proof (ParHom_inv _ _ _ X) as HX;
  simpl in HX0, HX; try contradiction;
  subst; reflexivity.
Qed.

Program Definition Par_of_Wide@{i p u v} :
  WideParallel@{i p} bool ⟶ Parallel@{u v} := {|
  fobj := fun p => p;
  fmap := fun a b m => par_of_wide_map@{i u v} m
|}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  destruct x, y, z; simpl in *;
  try destruct f; try destruct g; reflexivity.
Qed.

(* In [Parallel] the tag of an endomorphism is forced to [true]: the two [false]-tagged cases of [ParHom_inv_t] at equal endpoints are [False]. / 在 [Parallel] 中，一个自同态的标记被强制为 [true]：在相等端点处的两个 [false] 标记的 [ParHom_inv_t] 情况是 [False]。 *)
Lemma par_endo_tag (a : ParObj) (f : a ~{Parallel}~> a) : ``f = true.
Proof.
  destruct f as [bf hf]; destruct a, bf; simpl; try reflexivity;
  destruct (ParHom_inv _ _ _ hf).
Qed.

(*
 Both composites are the identity, and both round trips hold at STRICT
 functor equality: the object components are [eq_refl], so the transports
 of [Functor_StrictEq_Setoid] vanish and only the hom-level agreement is
 left to prove. 

 --------
 两个复合都是恒等，并且在严格函子等价下，两次往返都成立：对象部分是 [eq_refl]，因此 [Functor_StrictEq_Setoid] 的传输消失，只剩下要证明同态层面的对应。
*)
Lemma Par_of_Wide_Wide_of_Par :
  @equiv _ (@Functor_StrictEq_Setoid Parallel Parallel)
    (Par_of_Wide ◯ Wide_of_Par) (Id[Parallel]).
Proof.
  exists (fun _ => eq_refl).
  intros a b f; simpl; unfold Logic.transport_r, Logic.transport; simpl.
  destruct a, b; simpl in *.
  - symmetry; exact (par_endo_tag ParX f).
  - destruct f as [bf hf]; destruct bf; reflexivity.
  - destruct f as [bf hf]; destruct (ParHom_Y_X_absurd _ hf).
  - symmetry; exact (par_endo_tag ParY f).
Qed.

Lemma Wide_of_Par_Par_of_Wide :
  @equiv _ (@Functor_StrictEq_Setoid (WideParallel bool) (WideParallel bool))
    (Wide_of_Par ◯ Par_of_Wide) (Id[WideParallel bool]).
Proof.
  exists (fun _ => eq_refl).
  intros a b m; simpl.
  destruct a, b; simpl in *;
  try destruct m; reflexivity.
Qed.

(*
 The wide shape at a two-element index IS the walking parallel pair, as a
 genuine isomorphism of categories: [≅[StrictCat]] compares functors by
 [Functor_StrictEq_Setoid] (object equality on the nose), unlike [≅[Cat]],
 which in this library is equivalence of categories. 

 --------
 在二元索引下的宽形状就是行走的平行对，作为范畴的真正同构：[≅[StrictCat]] 通过 [Functor_StrictEq_Setoid]（对象上的精确相等）比较函子，这与 [≅[Cat]] 不同，后者在这个库中是范畴的等价。
*)
Program Definition WideParallel_bool_Parallel :
  @Isomorphism StrictCat (WideParallel bool) Parallel := {|
  to   := Par_of_Wide;
  from := Wide_of_Par
|}.
Next Obligation. exact Par_of_Wide_Wide_of_Par. Qed.
Next Obligation. exact Wide_of_Par_Par_of_Wide. Qed.

(*
 The weaker reading, derived: an isomorphism in [Cat] is an EQUIVALENCE of
 categories, so this says strictly less than the statement above. 

 --------
 较弱的表述，导出的：在 [Cat] 中的同构是范畴的等价，因此这严格上比上面的陈述要少。
*)
Program Definition WideParallel_bool_Parallel_Cat :
  @Isomorphism Cat (WideParallel bool) Parallel := {|
  to   := Par_of_Wide;
  from := Wide_of_Par
|}.
Next Obligation.
  exact (strict_equiv_implies_fun_equiv _ _ Par_of_Wide_Wide_of_Par).
Qed.
Next Obligation.
  exact (strict_equiv_implies_fun_equiv _ _ Wide_of_Par_Par_of_Wide).
Qed.

(*
 The shape comparison alone says nothing about DIAGRAMS.  This does: the
 binary diagram [APair f g] pulled back along the comparison is the wide
 diagram at the two-element family, again at strict functor equality with
 [eq_refl] object components. 

 --------
 仅仅形状比较并不能说明图表。这一点说明了：沿比较拉回的二进制图 [APair f g] 是两个元素族的宽图表，再次在严格函子等式下与 [eq_refl] 对象分量相等。
*)
Lemma AWide_bool_APair {C : Category} {x y : C} (f g : x ~> y) :
  @equiv _ (@Functor_StrictEq_Setoid (WideParallel bool) C)
    (AWide (fun b : bool => if b then f else g))
    (APair f g ◯ Par_of_Wide).
Proof.
  unshelve eexists.
  - intro p; destruct p; reflexivity.
  - intros a b m; simpl; unfold Logic.transport_r, Logic.transport; simpl.
    destruct a, b; simpl in *;
    try destruct m; reflexivity.
Qed.
