Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(*
   * * The discrete topology as a universal arrow

   nLab:      https://ncatlab.org/nlab/show/discrete+space
   nLab:      https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Discrete_space

   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   GTM 5, Springer 1998, §III.1, Exercise 3, printed p. 59 —
   item maclane:III.1:ex3.  The exercise asks for a universal
   arrow to each of four forgetful functors; this file is its
   THIRD row, the discrete topology on a set.  Riehl, “Category
   Theory in Context” 2nd ed., §4.1 Example 4.1.10 lists the same
   adjunction (riehl:4.1:example10).

   The content is Seven Sketches' Exercise 7.29 read as a universal
   property: a map out of a discrete space is continuous for ANY
   topology on the target, so the underlying-set map IS the continuous
   map, and the extension is unique because a continuous map is
   determined by its action on points.

   WHY THIS FILE DOES NOT PACKAGE AN [Adjunction], AND WHY THAT IS NOT A
   DEFECT OF THIS FILE.  Instance/Top/Forgetful.v records a
   pre-existing universe obstruction, in its own words: a functor out of
   [Top@{h o}] lands in [Sets@{h so}] while a functor INTO [Top@{h o}]
   must come from [Sets@{o so}], so “[a]n [Adjunction] record between the
   two would need both functors to share ONE Sets, at levels o and h
   simultaneously, with o < h: the packaged triple is unformable at every
   universe assignment.”  That file calls it “the library's familiar
   classifier phenomenon ... not a defect of the mathematics”, the same
   stratification Instance/Sets/Classifier.v lives with.  Accordingly it
   delivers the adjunction as the cross-universe transposition
   isomorphism [discrete_adj] with its four naturality lemmas,
   rather than as an [Adjunction].

   So the honest statement of #312's third row is NOT a packaged
   [UniversalArrow] — [Theory/Universal/Arrow.v]'s record would inherit
   exactly the same obstruction, since it mentions the forgetful functor
   applied to an object of the OTHER category.  What IS formable, and is
   delivered here, is the universal property itself, written out:

   - [disc_extend] : the extension of a setoid map to a continuous map
   out of the discrete space.
   - [discrete_universal] : the FULL universal property as a Type-valued
   [∃!] — every setoid map from A into the points of Y extends to one
   and only one continuous map out of [Discrete_Top A].  This is the
   elementary content that a [UniversalArrow] record would package,
   and nothing about it is conditional or cross-universe.
   - [disc_unit] : Mac Lane's unit X → U(X_disc), which the exercise
   names explicitly.

   THE UNIT IS THE IDENTITY, AND THAT IS STRICT.  [Top_Forget]'s object
   action is [Setoid_Lift (top_carrier X)] and [Top_Discrete]'s is
   [Discrete_Top A], whose carrier is A itself, so the composite is
   [Setoid_Lift A] ON THE NOSE — [disc_unit_target_strict] is [eq_refl],
   and it is NOT new: Instance/Top/Forgetful.v already ships
   [forget_discrete_on_objects], the same proposition with the same
   proof.  It is restated here only so the unit below can be read
   without leaving the file —
   and the unit is literally [id] of the lifted setoid.  That is the
   right mathematical statement rather than a degeneracy: the discrete
   topology adds nothing to the underlying set.  (That is the usual
   reason one expects this left adjoint to be fully faithful, but NEITHER
   [Full Top_Discrete] NOR [Faithful Top_Discrete] is proved here or
   anywhere in tree, and neither is claimed — see NOT DELIVERED.)  Note the
   unit
   must be stated on the LIFTED setoid: [A] itself lives in
   [Sets@{o so}] while [Top_Forget]'s values live in [Sets@{h so}], and
   those are different categories — the same stratification again.

   A MEASUREMENT WORTH RECORDING.  Writing [disc_extend] with the record
   literal [{| continuous_map := g; ... |}] is REJECTED even though the
   donor [discrete_adj] fills that very field the same way: the checker
   must solve [top_carrier ?X = A] for [?X], which is higher-order, and
   the ascription on the result type does not determine it in time.
   Applying the constructor explicitly, [@Build_ContinuousMorphism
   (Discrete_Top A) Y g _], fixes [?X] and elaborates.  The donor escapes
   because there the field sits inside a [Program Definition] whose
   expected type is already known.

   NOT DELIVERED: [Full Top_Discrete] and [Faithful Top_Discrete] are
   not proved, so the full faithfulness remarked on above is an
   expectation and not a result of this file.  No [Adjunction] and no
   [UniversalArrow] record either, for the reason above — and no claim that
   either is unformable for a reason
   OTHER than the donor's stratification, which is not re-derived here.
   Nothing is said about the indiscrete side beyond what Forgetful.v
   already proves, and no comparison with [Instance/Discrete.v]'s
   [DiscreteCat] (a different construction on a different subject) is
   made. 

   --------
   * * 离散拓扑作为通用箭头

   nLab:       https://ncatlab.org/nlab/show/discrete+space 
   nLab:       https://ncatlab.org/nlab/show/universal+morphism 
   维基百科:   https://en.wikipedia.org/wiki/Discrete_space 

   书籍: Mac Lane，《为工作数学家准备的范畴论》，第二版，
   GTM 5，Springer 1998，第III.1节，练习3，第59页印刷版 —
   条目 maclane:III.1:ex3。该练习要求为四个遗忘函子中的每一个寻找一个通用箭头；
   本文件是其第三行，即集合上的离散拓扑。Riehl，《上下文中的范畴论》第二版，第4.1节例4.1.10
   列出了相同的伴随关系 (riehl:4.1:example10)。内容是《七个素描》第 7.29 练习，可作为一个普遍性质来理解：从离散空间出的映射对于目标上的任何拓扑都是连续的，因此底层集合映射就是连续映射，并且扩展是唯一的，因为连续映射由其在点上的作用决定。为什么这个文件没有打包一个 [Adjunction]，以及为什么这不是这个文件的缺陷。Instance/Top/Forgetful.v 记录了一个预先存在的宇宙障碍，用它自己的话说：一个从 [Top@{h o}] 出发的函子落在 [Sets@{h so}] 中，而一个进入 [Top@{h o}] 的函子必须来源于 [Sets@{o so}]，因此“ [a] n [Adjunction] 之间的记录需要两个函子在同一时间共享一个 Sets，在 o 和 h 两个层次上，且 o < h：所打包的三元组在每个宇宙分配下都是无法形成的。” 那个文件称其为“库中熟悉的分类器现象……不是数学上的缺陷”，与 Instance/Sets/Classifier.v 中的分层现象相同。因此，它提供了伴随关系作为跨宇宙换位同构 [discrete_adj] 及其四个自然性引理，而不是作为一个 [Adjunction]。

   所以 #312 第三行的真实表述并不是一个打包的 [UniversalArrow]——[Theory/Universal/Arrow.v] 的记录会继承完全相同的障碍，因为它提到了应用于另一个范畴对象的遗忘函子。可以形成的，并且在这里提供的，是普遍性质本身，完整写出如下：-  [disc_extend]：从离散空间出发，将等价类映射扩展为连续映射。
   -  [discrete_universal]：作为类型值 [∃!] 的完整泛性质——从 A 到 Y 的每一个等价类映射都可以扩展为唯一的连续映射，出自 [Discrete_Top A]。这就是 [UniversalArrow] 记录所打包的基本内容，且其中没有任何条件或跨宇宙的内容。
   -  [disc_unit]：Mac Lane 的单元映射 X → U(X_disc)，练习题中明确给出了名称。单位是恒等映射，而且这是严格的。[Top_Forget] 的对象操作是 [Setoid_Lift (top_carrier X)]，而 [Top_Discrete] 的对象操作是 [Discrete_Top A]，其载体是 A 本身，所以复合正好是 [Setoid_Lift A]——[disc_unit_target_strict] 是 [eq_refl]，并且这并不是新的：Instance/Top/Forgetful.v 已经提供了 [forget_discrete_on_objects]，相同命题和相同证明。这里重新陈述只是为了让下面的单位可以在不离开文件的情况下阅读——而且单位字面上是提升后的等价集的 [id]。这才是正确的数学表述，而不是退化：离散拓扑对底层集合没有任何附加。（这通常是人们期望这个左伴随函子是完全忠实的原因，但这里或树中的任何地方都没有证明 [Full Top_Discrete] 或 [Faithful Top_Discrete]，也没有声称——见未交付。）注意，单位必须在提升后的集合等价类上陈述：[A] 本身属于 [Sets@{o so}]，而 [Top_Forget] 的值属于 [Sets@{h so}]，它们属于不同的范畴——再次是相同的分层问题。值得记录的测量。即使记录文字 [{| continuous_map := g; ... |}] 记录了 [disc_extend] 的写入，仍会被拒绝，即使捐赠者 [discrete_adj] 以完全相同的方式填充该字段：检查者必须为 [?X] 求解 [top_carrier ?X = A]，这是高阶的，并且结果类型的归属在时间上无法决定它。显式应用构造函数 [@Build_ContinuousMorphism (Discrete_Top A) Y g _] 可以修复 [?X] 并进行详细说明。捐赠者逃脱了，因为该字段位于 [Program Definition] 内，而其期望类型已知。未交付：[Full Top_Discrete] 和 [Faithful Top_Discrete] 尚未证明，因此上文提到的完全忠实性只是一个期望，而不是本文件的结果。由于上述原因，也没有 [Adjunction] 和 [UniversalArrow] 的记录——并且没有声称其中任何一个因捐赠者的分层以外的原因而不可形成，这在这里也没有重新推导。对于非离散方面，没有说超出 Forgetful.v 已经证明的内容，也没有与 [Instance/Discrete.v] 的 [DiscreteCat]（在不同对象上的不同构造）进行比较。
*)

(* * ** The extension of a setoid map to the discrete space / * ** 集值映射到离散空间的扩展 *)

(*
 A map out of a discrete space is continuous for every topology on the
 target ([out_of_discrete_continuous]), so the underlying setoid map is
 already the continuous map.  The constructor is applied explicitly; see
 the header for why the record literal is rejected here. 

 --------
 从离散空间出的映射对于目标上的每个拓扑（[out_of_discrete_continuous]）都是连续的，因此底层的集合等价映射已经是连续映射。构造函数是显式应用的；参见标题了解为什么这里拒绝记录字面量。
*)
Definition disc_extend (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y))
  : Discrete_Top A ~{Top}~> Y :=
  @Build_ContinuousMorphism (Discrete_Top A) Y g
    (out_of_discrete_continuous A Y g).

Example disc_extend_map (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) (a : carrier A) :
  disc_extend A Y g a = g a := eq_refl.

(* * ** The universal property (Mac Lane §III.1 Exercise 3, row three) / * ** 泛性质（Mac Lane 第 III.1 节练习 3，第三区） *)

Theorem discrete_universal (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) :
  ∃! f : Discrete_Top A ~{Top}~> Y, ∀ a, f a ≈ g a.
Proof.
  exists (disc_extend A Y g).
  - intro a; reflexivity.
  - intros f' Hf' a; simpl; symmetry; exact (Hf' a).
Qed.

(* * ** The unit X → U(X_disc), and that it is the identity / * ** 单位 X → U(X_disc)，并且它是恒等映射 *)

Example disc_unit_target_strict (A : SetoidObject) :
  fobj[Top_Forget] (fobj[Top_Discrete] A) = Setoid_Lift A := eq_refl.

Definition disc_unit (A : SetoidObject)
  : Setoid_Lift A ~{Sets}~> fobj[Top_Forget] (fobj[Top_Discrete] A) := id.

Example disc_unit_is_id (A : SetoidObject) (a : carrier A) :
  disc_unit A a = a := eq_refl.

(* * ** Agreement with the pre-existing transposition isomorphism / * ** 与预先存在的换位同构的一致性 *)

(* [discrete_adj]'s forward leg strips a continuous map to its underlying setoid map; on an extension it returns the map it started from. / [discrete_adj] 的前向函数将其连续映射剥离为其基础的集合等价映射；在扩展上，它返回最初的映射。 *)
Example disc_extend_is_adj_from (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) :
  to (discrete_adj A Y) (disc_extend A Y g) = g := eq_refl.

(*
   * ** Non-vacuity

   The witness must exercise a target whose topology is NOT discrete,
   or the universal property would say nothing: with both sides discrete
   every map is continuous for trivial reasons on both ends.  The
   two-point indiscrete space is the in-tree witness that separates. 

   --------
   * ** 非空性

   证据必须作用于一个拓扑不是离散的对象，否则泛性质将毫无意义：当两边都是离散的，每个映射在两端都是显然连续的。二点不可分空间是那个区分的树状证据。
*)

Example disc_universal_at_indiscrete
  (g : SetoidMorphism bool_setoid_object
         (top_carrier TwoPoint_Indiscrete)) :
  ∃! f : Discrete_Top bool_setoid_object ~{Top}~> TwoPoint_Indiscrete,
    ∀ a, f a ≈ g a :=
  discrete_universal bool_setoid_object TwoPoint_Indiscrete g.

(*
 And the extension really is the identity on points, so the universal
 property is not collapsing anything. 

 --------
 并且扩展在点上确实是恒等的，因此泛性质并没有压缩任何东西。
*)
Example disc_extend_indiscrete_computes
  (g : SetoidMorphism bool_setoid_object
         (top_carrier TwoPoint_Indiscrete)) (b : bool) :
  disc_extend bool_setoid_object TwoPoint_Indiscrete g b = g b := eq_refl.
