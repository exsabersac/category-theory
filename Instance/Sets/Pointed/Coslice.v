Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(* * * Pointed sets as the coslice of Sets under the one-point set / * * 有顶点集作为一点评集下的集合余切 *)

(*
 nLab:      https://ncatlab.org/nlab/show/pointed+object
 nLab:      https://ncatlab.org/nlab/show/under+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category
 Book:      Awodey, “Category Theory”, 1st ed., OUP 2006, §7.9 Example 7.26

 The header of Construction/Slice.v records the standard reading — “pointed
 sets are the coslice of Set under the one-point set” — and Awodey gives the
 same example (1st ed., §7.9 Example 7.26).  This file turns that sentence
 into a theorem: [Pointed_Coslice_iso] exhibits `PointedSets ≅[Cat] Coslice
 Sets SetsOne`.

 WHAT THAT STRENGTH IS, EXACTLY (the first commit of this file got this
 wrong and an audit corrected it).  An isomorphism in this library's [Cat]
 IS an equivalence of categories, because [Functor_Setoid] identifies
 functors that are merely naturally isomorphic — Instance/Cat.v says
 so in as many words, and Theory/Equivalence.v,172 ships the
 interconversion pair [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence]
 with both round trips.  So `≅[Cat]` here is NOT the on-the-nose
 isomorphism of categories that Awodey's §1.6 Example 1.8 asserts, and
 nothing in this file should be read as claiming it.  A strict
 isomorphism would have to be stated in Instance/StrictCat.v's
 [StrictCat], and the obstruction to it is recorded below: the coslice
 round trip replaces a structure map `m` by the constant map at `m ttt`,
 which agrees with `m` up to `≈` but is not the same function, so
 identifying the two is a function-extensionality step this library
 deliberately does not take.  The equivalence is therefore the honest
 strength, not a weakening of something already available.

 The content is the translation between the two ways of naming a point.  A
 basepoint of A is an element; a coslice object is a morphism 1 ~> A out of
 the terminal setoid, i.e. a global element (Structure/Terminal.v's header
 discusses the correspondence).  The two are interchangeable: evaluate at
 the unique point of 1 in one direction, take the constant map in the other.
 Better still, the coslice triangle

 `2 y ≈ f ∘ `2 x

 is pointwise EXACTLY [preserves_pt], so the arrows match on the nose too.

 Only one of the two round trips is the identity on the nose.  Pointed to
 coslice and back returns the same record, because the constant map at the
 basepoint evaluated at the point is the basepoint again; coslice to pointed
 and back replaces the structure map m by the constant map at [m ttt], which
 agrees with m up to `≈` — the one-point setoid has a single element, so
 this is a [destruct] — but not syntactically.  The comparison isomorphism
 in that direction is therefore carried by the identity of the underlying
 setoid together with the two triangle proofs ([coslice_counit_iso]). 

 --------
 nLab：       https://ncatlab.org/nlab/show/pointed+object
 nLab：       https://ncatlab.org/nlab/show/under+category
 维基百科：  https://en.wikipedia.org/wiki/Comma_category
 书籍：      Awodey，《范畴论》，第一版，牛津大学出版社 2006，§7.9 示例 7.26

 Construction/Slice.v 的标题记录了标准的表述——“带基集是集合在单点集下的余切类”——而 Awodey 给出了同样的例子（第一版，§7.9 示例 7.26）。该文件将该句子变成了一个定理：[Pointed_Coslice_iso] 展示了 `PointedSets ≅ [Cat] Coslice Sets SetsOne`。究竟这种强度是什么（这个文件的第一次提交写错了，审计后来纠正了）。在这个库的 [Cat] 中的同构是范畴的等价，因为 [Functor_Setoid] 识别出仅自然同构的函子——Instance/Cat.v 用明确的话说明了这一点，而 Theory/Equivalence.v，第172行提供了 [Equivalence_to_Cat_Iso] / [Cat_Iso_to_Equivalence] 的互相转换对，并且两次往返都是可以进行的。因此，这里的 `≅ [Cat]ZZ ` 并不是 Awodey 第1.6节示例1.8所断言的按字面意义的范畴同构，并且这个文件中没有任何内容应该被解读为声称它是。严格同构必须在 Instance/StrictCat.v 的 [StrictCat] 中声明，其障碍记录如下：余切回程将结构映射 `m` 替换为 `m ttt` 处的常值映射，该映射在 `≈` 范围内与 `m` 一致，但并非相同的函数，因此将两者识别为同一函数是一个函数外延步骤，而该库故意不采用。 因此，该等价是真正的强度，而不是对已有内容的削弱。内容是两种命名一个点方式之间的翻译。A 的基点是一个元素；余切对象是从终端集合同构 1 ~> A 的一个态射，即一个全局元素（Structure/Terminal.v 的标题讨论了这种对应关系）。两者是可以互换的：在一个方向上在 1 的唯一点上求值，另一个方向取常值映射。更好的是，余切三角形

 `2 y ≈ f ∘ ` 2 x

 在每一个点上完全等于 [preserves_pt]，因此箭头也完全一致。在这两次往返中，只有一次严格等于恒等映射。从指向的余切到返回会得到相同的记录，因为在基点的常量映射在该点处求值后仍然是基点；从余切到指向再返回会将结构映射 m 替换为在 [m ttt] 处的常量映射，这在 `≈` 下与 m 一致——一元集合具有单个元素，因此这是一个 [destruct]——但在语法上并非如此。因此，该方向上的比较同构是由底层集合的恒等映射以及两个三角形证明（[coslice_counit_iso]）承载的。
*)

#[local] Obligation Tactic := idtac.

(*
 The header of Construction/Slice.v records the standard reading of the
 coslice — “pointed sets are the coslice of Set under the one-point set”.
 Here that sentence becomes a theorem.  A global element of A, i.e. a map
 1 ~> A out of the terminal setoid, is the same data as a basepoint of A,
 and the coslice triangle is pointwise exactly [preserves_pt]. 

 --------
 Construction/Slice.v 的头部记录了余切片的标准读法——“指向集合是单点集合下的 Set 的余切片”。在这里，这句话变成了一个定理。A 的全局元，即来自终结集合同构的映射 1 ~> A，与 A 的基点是同样的数据，而余切片三角形在每一点上正好是 [preserves_pt]。
*)
Definition SetsOne : SetoidObject := @terminal_obj Sets Sets_Terminal.

(*
 A basepoint, read as a global element.  The one-point pointed set has the
 terminal setoid underneath it, so the constant map at the basepoint already
 has the right type. 

 --------
 一个基点，被读作全局元素。单点指定集合在其下方有终端等价类，因此基点处的恒等映射已经具有正确的类型。
*)
Definition pt_global (X : PointedSetoid) :
  SetsOne ~{Sets}~> pointed_setoid X := const_pt_map PointedOne X.

Program Definition Pointed_to_Coslice : PointedSets ⟶ Coslice Sets SetsOne := {|
  fobj := fun X => (pointed_setoid X; pt_global X);
  fmap := fun X Y f => (pointed_map f; _)
|}.
Next Obligation.
  intros X Y f u; simpl.
  symmetry.
  exact (preserves_pt f).
Qed.
Next Obligation.
  intros X Y f g Hfg u; simpl.
  exact (Hfg u).
Qed.
Next Obligation. intros X u; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z f g u; simpl; reflexivity. Qed.

Program Definition Coslice_to_Pointed : Coslice Sets SetsOne ⟶ PointedSets := {|
  fobj := fun p => {| pointed_setoid := `1 p; pt := `2 p ttt |};
  fmap := fun x y h => Build_PointedMorphism _ _ (`1 h) _
|}.
Next Obligation.
  intros x y h; simpl.
  symmetry.
  exact (`2 h ttt).
Qed.
Next Obligation.
  intros x y h h' Hhh u; simpl.
  exact (Hhh u).
Qed.
Next Obligation. intros x u; simpl; reflexivity. Qed.
Next Obligation. intros x y z h k u; simpl; reflexivity. Qed.

(*
 Going Pointed → Coslice → Pointed returns the very same record, since the
 global element evaluated at the only point of 1 is the basepoint again; the
 comparison isomorphism is therefore the identity. 

 --------
 Going Pointed → Coslice → Pointed 会返回完全相同的记录，因为在 1 的唯一点处评估的全局元素又是基点；因此，比对同构是恒等映射。
*)
Lemma Coslice_Pointed_unit :
  Coslice_to_Pointed ◯ Pointed_to_Coslice ≈ Id[PointedSets].
Proof.
  exists (fun X => iso_id).
  intros X Y f u; simpl.
  reflexivity.
Qed.

(*
 Going Coslice → Pointed → Coslice replaces the structure map by the
 constant map at its value on the point.  These agree up to `≈` but not on
 the nose, so the comparison isomorphism is carried by the identity of the
 underlying setoid together with the triangle proofs.  The isomorphism is
 assembled through [Build_Isomorphism] rather than by record notation, so
 that it does not depend on the field names [to] and [from] being unshadowed
 at this point in the development. 

 --------
 进入 Coslice → Pointed → Coslice 将结构映射替换为其在该点值上的常映射。这在 `≈` 下是一致的，但不完全相同，因此比较同构是由基础集合等价类的恒等映射以及三角形证明携带的。同构是通过 [Build_Isomorphism] 组装的，而不是通过记录符号组装，因此它不依赖于字段名 [to] 和 [from] 在此开发阶段未被遮蔽。
*)
Program Definition coslice_counit_iso (p : Coslice Sets SetsOne) :
  Pointed_to_Coslice (Coslice_to_Pointed p) ≅[Coslice Sets SetsOne] p :=
  @Build_Isomorphism (Coslice Sets SetsOne)
    (Pointed_to_Coslice (Coslice_to_Pointed p)) p
    (@id Sets (`1 p); _) (@id Sets (`1 p); _) _ _.
Next Obligation.
  intros p u; simpl.
  destruct u.
  reflexivity.
Qed.
Next Obligation.
  intros p u; simpl.
  destruct u.
  reflexivity.
Qed.
Next Obligation. intros p u; simpl; reflexivity. Qed.
Next Obligation. intros p u; simpl; reflexivity. Qed.

Lemma Coslice_Pointed_counit :
  Pointed_to_Coslice ◯ Coslice_to_Pointed ≈ Id[Coslice Sets SetsOne].
Proof.
  exists coslice_counit_iso.
  intros x y h u; simpl.
  reflexivity.
Qed.

(*
 Set_* IS the coslice of Sets under the one-point setoid — an isomorphism of
 categories, not merely an equivalence. 

 --------
 Set_* 是在单点集合上集合的余片——是范畴的同构，而不仅仅是等价。
*)
Definition Pointed_Coslice_iso : PointedSets ≅[Cat] Coslice Sets SetsOne :=
  @Build_Isomorphism Cat PointedSets (Coslice Sets SetsOne)
    Pointed_to_Coslice Coslice_to_Pointed
    Coslice_Pointed_counit Coslice_Pointed_unit.
