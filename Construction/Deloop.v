Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Delooping: monoids as one-object categories / * * 去环化：作为单对象范畴的幺半群 *)

(*
 nLab:      https://ncatlab.org/nlab/show/delooping
 nLab:      https://ncatlab.org/nlab/show/monoid
 nLab:      https://ncatlab.org/nlab/show/groupoid
 Wikipedia: https://en.wikipedia.org/wiki/Monoid
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §I.2, printed p. 11 (constructions 3 and 4)
 Book:      Awodey, "Category Theory", 2nd ed., §1.4, pp. 12-13
 Book:      Riehl, "Category Theory in Context", Example 1.1.4(ii), pp. 5-6
 Book:      Fong, Spivak, "Seven Sketches in Compositionality", CUP 2019,
 §3.2.1 Example 3.13, printed p. 83

 A monoid is exactly a category with one object.  Mac Lane's third
 construction in §I.2 takes a monoid M to the category [Deloop M] whose sole
 object is a formal point, whose arrows are the elements of M, whose
 composition is the multiplication of M, and whose identity arrow is the unit
 of M; the category laws then read off verbatim as the monoid laws.  His
 fourth construction specializes to groups: when every element has a
 two-sided inverse, every arrow of the one-object category is invertible, so
 the category is a one-object groupoid.  Conversely — the direction Awodey
 and Fong-Spivak both make explicit — for any category C and any object a,
 the endomorphism hom `a ~> a` is a monoid under composition with unit [id].
 This file provides all three, plus the statement that the two constructions
 are mutually inverse in the direction where that can be said on the nose
 ([hom_monoid_Deloop], which holds by [eq_refl]).

 Contents:

 MonObject                 a monoid (carrier setoid, unit, operation)
 Deloop M                  the one-object category B M
 hom_monoid C a            the endomorphism monoid of a in C
 hom_monoid_Deloop         hom_monoid (Deloop M) ttt = M, by eq_refl
 GrpObject                 a monoid with a two-sided inverse operation
 Deloop_group_invertible   every arrow of B G is an isomorphism
 Nat_Plus, Bool_Xor_Grp    inhabitation witnesses for the two records

 The functor-level half of the dictionary — that functors between deloopings
 are exactly monoid homomorphisms, so that a functor `B G ⟶ Vect` is a linear
 representation of G — is deliberately not built here; it belongs with the
 Mac Lane §I.3 material. 

 --------
 nLab:       https://ncatlab.org/nlab/show/delooping 
 nLab:       https://ncatlab.org/nlab/show/monoid 
 nLab:       https://ncatlab.org/nlab/show/groupoid 
 Wikipedia:  https://en.wikipedia.org/wiki/Monoid 
 书籍:      Mac Lane, 《为在职数学家准备的范畴论》，第2版，
 GTM 5, §I.2, 印刷页 11（构造 3 和 4）
 书籍:      Awodey, 《范畴论》，第2版，§1.4, 第12-13页
 书籍:      Riehl, 《情境中的范畴论》，示例 1.1.4(ii), 第5-6页
 书籍:      Fong, Spivak, 《组合性七讲》，CUP 2019，
 §3.2.1 示例 3.13, 印刷页 83一个幺半群恰好是一个只有一个对象的范畴。Mac Lane 在 §I.2 中的第三种构造将一个幺半群 M 转化为范畴 [Deloop M]，其唯一的对象是一个形式点，其箭头是 M 的元素，其复合是 M 的乘法，而其单位箭头是 M 的单位；然后范畴律会逐字体现为幺半群律。他的第四种构造专门针对群：当每个元素都有双边逆时，单对象范畴的每个箭头都是可逆的，因此该范畴是一个单对象群族。反之——Awodey 和 Fong-Spivak 都明确指出了这个方向——对于任意范畴 C 和任何对象 a，端同态 hom `a ~> a` 在以 [id] 作为单位的复合下构成一个幺半群。该文件提供了全部三者，以及指出在可以直接说明的方向上，两种构造是相互逆的陈述（[hom_monoid_Deloop]，由[eq_refl]成立）。

 内容：

 MonObject                 一个幺半群（承载集合等价类、单位元、运算）
 Deloop M                  单对象范畴 B M
 hom_monoid C a            对象 a 在范畴 C 中的自同态幺半群
 hom_monoid_Deloop         hom_monoid (Deloop M) ttt = M，通过 eq_refl
 GrpObject                 具有双侧逆运算的幺群
 Deloop_group_invertible   B G 的每一条箭头都是同构
 Nat_Plus, Bool_Xor_Grp    两个记录的具体实例字典的函子层面——也就是不同循环之间的函子正好是幺半群同态，因此一个函子 `B G ⟶ Vect` 是 G 的线性表示——在这里刻意没有建立；它属于 Mac Lane §I.3 的内容。
*)

(*
 Why "delooping", and what the one-object reading buys

 The name is topological.  Per the nLab (delooping), a delooping of an
 object X is an object B X whose loop space object is X again, so that
 passing from a group G to the one-object groupoid B G (equivalently, to
 its classifying space BG) inverts the formation of loops; the notation
 B is Riehl's and is standard.  The categorical content is Mac Lane's
 observation that the axioms match: associativity of composition is
 associativity of the operation, the two unit laws of a category are the
 two unit laws of a monoid, and the single object carries no information
 whatever.  Fong and Spivak put the equivalence in exactly this form —
 a category with one object *is* a monoid, taking the hom-set at that
 object as the carrier — and it is the reason both directions belong in
 one file rather than sitting apart as unrelated constructions.

 What the reading buys is that everything defined for categories
 immediately specializes to monoids.  The opposite category of a
 delooping is the delooping of the opposite monoid (Riehl, Example
 1.2.2(iii), the device by which right actions are presented as left
 actions); the idempotent-splitting completion of a delooped monoid is
 the category whose objects are the idempotents of the monoid
 (Construction/Karoubi.v); a functor out of a delooping is an action,
 which for groups in Vect is a linear representation.  In the other
 direction, the endomorphism monoid [hom_monoid] is how a category
 sees a single object in isolation, and it is the local invariant that
 Theory/Isomorphism.v's [IsIsomorphism] tests for invertibility of.

 Relationship to what is already in the tree.  [Instance/CMon.v]'s
 [CMonObject] is the *commutative* version of [MonObject] below, in the
 same setoid shape and with the same [Proper] field, and is used for the
 preadditive/biproduct development; it derives its right unit law from
 commutativity, whereas a bare monoid must carry both unit laws as data.
 [Theory/Algebra/Monoid.v] defines a monoid *object* internal to a
 monoidal category, which is the correct notion in general but drags a
 monoidal structure into a construction that needs nothing of the kind;
 the same holds for [Structure/Group.v]'s [GroupObject], an internal
 group object in a cartesian monoidal category, which is why [GrpObject]
 below is a small extension record instead.  [Theory/Bicategory/OneObject.v]
 is the same delooping one level up: it presents a monoidal category as a
 one-object *bicategory*, with the elements-as-arrows dictionary shifted
 from (object, arrow) to (arrow, 2-cell).  Finally
 [Construction/Funny/Comparison.v]'s [ListMon] is a hand-written one-object
 category on the free monoid over [bool], made for a single counterexample.
 It is NOT [Deloop] of that monoid: its composition is `v ++ u`, the
 REVERSED product (that file's own header says so), so it is [Deloop] of the
 OPPOSITE free monoid -- equivalently `(Deloop FreeBool)^op`, by [Deloop_op]
 in Construction/Deloop/Opposite.v.  The two are isomorphic via [rev], so no
 mathematics turns on it, but the distinction is precisely the
 composition-order point below and is worth stating exactly.

 Two further internal-monoid donors, neither usable here: Structure/Monoid.v
 defines `Monoid := @MonoidObject C CC_Monoidal` (still an ambient category),
 and Theory/Coq/Monoid.v is an operations-only class carrying no laws -- it
 nevertheless already observes in prose that a monoid is the hom-set of a
 one-object category, which is the statement this file proves. 

 --------
 为什么要“去环”，以及单对象解读能带来什么这个名字具有拓扑性质。根据 nLab（去环化）的定义，给定一个对象 X 的去环化是一个对象 B X，其循环空间对象再次是 X，因此从一个群 G 传到单对象群范畴 B G（等价地，其分类空间 BG）实际上是逆转了循环的形成；符号 B 来自 Riehl，并且是标准的。范畴的内容是 Mac Lane 的观察，即公理匹配：复合的结合律就是运算的结合律，范畴的两个单位律就是一个幺半群的两个单位律，而单对象本身不承载任何信息。Fong 和 Spivak 将等价关系正是以这种形式提出——一个只有一个对象的范畴 *就是* 一个幺半群，取该对象的同态集作为载体——这也是为什么两个方向都属于同一个文件，而不是分开作为不相关的构造存在的原因。通过阅读可以得知，为类别定义的一切内容都会立即专门化为幺半群。一个去环绕(delooping)的对偶类别是对偶幺半群的去环绕（Riehl，第1.2.2(iii)例，右作用被呈现为左作用的方法）；一个去环绕幺半群的幂等拆分完备是一个类别，其对象是该幺半群的幂等元（Construction/Karoubi.v）；从去环绕出发的函子是一个作用，对于 Vect 中的群来说是一个线性表示。在另一方向上，自同构幺半群 [hom_monoid] 是类别单独观察一个对象的方式，并且它是 Theory/Isomorphism.v 中 [IsIsomorphism] 用来测试可逆性的局部不变量。与树中已有内容的关系。[Instance/CMon.v] 的 [CMonObject] 是下面 [MonObject] 的*交换*版本，具有相同的集合结构和相同的 [Proper] 字段，并用于前加性/二元积的开发；它从交换性导出了右单位律，而一个普通的幺半群必须将两个单位律作为数据。同时，[Theory/Algebra/Monoid.v] 定义了一个在单体范畴内的幺半群*对象*，这在一般情况下是正确的概念，但却将单体结构引入了一个并不需要的构造中；同样适用于 [Structure/Group.v] 的 [GroupObject]，它是在笛卡尔单体范畴中的内部群对象，这就是为什么下面的 [GrpObject] 是一个小的扩展记录。[Theory/Bicategory/OneObject.v] 是在更高一级的相同解环：它将一个单体范畴表示为一个单对象的*二范畴*，元素到箭头的对应字典从 (对象, 箭头) 转换为 (箭头, 2-胞)。最后，[Construction/Funny/Comparison.v] 的 [ListMon] 是一个手写的单对象范畴，基于 [bool] 上的自由单子，为了一个单一的反例而制作。它不是该单子的 [Deloop]：它的复合是 `v ++ u`，即反向乘积（该文件的头部也提到），因此它是对立自由单子的 [Deloop] —— 等价于 `(Deloop FreeBool)^op`，由 Construction/Deloop/Opposite.v 中的 [Deloop_op] 给出。通过 [rev] 两者是同构的，因此没有数学上的影响，但区分正是下面关于复合顺序的要点，并且值得准确说明。另外两个内部单子捐赠者，这里都不能使用：Structure/Monoid.v 定义了 `Monoid := @MonoidObject C CC_Monoidal`（仍然是一个本体范畴），而 Theory/Coq/Monoid.v 是一个仅包含运算的类，不携带任何定律——尽管如此，它已经用文字描述指出单子是一个单对象范畴的同态集，而这正是此文件所证明的声明。
*)

(*
 A monoid: a setoid with a distinguished unit and an associative binary
 operation respecting `≈`, for which the unit is neutral on both sides.
 This is [Instance/CMon.v]'s [CMonObject] minus commutativity, hence with
 the right unit law promoted from a corollary to a field.

 ASSOCIATIVITY ORIENTATION.  The field is stated as

 a * (b * c) ≈ (a * b) * c

 rather than in the more usual left-to-right reading, because that is
 verbatim the orientation of [comp_assoc] in Theory/Category.v.  Delooping
 then supplies the category law by projection instead of by [symmetry], and
 — since [Set Primitive Projections] gives definitional eta for records —
 the round trip [hom_monoid_Deloop] below closes by [eq_refl] rather than
 only up to `≈`.  [mon_op_assoc_sym] restates the law in the other
 orientation for consumers who want it, exactly as [comp_assoc_sym] does
 for categories. 

 --------
 幺半群：一个带有特殊单位元和一个满足 `≈` 的结合二元运算的集合化结构，其中单位元在两侧都是中性的。这是 [Instance/CMon.v] 的 [CMonObject] 减去交换律，因此右单位律从推论提升为一个公理。

 结合性方向。该公理表述为

 a * (b * c) ≈ (a * b) * c而不是按照更常见的从左到右阅读，因为那正是 Theory/Category.v 中 [comp_assoc] 的方向。然后去环（Delooping）通过投影而不是通过 [symmetry] 提供范畴法则，并且——由于 [Set Primitive Projections] 为记录提供定义性的 eta——下面的往返 [hom_monoid_Deloop] 通过 [eq_refl] 闭合，而不仅仅是到 `≈`。[mon_op_assoc_sym] 以另一种方向重新陈述该法则，以满足需要的使用者，正如 [comp_assoc_sym] 对范畴所做的那样。
*)
Record MonObject := {
  mon_setoid :> SetoidObject;

  mon_unit : carrier mon_setoid;
  mon_op : carrier mon_setoid → carrier mon_setoid → carrier mon_setoid;

  mon_op_respects : Proper (equiv ==> equiv ==> equiv) mon_op;

  mon_op_assoc : ∀ a b c,
    mon_op a (mon_op b c) ≈ mon_op (mon_op a b) c;
  mon_op_unit_l : ∀ a, mon_op mon_unit a ≈ a;
  mon_op_unit_r : ∀ a, mon_op a mon_unit ≈ a
}.

#[export] Existing Instance mon_op_respects.

Arguments mon_unit {_}.
Arguments mon_op {_} _ _.
Arguments mon_op_assoc {_} _ _ _.
Arguments mon_op_unit_l {_} _.
Arguments mon_op_unit_r {_} _.

(*
 Associativity in the mirrored orientation, the analogue of
 [comp_assoc_sym]. 

 --------
 在镜像方向上的结合性，[comp_assoc_sym] 的类似物。
*)
Corollary mon_op_assoc_sym (M : MonObject) (a b c : carrier M) :
  mon_op (mon_op a b) c ≈ mon_op a (mon_op b c).
Proof.
  symmetry.
  apply mon_op_assoc.
Qed.

(*
 Inverses in a monoid are unique when they exist: if b is a left inverse of
 a and c is a right inverse of a, then b ≈ c, by the classical computation
 b ≈ b * 1 ≈ b * (a * c) ≈ (b * a) * c ≈ 1 * c ≈ c.  This is what makes the
 inverse operation of [GrpObject] below respect `≈` without carrying a
 [Proper] field of its own. 

 --------
 当逆元存在时，在幺半群中它们是唯一的：如果 b 是 a 的左逆元，而 c 是 a 的右逆元，那么 b ≈ c，这是通过经典计算得到的 b ≈ b * 1 ≈ b * (a * c) ≈ (b * a) * c ≈ 1 * c ≈ c。这就是使得下文 [GrpObject] 的逆运算在不携带自身 [Proper] 字段的情况下依然遵循 `≈` 的原因。
*)
Lemma mon_inverse_unique (M : MonObject) (a b c : carrier M) :
  mon_op b a ≈ mon_unit → mon_op a c ≈ mon_unit → b ≈ c.
Proof.
  intros Hba Hac.
  rewrite <- (mon_op_unit_r b).
  rewrite <- Hac.
  rewrite (mon_op_assoc b a c).
  rewrite Hba.
  apply mon_op_unit_l.
Qed.

(*
   * ** Mac Lane's construction 3: the one-object category B M 

   --------
   * ** 马克·莱恩的构造 3：单对象范畴 B M
*)

(*
 The delooping of a monoid M: one object, the elements of M as its arrows,
 multiplication as composition and the unit as the identity.  Every category
 law is a monoid law by projection, so no obligation is generated.

 Mac Lane and Riehl write [B M] for this category; the name here is
 [Deloop], which keeps the single letter B free as an ordinary variable
 throughout the development.

 COMPOSITION ORDER.  `f ∘ g` in this library means "g first, then f"
 (Theory/Category.v: `compose : (y ~> z) → (x ~> y) → (x ~> z)`), and the
 delooping takes `compose f g := mon_op f g`, i.e. the monoid product in the
 same argument order.  So an element of M read as an arrow multiplies on the
 left exactly as it composes on the left; no opposite monoid is introduced.
 (Riehl's Example 1.2.2(iii) — that `(B G)^op` is `B (G^op)`, proved as
 [Deloop_op] in Construction/Deloop/Opposite.v — is the
 statement that the *other* choice deloops the opposite monoid.)

 The sole object is [ttt : poly_unit] rather than [tt : unit], following
 Instance/One.v and Construction/Funny/Comparison.v: [poly_unit] is
 universe-polymorphic, so the object universe of [Deloop M] stays free
 instead of being pinned at [Set]. 

 --------
 一个幺半群 M 的去环化（delooping）：一个对象，M 的元素作为其箭头，乘法作为合成，单位作为恒等映射。每个范畴定律通过投影都是一个幺半群定律，因此不会产生任何约束。

 Mac Lane 和 Riehl 将该范畴记作 [B M]；这里的名称是 [Deloop]，这样在整个推导过程中，单个字母 B 可以作为普通变量使用。组合顺序。在此库中，`f ∘ g` 意味着“先 g，再 f”（Theory/Category.v: `compose : (y ~> z) → (x ~> y) → (x ~> z)`），而去环(loop解除)采用 `compose f g := mon_op f g`，即在相同参数顺序下的幺半群乘积。因此，作为箭头读取的 M 元素在左侧相乘，恰好如同它在左侧组合一样；没有引入相反的幺半群。（Riehl 的例子 1.2.2(iii) —— `(B G)^op` 是 `B (G^op)`，已在 Construction/Deloop/Opposite.v 中作为 [Deloop_op] 证明 —— 说明了*另一种选择*会去环生成相反的幺半群。）

 唯一对象是 [ttt : poly_unit] 而非 [tt : unit]，遵循 Instance/One.v 和 Construction/Funny/Comparison.v: [poly_unit] 是宇宙多态的，因此 [Deloop M] 的对象宇宙保持自由，而不是固定在 [Set] 上。
*)
Definition Deloop (M : MonObject) : Category := {|
  obj     := poly_unit;                        (* the single object / 单个物体 *)
  hom     := fun _ _ => carrier M;             (* arrows are elements of M / 箭是 M 的元素 *)
  homset  := fun _ _ => is_setoid M;           (* `≈` is the carrier's own / `≈` 是运营商自己的 *)
  id      := fun _ => mon_unit;                (* identity is the unit / 身份是单位 *)
  compose := fun _ _ _ f g => mon_op f g;      (* composition is the product / 作曲是产品 *)

  compose_respects := fun _ _ _ => mon_op_respects M;

  id_left  := fun _ _ => mon_op_unit_l;
  id_right := fun _ _ => mon_op_unit_r;

  comp_assoc     := fun _ _ _ _ => mon_op_assoc;
  comp_assoc_sym := fun _ _ _ _ => mon_op_assoc_sym M
|}.

(* * ** The converse: the endomorphism monoid hom(a, a) / * ** 共轭：自同态幺半群 hom(a, a) *)

(*
 For any category C and object a, the hom-setoid `a ~> a` is a monoid under
 composition, with the identity arrow as unit.  Again every monoid law is a
 category law by projection: [compose_respects], [comp_assoc], [id_left] and
 [id_right] are precisely the four fields required. 

 --------
 对于任意范畴 C 和对象 a，齐次集 `a ~> a` 在复合运算下是一个幺半群，单位元为恒等箭头。同样，每一个幺半群定律通过投影都是一个范畴定律：[compose_respects]、[comp_assoc]、[id_left] 和 [id_right] 恰好是所需的四个域。
*)
Definition hom_monoid (C : Category) (a : C) : MonObject := {|
  mon_setoid := {| carrier := a ~> a; is_setoid := @homset C a a |};

  mon_unit := id;
  mon_op   := fun f g => f ∘ g;

  mon_op_respects := @compose_respects C a a a;

  mon_op_assoc  := fun f g h => comp_assoc f g h;
  mon_op_unit_l := @id_left C a a;
  mon_op_unit_r := @id_right C a a
|}.

(* * ** The correspondence, on the nose / * ** 对应，恰到好处 *)

(*
 Delooping and taking endomorphisms are mutually inverse in the sense that
 can be stated as an equation: the endomorphism monoid of the single object
 of [Deloop M] is M itself, on the nose.  Both the data (carrier, unit,
 operation) and the law fields agree definitionally — the laws because
 [Deloop] took them from M by projection, in the orientation M states them
 in; the records because [Set Primitive Projections] gives eta.

 The opposite composite has no equational form to prove: [Deloop
 (hom_monoid C a)] is a one-object category, whereas C in general has many
 objects, and the honest statement — that it is the full subcategory of C
 on {a} — is a functor-level claim, belonging with the deferred §I.3
 dictionary. 

 --------
 去环化和取自同态是互为逆操作的，可以用一个方程来表述：[Deloop M]的单对象的自同态幺半群就是M本身，完全一致。数据（载体、单位、运算）和律字段在定义上也是一致的——律字段之所以一致，是因为[Deloop]通过投影从M获取它们，以M的方向陈述它们；而记录一致，是因为[Set Primitive Projections]给出了eta。

 相反的复合没有方程形式可证明：[Deloop (hom_monoid C a)]是一个单对象范畴，而C通常有多个对象，诚实的说法是——它是C在{a}上的满子范畴——这是一个函子级的陈述，属于延迟提到的§I.3词典部分。
*)
Example hom_monoid_Deloop (M : MonObject) : hom_monoid (Deloop M) ttt = M :=
  eq_refl.

(*
 The three data fields separately, for readers who want to see which parts
 of the round trip are definitional without unfolding the record equation. 

 --------
 这三个数据字段分别列出，供想要查看往返哪部分是定义性的读者使用，而无需展开记录方程。
*)
Example hom_monoid_Deloop_carrier (M : MonObject) :
  carrier (hom_monoid (Deloop M) ttt) = carrier M := eq_refl.

Example hom_monoid_Deloop_unit (M : MonObject) :
  @mon_unit (hom_monoid (Deloop M) ttt) = @mon_unit M := eq_refl.

Example hom_monoid_Deloop_op (M : MonObject) :
  @mon_op (hom_monoid (Deloop M) ttt) = @mon_op M := eq_refl.

(* * ** Mac Lane's construction 4: the group case / * ** 麦克莱恩的构造 4：群的情况 *)

(*
 A group, as a small extension of [MonObject] by a two-sided inverse
 operation.  As with [MonObject], this is a bare record rather than
 [Structure/Group.v]'s [GroupObject] (a group object internal to a cartesian
 monoidal category): the delooping needs the inverse of an *element*, and
 nothing about the ambient category the group might be internal to.

 [grp_inv] carries no [Proper] field: respecting `≈` is derivable from
 uniqueness of inverses, and is supplied as the instance
 [grp_inv_respects] below. 

 --------
 一个群，是 [MonObject] 在一个双边逆操作下的一个小扩展。像 [MonObject] 一样，这只是一个简单记录，而不是 [Structure/Group.v] 的 [GroupObject]（一个在笛卡尔幺半群范畴内的群对象）：去环化需要一个*元素*的逆，而与群可能内部的环境范畴无关。

 [grp_inv] 不携带 [Proper] 字段：尊重 `≈` 可以由逆元的唯一性推出，并作为下面的实例 [grp_inv_respects] 提供。
*)
Record GrpObject := {
  grp_monoid :> MonObject;

  grp_inv : carrier grp_monoid → carrier grp_monoid;

  grp_inv_l : ∀ a, mon_op (grp_inv a) a ≈ mon_unit;
  grp_inv_r : ∀ a, mon_op a (grp_inv a) ≈ mon_unit
}.

Arguments grp_inv {_} _.
Arguments grp_inv_l {_} _.
Arguments grp_inv_r {_} _.

(*
 Inversion respects `≈`.  If a ≈ b then the inverse of a is also a left
 inverse of b, and [mon_inverse_unique] identifies it with the inverse of b.
 This is a derived instance, not an axiom of the record. 

 --------
 取逆运算尊重 `≈`。如果 a ≈ b，那么 a 的逆元也是 b 的左逆元，并且 [mon_inverse_unique] 将其与 b 的逆元对应。这是一个推导出的实例，而不是记录的公理。
*)
#[export] Instance grp_inv_respects (G : GrpObject) :
  Proper (equiv ==> equiv) (@grp_inv G).
Proof.
  intros a b Hab.
  assert (Hinv : mon_op (grp_inv a) b ≈ mon_unit).
  { rewrite <- Hab.
    apply grp_inv_l. }
  exact (mon_inverse_unique G b (grp_inv a) (grp_inv b) Hinv (grp_inv_r b)).
Qed.

(*
 Every obligation from here to the end of the file is a monoid or group law
 verbatim, so the global [cat_simpl] obligation tactic is switched off (the
 Instance/CMon.v idiom): nothing below needs a proof search, and the searches
 [cat_simpl] would run are the wide ones whose behaviour has differed across
 Rocq versions. 

 --------
 从这里到文件末尾的每一个义务都是单子或群律的逐字体现，因此全局 [cat_simpl] 义务策略被关闭（Instance/CMon.v 习语）：下面没有什么需要证明搜索，而 [cat_simpl] 所进行的搜索是那些在不同 Rocq 版本中行为有所不同的广泛搜索。
*)
#[local] Obligation Tactic := idtac.

(*
 Mac Lane's construction 4: every arrow of the delooping of a group is
 invertible, i.e. [Deloop G] is a one-object groupoid.  The two-sided
 inverse of the arrow f is the group inverse of the element f, and the two
 inverse laws of [IsIsomorphism] are the two group laws verbatim.

 Composed with Theory/Isomorphism.v's [IsIsoToIso] — which is what
 [Deloop_group_iso] below does — this exhibits the single object of
 [Deloop G] as isomorphic to itself in as many ways as G has elements.  That
 its endomorphisms are exactly G is [hom_monoid_Deloop] above; here they are
 in addition all invertible, so they are its automorphisms. 

 --------
 麦克莱恩的构造4：一个群的去环化（delooping）的每一个箭头都是可逆的，即 [Deloop G] 是一个单对象群族（groupoid）。箭头 f 的双边逆元是元素 f 的群逆元，而 [IsIsomorphism] 的两个逆元定律正是两条群定律的逐字对应。

 与 Theory/Isomorphism.v 的 [IsIsoToIso] 组合——这也是下面 [Deloop_group_iso] 所做的——这表明 [Deloop G] 的单个对象与自身同构的方式与群 G 的元素数量相同。它的自同态正好是 G，这在上文 [hom_monoid_Deloop] 中已经说明；在这里，这些自同态额外都是可逆的，因此它们是其自同构。
*)
#[export] Program Instance Deloop_group_invertible (G : GrpObject)
  (x y : Deloop G) (f : x ~{Deloop G}~> y) : IsIsomorphism f := {
  two_sided_inverse := grp_inv f    (* the group inverse of the element f / 元素 f 的群逆 *)
}.
Next Obligation.
  intros G x y f.                   (* f ∘ f⁻¹ ≈ id is a * a⁻¹ ≈ 1 / f ∘ f⁻¹ ≈ id 是 a * a⁻¹ ≈ 1 *)
  apply grp_inv_r.
Qed.
Next Obligation.
  intros G x y f.                   (* f⁻¹ ∘ f ≈ id is a⁻¹ * a ≈ 1 / f⁻¹ ∘ f ≈ id 是 a⁻¹ * a ≈ 1 *)
  apply grp_inv_l.
Qed.

(*
 The same statement in object form: any two objects of [Deloop G] (there is
 only one) are isomorphic, and each element of G names such an isomorphism. 

 --------
 对象形式的相同陈述： [Deloop G] 的任意两个对象（只有一个）都是同构的，并且 G 的每个元素都表示这样一个同构。
*)
Definition Deloop_group_iso (G : GrpObject) (x y : Deloop G)
  (f : x ~{Deloop G}~> y) : x ≅ y :=
  IsIsoToIso f (Deloop_group_invertible G x y f).

(** ** Witnesses / ** 证人 *)

(*
 Both records are inhabited by ordinary algebra, so nothing above is
 vacuously true: the natural numbers under addition are a monoid that is not
 a group, and the booleans under exclusive or are the group Z/2.  Their
 carrier setoids take Coq's own equality as `≈`, which is why the
 [mon_op_respects] field of each is discharged by instance resolution rather
 than appearing as an obligation — every function respects [eq].

 (Both are the standard-library facts [PeanoNat.Nat.add_assoc] and
 [PeanoNat.Nat.add_0_r], which ARE in scope after Category.Lib -- only the
 short [Nat.*] aliases are not.  The inductions are kept because they are two
 lines each and make the witness self-contained, not because the library
 facts are unavailable.) 

 --------
 两个记录都由普通代数构成，因此上面的内容并非空真：自然数在加法下是一个幺半群，但不是群，而布尔值在异或下是群 Z/2。它们的承载集合采用 Coq 自身的等式作为 `≈`，这就是为什么每个记录的 [mon_op_respects] 字段是通过实例解析处理的，而不是作为义务出现——每个函数都遵守 [eq]。

 （两者都是标准库事实 [PeanoNat.Nat.add_assoc] 和 [PeanoNat.Nat.add_0_r]，在 Category.Lib 后处于作用域内 —— 只有简短的 [Nat.*] 别名不在。归纳保留是因为它们每个只有两行，并使见证自包含，而不是因为库事实不可用。）
*)
Lemma nat_add_assoc (a b c : nat) : (a + (b + c))%nat = ((a + b) + c)%nat.
Proof.
  induction a; simpl; [reflexivity | now rewrite IHa].
Qed.

Lemma nat_add_0_r (a : nat) : (a + 0)%nat = a.
Proof.
  induction a; simpl; [reflexivity | now rewrite IHa].
Qed.

(*
 (ℕ, +, 0): the free monoid on one generator, and the first monoid Mac Lane
 names.  Its delooping is the category with one object and one arrow per
 natural number — the free category on a single loop (Fong and Spivak's
 Example 3.13 reads the correspondence off this case).  The carrier setoid
 is Lib/Datatypes.v's [nat_setoid], i.e. Leibniz equality on [nat]. 

 --------
 (ℕ, +, 0)：一个生成元的自由幺半群，也是 Mac Lane 命名的第一个幺半群。它的去循环化是一个类别，该类别只有一个对象，并且每个自然数都有一个箭头——这是一个单环的自由范畴（Fong 和 Spivak 的例 3.13 从这个例子中读取对应关系）。承载集合（setoid）是 Lib/Datatypes.v 中的 [nat_setoid]，即 [nat] 上的莱布尼茨相等性。
*)
Program Definition Nat_Plus : MonObject := {|
  mon_setoid := {| carrier := nat; is_setoid := nat_setoid |};
  mon_unit   := 0%nat;
  mon_op     := Nat.add
|}.
Next Obligation.
  intros a b c.
  apply nat_add_assoc.
Qed.
Next Obligation.
  intros a; reflexivity.            (* 0 + a is a by computation / 0 + a 通过计算等于 a *)
Qed.
Next Obligation.
  intros a.
  apply nat_add_0_r.
Qed.

(*
 (bool, xor, false): the underlying monoid of Z/2, over Leibniz equality on
 [bool]. 

 --------
 (bool, xor, false)：Z/2 的基础幺半群，基于 [bool] 上的莱布尼茨等式。
*)
Program Definition Bool_Xor : MonObject := {|
  mon_setoid := {| carrier := bool
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := false;
  mon_op     := xorb
|}.
Next Obligation.
  intros a b c; now destruct a, b, c.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

(* Z/2 as a group: every element is its own inverse. / 作为群的 Z/2：每个元素都是它自身的逆元。 *)
Program Definition Bool_Xor_Grp : GrpObject := {|
  grp_monoid := Bool_Xor;
  grp_inv    := fun b => b
|}.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

(*
 Composition in the delooping really is the monoid operation: the two are
 the same function, not merely equivalent.  (The objects must be given
 explicitly — the hom of [Deloop M] is the same setoid at every pair of
 objects, so nothing in `a ∘ b` determines them.) 

 --------
 在去环中，组合实际上就是幺半群运算：两者是相同的函数，而不仅仅是等价的。（对象必须明确给出——[Deloop M] 的 Hom 在每对对象上都是相同的集合类，所以 `a ∘ b` 中没有任何东西决定它们。）
*)
Example deloop_nat_compose (a b : Nat_Plus) :
  @compose (Deloop Nat_Plus) ttt ttt ttt a b = (a + b)%nat := eq_refl.

(*
 And the inverse supplied by [Deloop_group_invertible] really is the group
 inverse: in Z/2, that of each arrow is the arrow itself. 

 --------
 由 [Deloop_group_invertible] 提供的逆元素确实是群的逆元：在 Z/2 中，每个箭头的逆元就是箭头本身。
*)
Example deloop_bool_inverse (b : Bool_Xor_Grp) :
  two_sided_inverse
    (IsIsomorphism:=Deloop_group_invertible Bool_Xor_Grp ttt ttt b) = b
  := eq_refl.
