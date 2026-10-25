Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * A category is a monoid in composable pairs (Mac Lane, CWM I.2, Remark 1) / * 一个范畴是在可组合对中的幺半群（Mac Lane，CWM I.2，备注 1） *)

(*
nLab:  https://ncatlab.org/nlab/show/internal+category
   nLab:  https://ncatlab.org/nlab/show/span
   Book:  Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          Section I.2, Remark 1 (printed p. 10)

   Immediately after giving the set-based definition of a category, Mac Lane
   observes that the definition says exactly one thing: a category is a MONOID
   for the product over its object set.  Spelled out, one is given two sets --
   a set O of objects and a set A of arrows -- together with two functions
   dom, cod : A -> O; the composable pairs form the fibred product

       A x_O A  =  { (g, f) in A x A | dom g = cod f },

   and a category structure on the graph (O, A, dom, cod) is precisely a unit

       e : O -> A          with  dom (e x) = cod (e x) = x

   and a multiplication

       m : A x_O A -> A    with  dom (m (g, f)) = dom f,
                                 cod (m (g, f)) = cod g

   that is associative and unital.  That is the germ of two later notions: a
   category internal to a category with pullbacks (replace "set" by "object of
   E" and the fibred product by a pullback), and a monad in the bicategory of
   spans, whose composition IS the fibred product above (nLab, "internal
   category").

--------
nLab: https://ncatlab.org/nlab/show/internal+category
nLab: https://ncatlab.org/nlab/show/span
书籍: Mac Lane, 《工作数学家用的范畴》，第二版，第I.2节，注释1（印刷页10）

在给出基于集合的范畴定义之后，Mac Lane 立刻指出该定义只说明了一件事：范畴是其对象集合上乘积的一个幺半群。具体来说，人们得到两个集合——一个对象集合 O 和一个箭头集合 A——以及两个函数 dom, cod : A -> O；可组合的对构成纤维积。

A x_O A  =  { (g, f) 属于 A x A | dom g = cod f },

并且在图 (O, A, dom, cod) 上的范畴结构恰好是一个单元

e : O -> A          其中 dom(e x) = cod(e x) = x

以及一次乘法

m : A x_O A -> A    且 dom (m (g, f)) = dom f,
                                 cod (m (g, f)) = cod g

它是结合的并且是幺元的。这是两个后来的概念的萌芽：一个具有拉回的范畴内部的范畴（将“集合”替换为 E 的对象，将纤维积替换为拉回），以及在跨度的二元范畴中的一个单子，其组合就是上面的纤维积（nLab，“内部范畴”）。
*)

(*
What this file is, and what it is not

   SCOPE.  This is the SET-LEVEL remark only -- the germ, not the theory.  A
   general internal category, in an arbitrary ambient category with pullbacks,
   is deliberately out of scope, as is the bicategory of spans, and so are
   functors/homomorphisms between the structures defined here.  The object
   sort O is a bare [Type] compared with Coq's strict [eq], NOT a setoid.
   That is faithful to the source: Mac Lane's remark is about the set-based
   presentation, where dom and cod are honest functions into a set of objects
   and the composability condition `dom g = cod f` is an equation between
   elements of that set.  The library's own [Category] does the same -- its
   [obj] is a [Type] and objects are compared by [eq] (see [dom_comp] and
   [cod_comp] in Theory/Category.v) -- so nothing new is being assumed here.
   The arrow sort, by contrast, IS a setoid: morphism comparisons are up to
   the chosen `≈`, as everywhere in this library.

   WHY THIS FILE LIVES HERE.  Theory/Category/ collects re-presentations of
   the [Category] class itself: Theory/Category/Raw.v strips the hom-setoid
   and the laws, Theory/Category/Semi.v drops the identities.  This file adds
   the two-sorted monoid presentation, and its payload is a
   comparison with [Category] -- Raw.v rebuilds a [Category] from raw data
   plus externally supplied laws, Semi.v projects one down to a semigroupoid,
   each one-directional; this file is the first whose payload is a round trip
   in both directions.  It is NOT Construction/Span/Monoid.v: nothing
   here is a construction performed inside an ambient category, and
   Construction/Span/Category.v is about spans in a category, which is a
   different (and heavier) subject.

   WHAT IS NEARBY, AND HOW IT DIFFERS.

   - Structure/Monoid.v defines [MonoidObject]: a monoid in a MONOIDAL
     category, in the sense of Benabou.  That is a different theorem shape.
     There the tensor is a global bifunctor on one category; here the
     "tensor" is the fibred product A x_O A, which is the hom-composition of
     the bicategory of spans over O and is not a monoidal structure on any
     single category in the tree.  The two only coincide after one builds
     Span(Set), which this file does not.

   - Structure/Span.v defines [Span C := Roof ⟶ C]: the diagram SHAPE of a
     span, with no composition and no bicategory structure.  So the
     "monoid in spans" reading of Mac Lane's remark is not available there,
     and this file does not use it either -- it works with the fibred product
     directly.

   - Theory/Metacategory.v and Theory/Metacategory/ArrowsOnly.v formalize
     Mac Lane's OTHER re-presentation, the single-sorted "arrows-only"
     metacategory of CWM I.1, where objects are recovered as identity arrows
     and composition is partial.  This file is the two-sorted remark of I.2:
     objects are a primitive sort and composition is total on the fibred
     product.

   - Construction/Enriched.v (header) already records in prose that
     enrichment is not internalization, and Theory/DoubleCategory.v (header)
     that a double category is a category internal to Cat.  Neither file
     defines an internal category; this one supplies the set-level case those
     remarks point at.

   HONESTY ABOUT STRENGTH (proved below, see the numbered notes in situ).

   1. [Category_from_SpanMonoid] -- the monoid presentation yields a
      [Category] -- is unconditional and axiom-free.

   2. [Category_SpanMonoid] -- an ordinary [Category] yields a monoid
      structure on its graph of bundled arrows -- is proved under an explicit
      hypothesis [HomRigid C]: transport of a morphism along object-equality
      proofs does not depend on WHICH proofs are chosen.  [HomRigid] follows
      at once from UIP on the objects ([HomRigid_of_ObjUIP]), which in turn is
      axiom-free by Hedberg whenever object equality is decidable -- the
      discipline of Construction/Grothendieck/Strict.v and Instance/FinSet.v.
      It is a HYPOTHESIS here, never an [Axiom].  The obstruction is real --
      needed by [arrow_mul_respects] and [arrow_mul_assoc], see NOTE 3 -- and
      genuine: [arrow_mul_respects_forces_UIP] at the end of this file proves
      that discharging it uniformly in C would entail uniqueness of identity
      proofs for every type.  The shape of the problem: multiplying
      along two different proofs of the same composability equation composes
      with two transports of one arrow that differ by a loop at the
      INTERMEDIATE object, and the arrow equivalence's freedom to choose paths
      at the two OUTER objects cannot repair a discrepancy in the middle.
      In the set-based reading Mac Lane intends, O is a set and the question
      does not arise.

   3. Round trips.  Objects match definitionally in both directions
      ([SpanMonoid_roundtrip_obj], [Category_roundtrip_obj], both [eq_refl]).
      On arrows, one composite of each round trip is the identity on the nose
      and the other only up to the relevant `≈`; that is exactly what is
      proved below, and no more is claimed.  Starting from a [Category] the
      comparison assembles into an isomorphism in [Cat]
      ([Category_monoid_iso]).  In this library that is the same strength as
      an equivalence of categories -- Cat's hom-setoid is [Functor_Setoid],
      so a [≅[Cat]] IS an equivalence (Instance/Cat.v, Theory/Equivalence.v's
      [Cat_Iso_to_Equivalence]/[Equivalence_to_Cat_Iso]) -- and it is the
      strongest packaging the library offers, a [StrictCat] isomorphism being
      out of reach without funext.  What is genuinely extra lives in the
      construction rather than the type: both functors are the identity on
      objects, and one hom round trip is definitional ([rb_from_to]).

   UNIVERSES (measured, not asserted -- read off [About] with [Set Printing
   Universes]).

   - [Graph@{o a p}] carries gobj : Type@{o} and garr : Type@{a}
     independently, with p the setoid's proof level.

   - [Category_from_SpanMonoid@{o a} : Graph@{o a a} → … → Category@{o a a}]:
     objects stay at the graph's object level and homs at its arrow level.
     No level is raised.

   - [Category_Graph@{a p _ o} : Category@{o p p} → Graph@{o a p}] with the
     constraints o ≤ a and p ≤ a: the bundled-arrow sort ∃ x y, x ~> y sits
     at the maximum of the object and hom universes, and nowhere higher.
     No successor bump reaches the printed types in either direction
     (auxiliary universes with strict bounds do occur in the constraint sets,
     e.g. [Category_Graph]'s, but none appears in a type), and [Category_Graph] and
     [Category_SpanMonoid] impose NO relation between the object and hom
     levels of the category they start from.

   - Re-building a [Category] from that graph does impose one: because
     [Category_from_SpanMonoid] wants the graph's arrow and proof levels to
     coincide, [Rebuild_to], [Rebuild_from] and [Category_monoid_iso] all
     carry the constraint o ≤ h, the object universe below the hom universe.
     That is the price of asking the original and the rebuilt category to be
     objects of the SAME [Cat].

--------
这个文件是什么，以及它不是什么

范围。 这里只是集合层面的说明——概念的萌芽，而非理论。 一个一般的内部范畴，在任意具有拉回（pullbacks）的环境范畴中，故意不在讨论范围之内，类似的还有跨结构（span）的双范畴，以及此处定义结构之间的函子/同态。 对象范畴 O 与 Coq 的严格 [eq] 相比只是一个简单的 [Type]，而不是集合等价（setoid）。 这忠实于原文：Mac Lane 的说明是关于基于集合的呈现，其中 dom 和 cod 是指向对象集合的真实函数，并且可组合性条件 `dom g = cod f` 是该集合中元素之间的方程。 库自身的 [Category] 也是如此——其 [obj] 是一个 [Type]，对象通过 [eq] 来比较（参见 Theory/Category.v 中的 [dom_comp] 和 [cod_comp]）——所以这里没有假设任何新的内容。 相比之下，箭头范畴确实是一个集合等价集：态射比较是依据所选的 `≈`，正如本库中其他地方一样。

为什么这个文件放在这里。Theory/Category/ 收集了 [Category] 类本身的再表示：Theory/Category/Raw.v 去掉了同态集和定律，Theory/Category/Semi.v 去掉了恒等元。这个文件增加了双排序单子表示，其主要内容是与 [Category] 的比较——Raw.v 从原始数据加上外部提供的定律重建 [Category]，Semi.v 投影到半群类，每个都是单向的；这个文件是第一个内容是在两个方向上往返的。它不是 Construction/Span/Monoid.v：这里没有任何在一个环境范畴内执行的构造，而 Construction/Span/Category.v 是关于范畴中的跨域，这是一个不同的（且更复杂的）主题。

附近的是什么，以及它有何不同。

- Structure/Monoid.v 定义了 [MonoidObject]：在一个 MONOIDAL 范畴中的一个幺半群（monoid），按照 Benabou 的定义。那是不同的定理形式。在那里，张量是在一个范畴上的全局双函子；而这里的“张量”是纤维积 A x_O A，它是 O 上跨度双范畴的同态组合，并不是树中任何单一范畴的幺半群结构。只有在构建 Span(Set) 之后，两者才会一致，而此文件并未进行该步骤。

- Structure/Span.v 定义了 [Span C := Roof ⟶ C]：一个跨度的图形形状，没有组合结构，也没有双范畴结构。因此，Mac Lane 评论中“跨度中的幺半群”这种解读在这里不可用，而且这个文件也没有使用它——它直接处理纤维积。

- Theory/Metacategory.v 和 Theory/Metacategory/ArrowsOnly.v 形式化了 Mac Lane 的另一种表示，单一类型的“仅箭头”元范畴（CWM I.1），其中对象作为恒等箭头被恢复，并且组合是部分的。该文件是 I.2 的双类型备注：对象是原始类型，并且组合在纤维积上是全体的。

- Construction/Enriched.v（标题）已经以散文形式记录了丰富化不是内化，Theory/DoubleCategory.v（标题）记录了双范畴是Cat中的一个内范畴。两个文件都没有定义内范畴；这个文件提供了那些评论所指向的集合层面的情况。

关于力量的诚实（如下所示证明，请参见原位编号注释）。

1. [Category_from_SpanMonoid] —— 幺半群的呈现产生一个 [Category] —— 是无条件且无公理的。

2. [Category_SpanMonoid]——一个普通的 [Category] 在其捆绑箭头的图上产生一个幺半群结构——是在一个明确的假设 [HomRigid C] 下证明的：沿着对象相等性证明对态射进行传输不依赖于选择哪个证明。[HomRigid] 立刻从对象上的 UIP ([HomRigid_of_ObjUIP]) 得出，而根据 Hedberg 定理，当对象相等性可判定时，它又是无公理的——这是 Construction/Grothendieck/Strict.v 和 Instance/FinSet.v 的规范。在这里它是一个假设，从未是 [Axiom]。障碍是真实存在的——在 [arrow_mul_respects] 和 [arrow_mul_assoc] 中需要它，见注释 3——并且是实实在在的：本文件末尾的 [arrow_mul_respects_forces_UIP] 证明了，如果在 C 中统一消除它，将意味着每种类型的恒等证明都是唯一的。
问题的形状：沿着同一可组合性方程的两个不同证明进行乘法，与一个箭头的两个传输组合，这两个传输在中间对象处相差一个环，并且箭头等价在两个外部对象处选择路径的自由不能修复中间的差异。在 Mac Lane 意图的基于集合的解读中，O 是一个集合，因此这个问题不会出现。

3. 往返。 对象在两个方向上在定义上相匹配（[SpanMonoid_roundtrip_obj]、[Category_roundtrip_obj]、以及 [eq_refl]）。 在箭头上，每个往返的一个复合是按字面意义的恒等，另一个则仅在相关的 `≈` 范围内成立；这正是下面所证明的内容，而且没有更多的主张。从 [Category] 开始，比较会组装成在 [Cat] 中的同构（[Category_monoid_iso]）。 在此库中，这与范畴等价的强度相同——Cat 的 hom-集合是 [Functor_Setoid]，因此 [≅[Cat] 是一个等价（Instance/Cat.v, Theory/Equivalence.v 的 [Cat_Iso_to_Equivalence]/[Equivalence_to_Cat_Iso]）——并且这是该库提供的最强封装，没有 funext 无法达到 [StrictCat] 的同构。 真正额外的部分存在于构造中，而不是类型中：两个函子在对象上都是恒等的，并且一个 hom 往返是定义性的（[rb_from_to]）。

UNIVERSES（已测量，非断言——用 [Set Printing Universes] 从 [About] 读取）。

- [Graph@{o a p}] 独立地携带 gobj : Type@{o} 和 garr : Type@{a}，其中 p 是集合等价的证明层级。

- [Category_from_SpanMonoid@{o a} : Graph@{o a a} → … → Category@{o a a}]:
     对象保持在图的对象层级，箭头保持在其箭头层级。
     没有层级被提升。

- [Category_Graph@{a p _ o} : Category@{o p p} → Graph@{o a p}] 在约束条件 o ≤ a 和 p ≤ a 下：捆绑箭头排序 ∃ x y, x ~> y 位于对象和态射宇宙的最大位置，并且没有更高的位置。无论向哪个方向，后续的提升都无法到达打印类型（严格界限的辅助宇宙确实出现在约束集合中，例如 [Category_Graph] 的，但没有出现在类型中），并且 [Category_Graph] 和 [Category_SpanMonoid] 对它们开始时的范畴的对象层级与态射层级之间没有任何关系。

- 从那个图重建 [Category] 确实会施加一个条件：因为 [Category_from_SpanMonoid] 希望图中的箭头和证明级别相一致，[Rebuild_to]、[Rebuild_from] 和 [Category_monoid_iso] 都包含约束 o ≤ h，即对象宇宙位于同态宇宙之下。这就是要求原始范畴和重建范畴成为同一个 [Cat] 的代价。
*)

(** ** Two-sorted graphs / ** 二类图 *)

(*
A graph in Mac Lane's sense: an object sort [gobj], an arrow sort [garr]
   with a chosen equivalence, and the two boundary maps.  The two
   respectfulness fields say that `≈`-equivalent arrows have equal endpoints;
   they are what makes the arrow sort a graph over [gobj] rather than merely a
   setoid with two functions out of it, and they are exactly what the arrow
   round trip below needs.

--------
在 Mac Lane 的意义下的图：一个对象类型 [gobj]，一个箭头类型 [garr]，并带有一个选定的等价关系，以及两个边界映射。这两个相容性字段说明 `≈` 等价的箭头具有相同的端点；它们使得箭头类型成为 [gobj] 上的图，而不仅仅是带有两个函数的集合论结构，并且它们正是下面箭头往返所需要的。
*)
Record Graph := {
  gobj : Type;                          (* the object sort O / 对象类型 O *)
  garr : Type;                          (* the arrow sort A / 箭头排序 A *)
  garr_setoid : Setoid garr;            (* arrows are compared up to ≈ / 箭头最多比较到 ≈ *)

  gdom : garr → gobj;                   (* dom : A → O / dom : A → O *)
  gcod : garr → gobj;                   (* cod : A → O / cod：A → O *)

  gdom_respects (a b : garr) :          (* ≈-equal arrows share a domain / ≈-相等的箭头共享一个域 *)
    @equiv _ garr_setoid a b → gdom a = gdom b;
  gcod_respects (a b : garr) :          (* ≈-equal arrows share a codomain / ≈-相等的箭头共享一个余域 *)
    @equiv _ garr_setoid a b → gcod a = gcod b
}.

Arguments gdom {_} _.
Arguments gcod {_} _.
Arguments gdom_respects {_ _ _} _.
Arguments gcod_respects {_ _ _} _.

#[export] Existing Instance garr_setoid.

(** ** The composable pairs A ×_O A / ** 可组合对 A ×_O A *)

(*
The fibred product `A ×_O A = { (g, f) | dom g = cod f }`, kept as data (a
   record, i.e. a sigma) rather than as a subset: [cp_match] is a genuine
   inhabitant of an equality type, available for transport.  [cp_outer] and
   [cp_inner] are the two projections; in the composite `m (g, f)` the outer
   arrow g is the one applied last, matching the library's convention that
   `f ∘ g` runs g first.

--------
纤维积 `A ×_O A = { (g, f) | dom g = cod f }` 以数据（记录，即 sigma 类型）而不是子集的形式保存：[cp_match] 是一个真正的等式类型的元素，可以用于迁移。[cp_outer] 和 [cp_inner] 是两个投影；在复合 `m (g, f)` 中，外部箭头 g 是最后应用的，这符合库的约定，即 `f ∘ g` 先运行 g。
*)
Record Composable (G : Graph) := {
  cp_outer : garr G;                             (* g *)
  cp_inner : garr G;                             (* f *)
  cp_match : gdom cp_outer = gcod cp_inner       (* the composability equation / 可组合性方程 *)
}.

Arguments cp_outer {_} _.
Arguments cp_inner {_} _.
Arguments cp_match {_} _.
Arguments Build_Composable {_} _ _ _.

(*
Two composable pairs are identified when their two projections are.  This
   is the correct setoid on a pullback taken over a sort compared by strict
   equality: the third component is a proof of an equation in [gobj] and
   carries no further information about the pair.  Note that it is NOT `eq` on
   [Composable] -- see [Composable_ump_unique].

--------
当它们的两个投影存在时，一个可组合的对就被确定。这是在通过严格相等比较的排序上取拉回的正确集合：第三个分量是 [gobj] 中一个等式的证明，并不携带关于该对的进一步信息。注意，它不是 `eq` 在 [Composable] 上——参见 [Composable_ump_unique]。
*)
Definition Composable_equiv {G : Graph} (p q : Composable G) : Type :=
  (cp_outer p ≈ cp_outer q) ∧ (cp_inner p ≈ cp_inner q).

Definition Composable_Setoid (G : Graph) : Setoid (Composable G).
Proof.
  refine {| equiv := @Composable_equiv G; setoid_equiv := _ |}.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct X; split; now symmetry.
  - destruct X, X0; split; etransitivity; eassumption.
Defined.

(*
Both projections respect that equivalence, so each is a setoid map
   `A ×_O A → A`.

--------
两个投影都尊重该等价关系，因此每个都是一个集合同态 `A ×_O A → A`。
*)
Lemma cp_outer_respects {G : Graph} (p q : Composable G) :
  Composable_equiv p q → cp_outer p ≈ cp_outer q.
Proof. now intros [H _]. Qed.

Lemma cp_inner_respects {G : Graph} (p q : Composable G) :
  Composable_equiv p q → cp_inner p ≈ cp_inner q.
Proof. now intros [_ H]. Qed.

(*
The universal property, in the only form available without quotients: a
   pair of maps into [garr] whose boundaries agree factors through the
   composable pairs, on the nose on both projections.

--------
通用性质，在唯一没有商的形式下：一对映射到 [garr]，其边界一致，通过可组合对的映射在两个投影上严格成立。
*)
Definition Composable_med {G : Graph} {X : Type}
           (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x))
           (x : X) : Composable G :=
  Build_Composable (u x) (v x) (H x).

Lemma Composable_med_outer {G : Graph} {X : Type}
      (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x)) (x : X) :
  cp_outer (Composable_med u v H x) = u x.
Proof. reflexivity. Qed.

Lemma Composable_med_inner {G : Graph} {X : Type}
      (u v : X → garr G) (H : ∀ x, gdom (u x) = gcod (v x)) (x : X) :
  cp_inner (Composable_med u v H x) = v x.
Proof. reflexivity. Qed.

(*
Uniqueness, stated honestly: the mediating map is determined by its two
   projections UP TO [Composable_equiv], not up to `eq`.  Two mediating maps
   with the same projections can still differ in the proof component, and
   identifying those would need proof irrelevance or UIP on [gobj], neither of
   which is assumed.  Since [Composable_equiv] is the equivalence the
   multiplication is required to respect, this is the uniqueness that is
   actually used.

--------
独特性，坦率地说：中介映射是由它的两个投影决定的，范围是 [Composable_equiv]，而不是 `eq`。两个具有相同投影的中介映射在证明部分仍然可能不同，而要识别这些不同需要 [gobj] 上的证明无关性或 UIP，这两者都没有假设。由于 [Composable_equiv] 是乘法需要遵守的等价关系，这就是实际上使用的唯一性。
*)
Lemma Composable_ump_unique {G : Graph} {X : Type} (k k' : X → Composable G) :
  (∀ x, cp_outer (k x) ≈ cp_outer (k' x)) →
  (∀ x, cp_inner (k x) ≈ cp_inner (k' x)) →
  ∀ x, Composable_equiv (k x) (k' x).
Proof. intros Ho Hi x; split; [ apply Ho | apply Hi ]. Qed.

(** ** The monoid structure on a graph / ** 图上的幺半群结构 *)

(*
Mac Lane's unit and multiplication, with their boundary conditions and
   laws.  The multiplication is presented in curried form, taking the
   composability proof as an explicit argument, because that is how it is
   applied; [sm_pair_mul] below repackages it as the map `A ×_O A → A` of the
   remark and [sm_pair_mul_respects] shows the curried respectfulness field is
   exactly respectfulness for the pullback setoid.

   All laws are stated up to the arrow setoid's `≈`, and universally over the
   composability proofs.  Quantifying over the proofs is not a weakening: it
   is the content of "m is a function on A ×_O A", since two composable pairs
   with the same components are the same element of the pullback whatever
   proof witnesses their composability.

--------
Mac Lane 的单位和乘法，以及它们的边界条件和公理。乘法以柯里化形式呈现，将可组合性证明作为显式参数，因为这就是它的应用方式；下面的 [sm_pair_mul] 将其重新打包为该备注中的映射 `A ×_O A → A`，而 [sm_pair_mul_respects] 显示柯里化的尊重性字段正好是拉回集合的尊重性。

所有公理都在箭头集合的 `≈` 下陈述，并且在可组合性证明上是普遍的。对证明进行量化并不是一种弱化：它是“m 是 A ×_O A 上的函数”的内容，因为具有相同组件的两个可组合对无论哪个证明见证它们的可组合性，都是拉回中的同一个元素。
*)
Record SpanMonoid (G : Graph) := {
  sm_unit : gobj G → garr G;                     (* e : O → A / e : O → A *)
  sm_unit_dom : ∀ x, gdom (sm_unit x) = x;       (* dom (e x) = x / dom (e x) = x *)
  sm_unit_cod : ∀ x, gcod (sm_unit x) = x;       (* cod (e x) = x / cod (e x) = x *)

  sm_mul (g f : garr G) : gdom g = gcod f → garr G;   (* m : A ×_O A → A / m : A ×_O A → A *)

  sm_mul_dom : ∀ g f p, gdom (sm_mul g f p) = gdom f;  (* dom (m (g,f)) = dom f / dom (m (g,f)) = dom f *)
  sm_mul_cod : ∀ g f p, gcod (sm_mul g f p) = gcod g;  (* cod (m (g,f)) = cod g / cod (m (g,f)) = cod g *)

  (*
m is a map out of the pullback setoid: it respects `≈` componentwise and
     does not depend on the composability witness.

--------
m 是一个从拉回集合等价类出的映射：它在各组成部分上遵守 `≈`，并且不依赖于可组合性证据。
*)
  sm_mul_respects : ∀ g g' f f' p p',
    g ≈ g' → f ≈ f' → sm_mul g f p ≈ sm_mul g' f' p';

  sm_id_left  : ∀ f p, sm_mul (sm_unit (gcod f)) f p ≈ f;   (* e ∘ f = f / e ∘ f = f *)
  sm_id_right : ∀ f p, sm_mul f (sm_unit (gdom f)) p ≈ f;   (* f ∘ e = f / f ∘ e = f *)

  (* Associativity, in the orientation of [comp_assoc]. / 结合性，在 [comp_assoc] 的方向上。 *)
  sm_assoc : ∀ h g f (p : gdom h = gcod g) (q : gdom g = gcod f)
               (pl : gdom (sm_mul h g p) = gcod f)
               (pr : gdom h = gcod (sm_mul g f q)),
    sm_mul h (sm_mul g f q) pr ≈ sm_mul (sm_mul h g p) f pl
}.

Arguments sm_unit {_} _ _.
Arguments sm_unit_dom {_} _ _.
Arguments sm_unit_cod {_} _ _.
Arguments sm_mul {_} _ _ _ _.
Arguments sm_mul_dom {_} _ _ _ _.
Arguments sm_mul_cod {_} _ _ _ _.
Arguments sm_mul_respects {_} _ {_ _ _ _} _ _ _ _.
Arguments sm_id_left {_} _ _ _.
Arguments sm_id_right {_} _ _ _.
Arguments sm_assoc {_} _ _ _ _ _ _ _ _.

(*
The multiplication as a map out of the composable pairs, which is the shape
   in which Mac Lane states it.

--------
乘法作为从可组合对到映射的形式，这就是 Mac Lane 陈述它的方式。
*)
Definition sm_pair_mul {G : Graph} (M : SpanMonoid G) (p : Composable G) : garr G :=
  sm_mul M (cp_outer p) (cp_inner p) (cp_match p).

(*
...and the curried respectfulness field is precisely respectfulness for the
   pullback setoid.  Both directions, so that neither presentation is
   privileged.

--------
...而柯里化的尊重性域正是对拉回集合等价关系的尊重性。两个方向都考虑，以确保没有一种表达是优先的。
*)
Lemma sm_pair_mul_respects {G : Graph} (M : SpanMonoid G) (p q : Composable G) :
  Composable_equiv p q → sm_pair_mul M p ≈ sm_pair_mul M q.
Proof.
  intros [Ho Hi]; unfold sm_pair_mul.
  now apply (sm_mul_respects M).
Qed.

Lemma sm_mul_of_pair {G : Graph} (M : SpanMonoid G)
      (m : Composable G → garr G)
      (Hm : ∀ p q, Composable_equiv p q → m p ≈ m q)
      (g g' f f' : garr G) (p : gdom g = gcod f) (p' : gdom g' = gcod f') :
  g ≈ g' → f ≈ f' → m (Build_Composable g f p) ≈ m (Build_Composable g' f' p').
Proof. intros Hg Hf; now apply Hm; split. Qed.

(** ** From the monoid presentation to a [Category] / ** 从幺半群表示到 [Category] *)

(*
The hom from x to y: an arrow together with proofs pinning its endpoints.
   The proofs are kept as data so that they may be used to build the
   composability witness; they are invisible to the hom-setoid, which compares
   only the underlying arrows.

--------
从 x 到 y 的同态：一个箭头以及固定其端点的证明。证明被作为数据保留，以便可以用来构建可组合性证据；它们对于同态集体是不可见的，同态集体只比较底层的箭头。
*)
Definition SMHom (G : Graph) (x y : gobj G) : Type :=
  { a : garr G & (gdom a = x) ∧ (gcod a = y) }.

Definition sa_arr {G : Graph} {x y : gobj G} (f : SMHom G x y) : garr G := `1 f.
Definition sa_dom {G : Graph} {x y : gobj G} (f : SMHom G x y)
  : gdom (sa_arr f) = x := fst (`2 f).
Definition sa_cod {G : Graph} {x y : gobj G} (f : SMHom G x y)
  : gcod (sa_arr f) = y := snd (`2 f).

(*
The hom-setoid compares only the underlying arrows: the endpoint proofs are
   invisible to it.

--------
霍姆-集合类只比较底层的箭头：端点证明对它是不可见的。
*)
Definition SpanArrow_equiv {G : Graph} {x y : gobj G}
           (f g : SMHom G x y) : Type := sa_arr f ≈ sa_arr g.

Definition SpanArrow_Setoid (G : Graph) (x y : gobj G)
  : Setoid (SMHom G x y).
Proof.
  refine {| equiv := @SpanArrow_equiv G x y; setoid_equiv := _ |}.
  unfold SpanArrow_equiv.
  constructor.
  - intros f; reflexivity.
  - intros f g H; symmetry; exact H.
  - intros f g h H1 H2; transitivity (sa_arr g); assumption.
Defined.

(* The identity at x is the unit e x, carrying its two boundary laws. / 在 x 的恒等元是单位 e x，遵循它的两个边界律。 *)
Definition smc_id {G : Graph} (M : SpanMonoid G) (x : gobj G) : SMHom G x x :=
  (sm_unit M x; (sm_unit_dom M x, sm_unit_cod M x)).

(*
Two homs that meet at y are composable in the graph: their endpoint proofs
   compose to the required equation `dom g = cod f`.

--------
在图中，两个在 y 相遇的同态是可组合的：它们的端点证明可以组合成所需的方程 `dom g = cod f`。
*)
Definition smc_match {G : Graph} {x y z : gobj G}
           (g : SMHom G y z) (f : SMHom G x y)
  : gdom (sa_arr g) = gcod (sa_arr f) :=
  eq_trans (sa_dom g) (eq_sym (sa_cod f)).

(*
Composition is the monoid multiplication; the boundary laws of the
   multiplication supply the endpoint proofs of the result.

--------
组合就是单子乘法；乘法的边界律提供了结果的端点证明。
*)
Definition smc_compose {G : Graph} (M : SpanMonoid G) {x y z : gobj G}
           (g : SMHom G y z) (f : SMHom G x y) : SMHom G x z :=
  (sm_mul M (sa_arr g) (sa_arr f) (smc_match g f);
    (eq_trans (sm_mul_dom M _ _ _) (sa_dom f),
     eq_trans (sm_mul_cod M _ _ _) (sa_cod g))).

(*
NOTE 1.  Unconditional and axiom-free: no UIP, no rigidity, no hypothesis
   on [gobj] beyond its being a [Type].  Every law follows from the
   corresponding [SpanMonoid] field, the proof-independence of
   [sm_mul_respects] absorbing the fact that the composability witness built
   by [smc_match] depends on the endpoint proofs carried by the homs, which
   the hom-setoid cannot see.

--------
注 1. 无条件且无公理：没有 UIP，没有刚性，对 [gobj] 除了它是 [Type] 外没有任何假设。每条定律都源自相应的 [SpanMonoid] 域，[sm_mul_respects] 的证明独立性吸收了一个事实，即由 [smc_match] 构建的可组合性证明依赖于同构携带的端点证明，而同构集合无法看到这些证明。
*)
Definition Category_from_SpanMonoid {G : Graph} (M : SpanMonoid G) : Category.
Proof.
  unshelve refine (Build_Category' (SMHom G) (smc_id M) (@smc_compose G M)).
  - exact (SpanArrow_Setoid G).
  - proper.
    unfold smc_compose, sa_arr; simpl.
    now apply (sm_mul_respects M).
  - intros x y f.
    unfold smc_compose, smc_id, sa_arr; simpl.
    destruct f as [a [pd pc]]; simpl in *.
    destruct pc.
    now apply (sm_id_left M).
  - intros x y f.
    unfold smc_compose, smc_id, sa_arr; simpl.
    destruct f as [a [pd pc]]; simpl in *.
    destruct pd.
    now apply (sm_id_right M).
  - intros x y z w f g h.
    unfold smc_compose, sa_arr; simpl.
    apply (sm_assoc M).
Defined.

(** ** Bundled arrows, and transport along object equalities / ** 捆绑箭头，以及沿对象等式的传输 *)

(* The bundled-arrow sigma ∃ x y, x ~> y, as a record. / 捆绑箭头西格玛 ∃ x y, x ~> y，作为一个记录。 *)
Record BundledArrow (C : Category) := {
  asrc : C;
  atgt : C;
  aarr : asrc ~> atgt
}.

Arguments asrc {_} _.
Arguments atgt {_} _.
Arguments aarr {_} _.
Arguments Build_BundledArrow {_} _ _ _.

(*
The groupoid laws for [eq] that the transport pack needs.  Each is proved by
   [destruct] with both endpoints universally quantified, which is what makes
   it applicable later at a LOOP `e : x = x`, where [destruct] is unavailable.
   None of this is UIP: no two proofs of the same equation are identified.

--------
[eq] 的群类定律是传输包所需要的。每个定律都由 [destruct] 证明，两个端点都是全称量化的，这使得它在之后的 LOOP `e : x = x` 中适用，而在该处 [destruct] 是不可用的。这些都不是 UIP：同一个方程的两个证明之间没有被识别为相同。
*)
Lemma eq_trans_id_l {A : Type} {x y : A} (e : x = y) : eq_trans eq_refl e = e.
Proof. destruct e; reflexivity. Qed.

Lemma eq_trans_id_r {A : Type} {x y : A} (e : x = y) : eq_trans e eq_refl = e.
Proof. destruct e; reflexivity. Qed.

Lemma eq_trans_sym_l {A : Type} {x y : A} (e : x = y) :
  eq_trans (eq_sym e) e = eq_refl.
Proof. destruct e; reflexivity. Qed.

(*
Transport of a morphism along equalities of its two endpoints.  Everything
   in this section is proved by [destruct]ing the equalities in their general
   form (both endpoints universally quantified), so none of it uses UIP.

--------
沿着其两个端点的等式传输一个态射。本节中的所有内容都是通过对一般形式的等式（两个端点都是全称量化的）进行 [destruct] 证明的，因此其中没有使用 UIP。
*)
Definition hom_transport {C : Category} {x x' y y' : C}
           (p : x = x') (q : y = y') (f : x ~> y) : x' ~> y' :=
  match p in (_ = X) return (X ~> y') with
  | eq_refl => match q in (_ = Y) return (x ~> Y) with
               | eq_refl => f
               end
  end.

(*
Keep [simpl] from tearing the transports open into raw [match]es: every
   fact about them below is stated at the level of [hom_transport] itself.

--------
防止 [simpl] 将运输体撕开成原始的 [match]：以下关于它们的每一个事实都是以 [hom_transport] 本身的层面陈述的。
*)
Arguments hom_transport : simpl never.

#[export]
Instance hom_transport_respects {C : Category} {x x' y y' : C}
         (p : x = x') (q : y = y') :
  Proper (equiv ==> equiv) (hom_transport p q).
Proof. destruct p, q; repeat intro; assumption. Qed.

Lemma hom_transport_refl {C : Category} {x y : C} (f : x ~> y) :
  hom_transport eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

Lemma hom_transport_trans {C : Category} {x1 x2 x3 y1 y2 y3 : C}
      (p : x1 = x2) (p' : x2 = x3) (q : y1 = y2) (q' : y2 = y3) (f : x1 ~> y1) :
  hom_transport p' q' (hom_transport p q f)
    = hom_transport (eq_trans p p') (eq_trans q q') f.
Proof. destruct p, p', q, q'; reflexivity. Qed.

Lemma hom_transport_sym_inv {C : Category} {x x' y y' : C}
      (p : x = x') (q : y = y') (f : x ~> y) :
  hom_transport (eq_sym p) (eq_sym q) (hom_transport p q f) = f.
Proof. destruct p, q; reflexivity. Qed.

Lemma hom_transport_id {C : Category} {x x' : C} (u : x = x') :
  hom_transport u u (id[x]) = id[x'].
Proof. destruct u; reflexivity. Qed.

(*
Transport of a composite splits into transport of the two outer endpoints;
   the shared middle object is untouched.

--------
复合体的传输分为传输两个外端点；共享的中间对象保持不变。
*)
Lemma hom_transport_comp {C : Category} {x x' y z z' : C}
      (p : x = x') (r : z = z') (f : y ~> z) (g : x ~> y) :
  hom_transport p r (f ∘ g)
    = hom_transport eq_refl r f ∘ hom_transport p eq_refl g.
Proof. destruct p, r; reflexivity. Qed.

(* Transport at the middle object slides across a composite. / 中间物体上的运输滑过复合材料。 *)
Lemma hom_transport_slide {C : Category} {w x x' y : C}
      (u : x = x') (f : x ~> y) (g : w ~> x) :
  f ∘ g = hom_transport u eq_refl f ∘ hom_transport eq_refl u g.
Proof. destruct u; reflexivity. Qed.

(** ** The graph of a category / ** 一个范畴的图 *)

(*
Two bundled arrows are equivalent when there are equalities of their
   endpoints carrying one to the other up to `≈`.  The equalities are kept as
   data ([sigT], not [ex]) so the witnesses can be chosen and reused.

--------
当它们的端点之间存在将一个端点映射到另一个端点的相等关系（直到 `≈`）时，两个捆绑的箭头是等价的。相等关系作为数据保留（[sigT]，而不是 [ex]），以便可以选择和重用见证者。
*)
Definition BundledArrow_equiv {C : Category} (a b : BundledArrow C) : Type :=
  { p : asrc a = asrc b &
  { q : atgt a = atgt b & hom_transport p q (aarr a) ≈ aarr b }}.

Definition BundledArrow_Setoid (C : Category) : Setoid (BundledArrow C).
Proof.
  refine {| equiv := @BundledArrow_equiv C; setoid_equiv := _ |}.
  constructor; repeat intro.
  - exists eq_refl, eq_refl; reflexivity.
  - destruct X as [p [q H]].
    exists (eq_sym p), (eq_sym q).
    rewrite <- H, hom_transport_sym_inv.
    reflexivity.
  - destruct X as [p [q H]], X0 as [p' [q' H']].
    exists (eq_trans p p'), (eq_trans q q').
    rewrite <- hom_transport_trans, H.
    exact H'.
Defined.

Definition Category_Graph (C : Category) : Graph.
Proof.
  unshelve refine {| gobj := obj[C]
                   ; garr := BundledArrow C
                   ; garr_setoid := BundledArrow_Setoid C
                   ; gdom := @asrc C
                   ; gcod := @atgt C |}.
  - intros a b H; exact (`1 H).
  - intros a b H; exact (`1 (`2 H)).
Defined.

(** ** Rigidity: when transport does not see which proof it travelled along / ** 刚性：当传输无法看到它沿哪条路径传输时 *)

(*
NOTE 2.  The hypothesis under which an ordinary category yields a monoid on
   its graph of bundled arrows.  It says that transporting a morphism along
   object equalities depends only on the endpoints, not on the proofs.  This
   is implied by UIP on the objects, and holds trivially in the set-based
   reading Mac Lane intends.  It is never assumed as an [Axiom]: every result
   below that needs it takes it as an argument.

--------
注意2. 在普通范畴下，其捆绑箭头的图上产生幺半群的假设。它表示沿对象等式传输态射仅依赖于端点，而不依赖于证明。这由对象上的UIP（唯一恒等原理）推导，并且在Mac Lane意图的基于集合的解释中显然成立。在任何情况下，这都不是假定条件：下面需要它的每个结果都将其作为参数引入。
*)
Definition HomRigid (C : Category) : Type :=
  ∀ (x x' y y' : C) (p p' : x = x') (q q' : y = y') (f : x ~> y),
    hom_transport p q f ≈ hom_transport p' q' f.

Definition ObjUIP (C : Category) : Type :=
  ∀ (x y : C) (p q : x = y), p = q.

(*
UIP on objects gives rigidity.  [ObjUIP] is axiom-free for every category
   whose object equality is decidable, by Hedberg's argument -- the discipline
   already used in Instance/FinSet.v and Theory/Multicategory/Endomorphism.v.

--------
对象上的 UIP 提供了刚性。根据 Hedberg 的论证，对于每个对象相等性可判定的范畴，[ObjUIP] 是无公理的——这一方法已经在 Instance/FinSet.v 和 Theory/Multicategory/Endomorphism.v 中使用。
*)
Lemma HomRigid_of_ObjUIP {C : Category} : ObjUIP C → HomRigid C.
Proof.
  intros U x x' y y' p p' q q' f.
  rewrite (U _ _ p p'), (U _ _ q q').
  reflexivity.
Qed.

(*
The calculation behind functoriality of the comparison [Rebuild_from]
   below, stated once over arbitrary transport data.  Composing two arrows
   after transporting their boundaries is the same as transporting the
   boundaries of their composite, provided one may ignore WHICH object paths
   were used -- which is what [HomRigid] grants.  The intermediate objects of
   the two composites differ (one meets at the domain of the outer arrow, the
   other at the shared object of the two homs), so [hom_transport_slide] is
   what carries the one to the other.

--------
下面关于比较 [Rebuild_from] 的函子性背后的计算，曾在任意传输数据上说明过。将两个箭头在传输它们的边界后组成，与传输它们的复合的边界是相同的，前提是可以忽略使用了哪些对象路径——这就是 [HomRigid] 所授予的。两个复合的中间对象不同（一个在外箭头的定义域处会合，另一个在两个同态的共享对象处会合），所以 [hom_transport_slide] 才是将一个带到另一个的方式。
*)
Lemma hom_transport_compose_compare {C : Category} (rigid : HomRigid C)
      {xa ya xb yb x y z : C} (α : xa ~> ya) (β : xb ~> yb)
      (da : xa = y) (ca : ya = z) (db : xb = x) (cb : yb = y)
      (P : xa = yb) (dc : xb = x) (cc : ya = z) :
  hom_transport dc cc (α ∘ hom_transport eq_refl (eq_sym P) β)
    ≈ hom_transport da ca α ∘ hom_transport db cb β.
Proof.
  rewrite hom_transport_comp, hom_transport_trans.
  rewrite eq_trans_id_l, eq_trans_id_r.
  rewrite (hom_transport_slide da (hom_transport eq_refl cc α)
                                  (hom_transport dc (eq_sym P) β)).
  rewrite !hom_transport_trans, !eq_trans_id_l, !eq_trans_id_r.
  now rewrite (rigid _ _ _ _ da da cc ca α),
              (rigid _ _ _ _ dc db (eq_trans (eq_sym P) da) cb β).
Qed.

(** ** From a [Category] to the monoid presentation / ** 从 [Category] 到幺半群表示 *)

(*
The unit is the identity arrow; the multiplication is composition, after
   transporting the inner arrow's codomain to the outer arrow's domain along
   the composability proof.

--------
单位是恒等箭头；乘法是组合，在沿着可组合性证明将内箭头的陪域传输到外箭头的定义域之后进行。
*)
Definition arrow_unit {C : Category} (x : C) : BundledArrow C :=
  Build_BundledArrow x x (id[x]).

Definition arrow_mul {C : Category} (g f : BundledArrow C) (p : asrc g = atgt f)
  : BundledArrow C :=
  Build_BundledArrow (asrc f) (atgt g)
    (aarr g ∘ hom_transport eq_refl (eq_sym p) (aarr f)).

(*
The two unit laws hold WITHOUT rigidity.  The trick is that the arrow
   equivalence lets one choose the object paths: the very proof [p] that has
   to be transported along is offered back as the witness, and the two
   transports cancel by [eq_trans_sym_l] / [hom_transport_id].  This is worth
   isolating, because it confines the obstruction of [arrow_mul_respects]
   below to that one law rather than to the correspondence at large.

--------
这两个单位律在没有严格性的情况下成立。诀窍在于箭头等价让人可以选择对象路径：必须沿着传输的证明 [p] 被作为见证返回，而两个传输通过 [eq_trans_sym_l] / [hom_transport_id] 相互抵消。这值得单独提出，因为它将下文 [arrow_mul_respects] 的障碍限制在这一条定律上，而不是整个对应关系上。
*)
Lemma arrow_mul_id_left {C : Category} (f : BundledArrow C) (p : atgt f = atgt f) :
  BundledArrow_equiv (arrow_mul (arrow_unit (atgt f)) f p) f.
Proof.
  destruct f as [xf yf φf]; simpl in *.
  unfold BundledArrow_equiv, arrow_mul, arrow_unit; simpl.
  exists eq_refl, p.
  rewrite id_left, hom_transport_trans, eq_trans_sym_l, eq_trans_id_l.
  now rewrite hom_transport_refl.
Qed.

Lemma arrow_mul_id_right {C : Category} (f : BundledArrow C) (p : asrc f = asrc f) :
  BundledArrow_equiv (arrow_mul f (arrow_unit (asrc f)) p) f.
Proof.
  destruct f as [xf yf φf]; simpl in *.
  unfold BundledArrow_equiv, arrow_mul, arrow_unit; simpl.
  exists (eq_sym p), eq_refl.
  rewrite hom_transport_comp, hom_transport_refl, hom_transport_trans.
  rewrite eq_trans_id_l, eq_trans_id_r, hom_transport_id.
  now rewrite id_right.
Qed.

(*
NOTE 3.  Respectfulness of the multiplication is where the correspondence
   first meets [HomRigid], and it is the essential use.  Multiplying the same
   pair along two proofs p, p' of the same composability equation composes the
   outer arrow with two transports of the inner arrow that differ by a loop at
   the INTERMEDIATE object -- the object where the two arrows meet.  The arrow
   equivalence is free to pick paths at the source and the target of the
   composite, but neither is the intermediate object, so that freedom cannot
   repair the discrepancy.  And the hypothesis is unavoidable, not merely
   convenient: [arrow_mul_respects_forces_UIP] at the end of this file shows
   that proving [arrow_mul_respects] without it, uniformly in C, entails
   uniqueness of identity proofs for every type.  The countermodel is chosen
   so the composite lands in a RIGID corner: objects [option A], where
   [None]'s loop space is provably contractible by an encode-decode argument,
   pinning the setoid freedom at the outer objects while the intermediate
   object [Some a] keeps the loops of A.

   The exact tally over the eight law fields of [SpanMonoid], as proved: the two
   unit laws are rigidity-free ([arrow_mul_id_left], [arrow_mul_id_right]);
   [arrow_mul_respects] and [arrow_mul_assoc] both use it, the latter because
   the record quantifies over ARBITRARY witnesses for the two derived
   composability equations, so the same intermediate-object discrepancy
   arises there too.

--------
注 3：乘法的尊重是对应关系
 第一次认识[HomRigid]，就是必不可少的用途。 相乘相同
 沿着同一可组合性方程的两个证明 p, p' 的对组成
 外部箭头与内部箭头的两个传输不同之处在于循环
 中间对象——两个箭头相交的对象。 箭头
 等价性可以在源和目标处自由选择路径
 复合体，但两者都不是中间对象，因此自由不能
 修复差异。 这个假设是不可避免的，而不仅仅是
 方便：[arrow_mul_respects_forces_UIP] 在此文件末尾显示
 证明 [arrow_mul_respects] 没有它，统一用 C 语言，需要
 每种类型的恒等证明的唯一性。 选择反模型
 因此复合材料落在一个刚性的角落：对象 [option A]，其中
 [None] 的循环空间可通过编码-解码参数证明可收缩，
 将集合自由度固定在外部物体上，而中间物体
 对象 [Some a] 保留 A 的循环。

[SpanMonoid] 的八个定律场的精确统计，已证明：两个
 单位定律是无刚性的（[arrow_mul_id_left]、[arrow_mul_id_right]）；
 [arrow_mul_respects] 和 [arrow_mul_assoc] 都使用它，后者是因为
 该记录量化了两个派生的任意证人
 可组合性方程，因此相同的中间对象差异
 那里也出现。
*)
Lemma arrow_mul_respects {C : Category} (rigid : HomRigid C)
      (g g' f f' : BundledArrow C) (p : asrc g = atgt f) (p' : asrc g' = atgt f') :
  BundledArrow_equiv g g' → BundledArrow_equiv f f' →
  BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p').
Proof.
  destruct g as [xg yg φg], g' as [xg' yg' φg'],
           f as [xf yf φf], f' as [xf' yf' φf']; simpl in *.
  intros [pg [qg Hg]] [pf [qf Hf]]; simpl in *.
  destruct pg, qg, pf, qf.
  rewrite hom_transport_refl in Hg.
  rewrite hom_transport_refl in Hf.
  unfold BundledArrow_equiv, arrow_mul; simpl.
  exists eq_refl, eq_refl.
  rewrite hom_transport_refl, Hg, Hf.
  now rewrite (rigid xf xf yf xg eq_refl eq_refl (eq_sym p) (eq_sym p') φf').
Qed.

(*
[pl] and [pr] repeat the types of [q] and [p] -- that is not redundancy but
   the reduced form of the record's [sm_assoc] hypotheses, since the boundary
   laws of [arrow_mul] hold by [eq_refl] here.  They are separate arguments
   precisely because they are separate PROOFS.

--------
[pl] 和 [pr] 重复了 [q] 和 [p] 的类型——这不是冗余，而是记录的 [sm_assoc] 假设的简化形式，因为 [arrow_mul] 的边界定律在这里通过 [eq_refl] 成立。它们是分开的论证，正因为它们是独立的证明。
*)
Lemma arrow_mul_assoc {C : Category} (rigid : HomRigid C)
      (h g f : BundledArrow C) (p : asrc h = atgt g) (q : asrc g = atgt f)
      (pl : asrc g = atgt f) (pr : asrc h = atgt g) :
  BundledArrow_equiv (arrow_mul h (arrow_mul g f q) pr)
              (arrow_mul (arrow_mul h g p) f pl).
Proof.
  destruct h as [xh yh χ], g as [xg yg γ], f as [xf yf φ]; simpl in *.
  unfold BundledArrow_equiv, arrow_mul; simpl.
  exists eq_refl, eq_refl.
  rewrite hom_transport_refl.
  rewrite (rigid xf xf yg xh eq_refl eq_refl (eq_sym pr) (eq_sym p)
                 (γ ∘ hom_transport eq_refl (eq_sym q) φ)).
  rewrite hom_transport_comp, hom_transport_refl.
  rewrite (rigid xf xf yf xg eq_refl eq_refl (eq_sym q) (eq_sym pl) φ).
  apply comp_assoc.
Qed.

Definition Category_SpanMonoid (C : Category) (rigid : HomRigid C)
  : SpanMonoid (Category_Graph C).
Proof.
  unshelve refine (Build_SpanMonoid (Category_Graph C)
                     (@arrow_unit C) _ _ (@arrow_mul C) _ _ _ _ _ _).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros g g' f f' pp pp' Hg Hf.
    exact (arrow_mul_respects rigid g g' f f' pp pp' Hg Hf).
  - intros f pp; exact (arrow_mul_id_left f pp).
  - intros f pp; exact (arrow_mul_id_right f pp).
  - intros h g f pp qq pl pr.
    exact (arrow_mul_assoc rigid h g f pp qq pl pr).
Defined.

(** ** Round trip I: starting from the monoid presentation / ** 往返 I：从幺半群表示出发 *)

Section MonoidRoundTrip.

Context {G : Graph}.
Context (M : SpanMonoid G).

Notation C' := (Category_from_SpanMonoid M).

(* Objects are literally the same type -- no comparison is needed. / 对象字面上是相同类型——不需要比较。 *)
Lemma SpanMonoid_roundtrip_obj : obj[C'] = gobj G.
Proof. reflexivity. Qed.

(*
Two homs of the constructed category are identified exactly when their
   underlying arrows are: the endpoint proofs are invisible.

--------
只有当构造范畴的两个同态的底层箭头相同时，它们才被完全认定：端点证明是不可见的。
*)
Lemma span_hom_equiv {x y : gobj G} (f g : x ~{C'}~> y) :
  sa_arr f ≈ sa_arr g → f ≈ g.
Proof. intro H; exact H. Qed.

(* The identity of the constructed category IS the unit of M ... / 构造范畴的同一性是 M 的单位 ... *)
Lemma span_id_arr (x : gobj G) : sa_arr (@id C' x) = sm_unit M x.
Proof. reflexivity. Qed.

(*
... and its composition IS the multiplication of M, along ANY proof of the
   composability equation.  This is the sense in which the category structure
   and the monoid structure are the same structure.

--------
... 它的组成就是 M 的乘积，沿着可组合性方程的任意证明进行。这就是范畴结构和幺半群结构是相同结构的意义。
*)
Lemma span_compose_arr {x y z : gobj G} (g : y ~{C'}~> z) (f : x ~{C'}~> y)
      (pf : gdom (sa_arr g) = gcod (sa_arr f)) :
  sa_arr (g ∘ f) ≈ sm_mul M (sa_arr g) (sa_arr f) pf.
Proof. apply (sm_mul_respects M); reflexivity. Qed.

(*
Now the graph round trip: bundle an arrow with the endpoints its own
   boundary maps assign to it, and unbundle by forgetting them again.

--------
现在图的往返：将箭头与它的端点及其自身边界映射所指派的点捆绑在一起，然后通过再次忘记它们来解捆绑。
*)
Definition sm_bundle (a : garr G) : garr (Category_Graph C') :=
  @Build_BundledArrow (Category_from_SpanMonoid M)
    (gdom a) (gcod a) (a; (eq_refl, eq_refl)).

Definition sm_unbundle (u : garr (Category_Graph C')) : garr G := sa_arr (aarr u).

Lemma sm_bundle_dom (a : garr G) : gdom (sm_bundle a) = gdom a.
Proof. reflexivity. Qed.

Lemma sm_bundle_cod (a : garr G) : gcod (sm_bundle a) = gcod a.
Proof. reflexivity. Qed.

Lemma sm_unbundle_dom (u : garr (Category_Graph C')) :
  gdom (sm_unbundle u) = gdom u.
Proof. exact (sa_dom (aarr u)). Qed.

Lemma sm_unbundle_cod (u : garr (Category_Graph C')) :
  gcod (sm_unbundle u) = gcod u.
Proof. exact (sa_cod (aarr u)). Qed.

(*
Transporting a hom of C' along object equalities leaves the underlying
   arrow alone -- C' stores the endpoints separately from the arrow.

--------
沿着对象等式传输 C' 的同态会保持底层箭头不变——C' 将端点与箭头分开存储。
*)
Lemma sa_arr_transport {x y x' y' : gobj G} (p : x = x') (q : y = y')
      (h : x ~{C'}~> y) :
  sa_arr (@hom_transport (Category_from_SpanMonoid M) x x' y y' p q h)
    = sa_arr h.
Proof. destruct p, q; reflexivity. Qed.

(* ONE composite of the round trip is the identity on the nose. / 一次往返的组合正好是恒等映射。 *)
Lemma sm_unbundle_bundle (a : garr G) : sm_unbundle (sm_bundle a) = a.
Proof. reflexivity. Qed.

(*
THE OTHER is the identity only up to `≈`, and that is exactly right: the
   bundled form re-derives the endpoints from [gdom] and [gcod], which agree
   with the recorded ones only propositionally.  No stronger statement holds
   here, and none is claimed.

--------
另一个恒等仅在 `≈` 范围内有效，这完全正确：捆绑的形式从 [gdom] 和 [gcod] 重新导出端点，它们仅在命题上与记录的端点一致。这里没有更强的断言，并且也没有任何这样的主张。
*)
Lemma sm_bundle_unbundle (u : garr (Category_Graph C')) :
  sm_bundle (sm_unbundle u) ≈ u.
Proof.
  destruct u as [x y h].
  exists (sa_dom h), (sa_cod h).
  apply span_hom_equiv.
  now rewrite sa_arr_transport.
Qed.

(*
Both comparisons respect `≈`.  Together with the two composites above and
   the four boundary lemmas, that makes the pair a setoid isomorphism
   commuting with [gdom] and [gcod] -- a comparison of GRAPHS, not merely a
   bijection of the underlying types.

--------
两个比较都尊重 `≈`。加上上面提到的两个复合以及四个边界引理，这使得这一对成为一个集合同构，并且与 [gdom] 和 [gcod] 交换——这是对 GRAPHS 的比较，而不仅仅是对底层类型的双射。
*)
Lemma sm_bundle_respects (a b : garr G) : a ≈ b → sm_bundle a ≈ sm_bundle b.
Proof.
  intro H.
  exists (gdom_respects H), (gcod_respects H).
  apply span_hom_equiv.
  rewrite sa_arr_transport.
  exact H.
Qed.

Lemma sm_unbundle_respects (u v : garr (Category_Graph C')) :
  u ≈ v → sm_unbundle u ≈ sm_unbundle v.
Proof.
  intros [p [q H]]; unfold sm_unbundle.
  rewrite <- (sa_arr_transport p q (aarr u)).
  exact H.
Qed.

End MonoidRoundTrip.

(*
Conjugating by identity isomorphisms does nothing.  This is the shape
   [Functor_Setoid]'s naturality condition takes when the two functors agree
   on objects definitionally, as both comparisons below do.

--------
通过恒等同构进行结合不会有任何效果。这就是当两个函子在对象上按定义相同时（如下两种比较所示），[Functor_Setoid] 的自然性条件所采取的形式。
*)
Lemma iso_id_conj {D : Category} {x y : D} (h : x ~> y) :
  from (@iso_id D y) ∘ h ∘ to (@iso_id D x) ≈ h.
Proof. simpl; now rewrite id_right, id_left. Qed.

(** ** Round trip II: starting from a [Category] / ** 往返行程 II：从 [Category] 出发 *)

Section CategoryRoundTrip.

Context (C : Category).
Context (rigid : HomRigid C).

Notation Rebuilt := (Category_from_SpanMonoid (Category_SpanMonoid C rigid)).

(* Objects are literally the same type. / 对象字面上是相同的类型。 *)
Lemma Category_roundtrip_obj : obj[Rebuilt] = obj[C].
Proof. reflexivity. Qed.

Definition rb_to {x y : C} (f : x ~> y) : x ~{Rebuilt}~> y :=
  (Build_BundledArrow x y f; (eq_refl, eq_refl)).

Definition rb_from {x y : C} (h : x ~{Rebuilt}~> y) : x ~> y :=
  @hom_transport C _ _ _ _ (sa_dom h) (sa_cod h) (aarr (sa_arr h)).

(* ONE composite is the identity on the nose. / 一个复合函数恰好是恒等函数。 *)
Lemma rb_from_to {x y : C} (f : x ~> y) : rb_from (rb_to f) = f.
Proof. reflexivity. Qed.

(* THE OTHER only up to `≈`, for the same reason as before. / 另一个只到 `≈`，原因同之前一样。 *)
Lemma rb_to_from {x y : C} (h : x ~{Rebuilt}~> y) : rb_to (rb_from h) ≈ h.
Proof.
  apply (span_hom_equiv (Category_SpanMonoid C rigid)).
  exists (eq_sym (sa_dom h)), (eq_sym (sa_cod h)).
  unfold rb_to, rb_from; simpl.
  now rewrite hom_transport_sym_inv.
Qed.

(*
The two comparisons are functors.  [Rebuild_to] is unconditional;
   [Rebuild_from] uses rigidity twice, once to see that it respects `≈` and
   once for functoriality, since it has to compare transports of one morphism
   along independently chosen object paths.

--------
这两个比较是范畴函子。[Rebuild_to] 是无条件的；[Rebuild_from] 使用了两次刚性，一次是为了查看它是否遵守 `≈`，另一次是为了函子性，因为它必须比较沿独立选择的对象路径对一个态射的传送。
*)
Definition Rebuild_to : C ⟶ Rebuilt.
Proof.
  unshelve refine (@Build_Functor C Rebuilt
                    (λ x : C, x)
                    (λ (x y : C) (f : x ~> y), rb_to f) _ _ _).
  - intros x y f g Hfg.
    apply (span_hom_equiv (Category_SpanMonoid C rigid)).
    exists eq_refl, eq_refl.
    now rewrite hom_transport_refl.
  - reflexivity.
  - reflexivity.
Defined.

Definition Rebuild_from : Rebuilt ⟶ C.
Proof.
  unshelve refine (@Build_Functor Rebuilt C
                    (λ x : Rebuilt, x)
                    (λ (x y : Rebuilt) (h : x ~{Rebuilt}~> y), rb_from h) _ _ _).
  - intros x y h h' Hh.
    destruct Hh as [pp [qq HH]].
    unfold rb_from.
    rewrite <- HH, hom_transport_trans.
    apply rigid.
  - reflexivity.
  - intros x y z h h'.
    unfold rb_from; simpl.
    apply (hom_transport_compose_compare rigid).
Defined.

(*
NOTE 4.  The round trip packages as an isomorphism in [Cat].  In this
   library that is the SAME strength as an equivalence of categories: Cat's
   hom-setoid is [Functor_Setoid], which identifies functors up to natural
   isomorphism, and Theory/Equivalence.v converts [≅[Cat]] to
   [EquivalenceOfCategories] and back.  It is nevertheless the strongest
   packaging available -- a [StrictCat] isomorphism would need funext -- and
   the genuinely extra content is in the construction: both object maps are
   the identity function on obj[C], one hom leg is the identity on the nose
   ([rb_from_to]), and the other holds per hom-setoid ([rb_to_from]).

--------
注意 4. 回程打包作为 [Cat] 中的同构。在该库中，它与范畴等价具有相同的强度：Cat 的 hom-setoid 是 [Functor_Setoid]，它将函子按自然同构进行识别，而 Theory/Equivalence.v 将 [≅[Cat] 转换为 [EquivalenceOfCategories] 并返回。然而，它仍然是可用的最强打包——一个 [StrictCat] 同构将需要 funext——真正的额外内容在于构造：两个对象映射都是 obj[C] 上的恒等函数，一个 hom 分支是完全恒等 ([rb_from_to])，另一个则在每个 hom-setoid 上成立 ([rb_to_from])。
*)
Definition Category_monoid_iso : C ≅[Cat] Rebuilt.
Proof.
  unshelve refine (@Build_Isomorphism Cat C Rebuilt Rebuild_to Rebuild_from _ _).
  - exists (λ x, iso_id).
    intros x y h.
    rewrite iso_id_conj.
    apply rb_to_from.
  - exists (λ x, iso_id).
    intros x y f.
    rewrite iso_id_conj.
    reflexivity.
Defined.

End CategoryRoundTrip.

(* ------------------------------------------------------------------------ *)
(** ** Necessity of [HomRigid]: a reverse-mathematics theorem / ** [HomRigid] 的必要性：一个反向数学定理 *)

(*
NOTE 3 explains why [arrow_mul_respects] consumes rigidity; this section
   shows the consumption is unavoidable.  If the multiplication respected
   [BundledArrow_equiv] uniformly in C WITHOUT the hypothesis, uniqueness of
   identity proofs would follow for every type.

   The countermodel is built so the composite lands in a RIGID corner.  Its
   objects are [option A]: the loop space of [None] is contractible for every
   A, by the encode-decode argument below, so the arrow equivalence has no
   freedom at the outer objects of the test composite -- while the
   intermediate object [Some a] keeps the loops of A, which is where the two
   composability proofs are allowed to differ.  (The technique follows
   Instance/Discrete/Reconstruct.v's [Discrete_DiscreteRigid_forces_UIP]; the
   extra encode-decode step is needed here precisely because this file's
   setoid gives freedom at TWO objects rather than none.)

--------
注释3解释了为什么[arrow_mul_respects]会消耗刚性；本节显示这种消耗是不可避免的。如果乘法在C中在没有假设的情况下均匀地遵守[BundledArrow_equiv]，那么每种类型的恒等证明的唯一性都将随之而来。

反例模型的构建使复合落在一个刚性角落。它的对象是[option A]：通过下面的编码-解码论证，[None]的环空间对于每个A都是可缩的，因此箭头等价在测试复合的外部对象上没有自由度——而中间对象[Some a]保留了A的环，这是允许两个可组合性证明有所不同的地方。（该技术遵循Instance/Discrete/Reconstruct.v的[Discrete_DiscreteRigid_forces_UIP]；这里需要额外的编码-解码步骤，正是因为这个文件的集合等价在两个对象上提供了自由，而不是一个都没有。）
*)

Lemma etr_assoc {X : Type} {u v w z : X} (i : u = v) (j : v = w) (k : w = z) :
  eq_trans i (eq_trans j k) = eq_trans (eq_trans i j) k.
Proof. destruct i, j, k; reflexivity. Qed.

#[local] Set Default Proof Using "All".

Section Countermodel.

(* An arbitrary type with an arbitrary point. / 一个具有任意点的任意类型。 *)
Context (A : Type) (a : A).

(*
Objects: [option A].  [None] is a RIGID point -- its loop space is
   provably contractible ([none_loop]) whatever A is -- while [Some a] is
   FLOPPY: its loops are exactly the loops of A at a.

--------
对象：[option A]。[None] 是一个刚性点——它的环空间是可证明可缩的（[none_loop]），无论 A 是什么——而 [Some a] 是松散的：它的环正好是 A 在 a 处的环。
*)
Definition ob : Type := option A.
Definition pt (x : ob) : A := match x with None => a | Some b => b end.

Definition PtCat : Category.
Proof.
  unshelve refine (Build_Category' (fun x y : ob => pt x = pt y)
                     (fun _ => eq_refl)
                     (fun x y z (g : pt y = pt z) (f : pt x = pt y) =>
                        eq_trans f g)).
  - intros x y.
    exact {| equiv := @eq (pt x = pt y); setoid_equiv := eq_equivalence |}.
  - intros x y z g g2 Hg f f2 Hf; simpl in *; now subst.
  - intros; apply eq_trans_id_r.
  - intros; apply eq_trans_id_l.
  - intros; symmetry; apply etr_assoc.
Defined.

(** The loop space of [None] is contractible, constructively, for every A. / 对于每个 A，[None] 的环空间是可缩的，并且是构造性的。 *)
Definition ocode (y : ob) : Type :=
  match y with None => unit | Some _ => Empty_set end.

Definition oenc {y : ob} (e : @eq ob None y) : ocode y :=
  match e in (_ = z) return ocode z with eq_refl => tt end.

Definition odec {y : ob} (c : ocode y) : @eq ob None y :=
  match y return ocode y -> @eq ob None y with
  | None   => fun _ => eq_refl
  | Some _ => fun c => match c with end
  end c.

Lemma odec_oenc {y : ob} (e : @eq ob None y) : odec (oenc e) = e.
Proof. destruct e; reflexivity. Qed.

Lemma none_loop (e : @eq ob None None) : e = eq_refl.
Proof. exact (eq_sym (odec_oenc e)). Qed.

(** [f_equal pt] undoes [f_equal Some]; general in both endpoints. / [f_equal pt] 撤销 [f_equal Some]；在两个端点上通用。 *)
Lemma pt_Some {u v : A} (w : u = v) : f_equal pt (f_equal (@Some A) w) = w.
Proof. destruct w; reflexivity. Qed.

Lemma pt_sym {x y : ob} (w : x = y) :
  f_equal pt (eq_sym w) = eq_sym (f_equal pt w).
Proof. destruct w; reflexivity. Qed.

(** How [hom_transport] computes in PtCat. / [hom_transport] 如何在 PtCat 中进行计算。 *)
Lemma ht_pt {x y y' : ob} (q : y = y') (h : x ~{PtCat}~> y) :
  @hom_transport PtCat x x y y' eq_refl q h = eq_trans h (f_equal pt q).
Proof. destruct q; reflexivity. Qed.

(**
The two test arrows: [fA : None -> Some a] and [gA : Some a -> None].
    Their composite lands in the RIGID corner [None -> None].

--------
两个测试箭：[fA : None -> Some a] 和 [gA : Some a -> None]。它们的复合物落在刚性角 [None -> None]。
*)
Definition fA : BundledArrow PtCat := @Build_BundledArrow PtCat None (Some a) eq_refl.
Definition gA : BundledArrow PtCat := @Build_BundledArrow PtCat (Some a) None eq_refl.

Lemma fA_self : BundledArrow_equiv fA fA.
Proof. exists eq_refl, eq_refl; reflexivity. Qed.

Lemma gA_self : BundledArrow_equiv gA gA.
Proof. exists eq_refl, eq_refl; reflexivity. Qed.

Lemma forces_loop
  (K : forall (C : Category) (g g' f f' : BundledArrow C)
              (p : asrc g = atgt f) (p' : asrc g' = atgt f'),
       BundledArrow_equiv g g' -> BundledArrow_equiv f f' ->
       BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p'))
  (e : a = a) : e = eq_refl.
Proof.
  pose (p  := f_equal (@Some A) e : @eq ob (Some a) (Some a)).
  pose (p' := eq_refl : @eq ob (Some a) (Some a)).
  specialize (K PtCat gA gA fA fA p p' gA_self fA_self).
  destruct K as [P [Q H]].
  rewrite (none_loop P), (none_loop Q) in H.
  assert (H2 :
    eq_trans (@hom_transport PtCat None None (Some a) (Some a)
                eq_refl (eq_sym p) (eq_refl : pt None = pt (Some a)))
             (eq_refl : pt (Some a) = pt None)
  = eq_trans (@hom_transport PtCat None None (Some a) (Some a)
                eq_refl (eq_sym p') (eq_refl : pt None = pt (Some a)))
             (eq_refl : pt (Some a) = pt None)) by exact H.
  rewrite !(ht_pt _ (eq_refl : pt None = pt (Some a))) in H2.
  rewrite !eq_trans_id_l, !eq_trans_id_r in H2.
  rewrite !pt_sym in H2.
  unfold p, p' in H2.
  rewrite pt_Some in H2.
  simpl in H2.
  rewrite <- (eq_sym_involutive e), H2.
  reflexivity.
Qed.

End Countermodel.

(**
* The necessity theorem.

    If the multiplication [arrow_mul] of Theory/Category/Monoid.v respected
    [BundledArrow_equiv] WITHOUT the [HomRigid] hypothesis -- i.e. if
    [arrow_mul_respects] held with its [rigid] argument dropped -- then UIP
    would hold for every type.  So the hypothesis isolated at
    [sm_mul_respects] is not an artefact of the chosen proof.

--------
* 必要性定理。

如果 Theory/Category/Monoid.v 的乘法 [arrow_mul] 在没有 [HomRigid] 假设的情况下仍然遵守 [BundledArrow_equiv]——也就是说，如果在去掉其 [rigid] 参数的情况下 [arrow_mul_respects] 成立——那么 UIP 将对每种类型成立。因此，在 [sm_mul_respects] 处隔离的假设并不是所选证明的产物。
*)
Theorem arrow_mul_respects_forces_UIP
  (K : forall (C : Category) (g g' f f' : BundledArrow C)
              (p : asrc g = atgt f) (p' : asrc g' = atgt f'),
       BundledArrow_equiv g g' -> BundledArrow_equiv f f' ->
       BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p')) :
  forall (A : Type) (a : A) (e : a = a), e = eq_refl.
Proof. intros A a e; exact (forces_loop A a K e). Qed.

(* ... and hence full UIP / HomRigid for every category. / ... 因此每个范畴都具有完全的 UIP / HomRigid。 *)
Corollary arrow_mul_respects_forces_UIP'
  (K : forall (C : Category) (g g' f f' : BundledArrow C)
              (p : asrc g = atgt f) (p' : asrc g' = atgt f'),
       BundledArrow_equiv g g' -> BundledArrow_equiv f f' ->
       BundledArrow_equiv (arrow_mul g f p) (arrow_mul g' f' p')) :
  forall (A : Type) (x y : A) (u v : x = y), u = v.
Proof.
  intros A x y u v.
  destruct u.
  symmetry; apply (arrow_mul_respects_forces_UIP K).
Qed.
