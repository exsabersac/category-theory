Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Structure.Thin.

Generalizable All Variables.

(* * * Monads and comonads in a thin category / * * 稀薄范畴中的单子与余单子 *)

(*
 nLab: https://ncatlab.org/nlab/show/closure+operator
 nLab: https://ncatlab.org/nlab/show/idempotent+monad
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, SS VI.1, printed p. 139
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 SS 10.2, Example 10.4, printed p. 270
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 SS 1.4.4, Example 1.122, printed p. 34
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
 Example 5.1.7, printed p. 186

 Mac Lane asks on p. 139 "What is a monad in a preorder P?", and answers
 that the unit and multiplication exist "precisely when x ≤ Tx,
 T(Tx) ≤ Tx" (his display (3)), "the diagrams (2) then necessarily
 commute because in a preorder there is at most one arrow from here to
 yonder".  The argument uses nothing about a preorder beyond that last
 clause, so this file states it for ANY thin category in the sense of
 Structure/Thin.v's [Thin]: [thin_monad] builds a monad from an
 endofunctor and the two arrow families alone, and each of the five
 monad laws is one appeal to thinness.

 Mac Lane goes on: "The first equation of (3) gives Tx ≤ T(Tx)", the
 unit at Tx, and in a partial order he concludes T(Tx) = Tx.  Awodey's
 Example 10.4 (p. 270) makes the same step for a poset: "A monad on P is
 a monotone function T : P → P with x ≤ Tx and T²x ≤ Tx.  But then
 T² = T, i.e. T is idempotent."  Without antisymmetry the conclusion is
 an isomorphism, and that is [thin_join_IsIso]: the inverse of join at
 x is ret at M x, and both inverse laws are thinness.  Packaged,
 [thin_IdempotentMonad] says that EVERY monad on a thin category is an
 [IdempotentMonad] in the sense of Construction/Reflective/Idempotent.v.
 That file takes the class as a hypothesis; here it is derived, and the
 derivation is one of the two pieces of #463 with no earlier in-tree
 counterpart (the other is Construction/Reflective/Idempotent/Induced.v,
 the monad induced by the idempotent reflection being the original
 one).  [thin_talgebra_iff] is Mac Lane's reading of the algebras
 on p. 141, "a T-algebra is then an x ∈ P with Tx ≤ x": an algebra in a
 thin category is exactly an arrow T x ~> x.

 THE DUALS, BY DUALITY.  Riehl's Example 5.1.7 (p. 186) adds: "Dually,
 a comonad on a poset category (P, ≤) defines a kernel operator: an
 order-preserving function K so that Kp ≤ p and Kp = K²p."  Nothing on
 the comonad side is proved again.  Theory/Monad.v defines [Comonad] as
 [@Monad (C^op) (W^op)] and Construction/Opposite.v sets hom[C^op] x y
 to hom[C] y x, so each dual below is the monad-side constant at C^op,
 fed Structure/Thin.v's [Thin_Opposite]:
 - [thin_comonad] is [thin_monad] at C^op, typed by conversion;
 - [thin_IdempotentComonad] is [thin_IdempotentMonad] at C^op, and
 lands in Construction/Reflective/FixedPoints.v's
 [IdempotentComonad];
 - [thin_wcoalgebra_iff] is [thin_talgebra_iff] at C^op, read through
 Comonad/Coalgebra.v's bridges [WCoalgebra_to_TAlgebra] and
 [TAlgebra_to_WCoalgebra];
 - [thin_coreflective] is FixedPoints.v's [Idempotent_Coreflective] at
 the thin witness: the coreflection onto the objects where the
 counit is invertible, the dual of Seven Sketches Example 1.122's
 adjunction between a closure operator and the inclusion of its
 fixed points.
 The order-theoretic consumers are Instance/Proset/Monad.v, where a
 monad on a preorder is shown to be a closure operator,
 Instance/Props/Modal.v, the modal operator B ⇒ − on propositions, and,
 for the duals, Instance/Proset/Monad/Interior.v, where a comonad on a
 preorder is shown to be an interior operator, with its instance at the
 subsets of a space in Instance/Top/Interior.v.

 STRENGTHS.  [thin_monad]'s ret and join are the given families by
 [eq_refl] ([thin_monad_ret], [thin_monad_join]), and so are the
 extract and duplicate of [thin_comonad] ([thin_comonad_extract],
 [thin_comonad_duplicate]): the comonad is the monad at C^op on the
 nose, with no transport.  The algebra and coalgebra structure maps
 round-trip by [eq_refl] ([thin_talgebra_round],
 [thin_wcoalgebra_round]).  What is NOT on the nose is the comparison
 of [thin_monad] with a monad [MM] that has the same ret and join:
 [thin_monad TC T ret join = MM] is refused by conversion, because the
 law fields of a variable monad are stuck projections while those of
 [thin_monad] are appeals to [TC].  Any two such monads agree
 componentwise, at the hom-setoid's ≈, which in a thin category is the
 only comparison there is.

 UNIVERSES, read off [About].  Every constant binds [@{t o h}] with
 [C : Category@{o h h}]; hom and proof are identified because
 Structure/Thin.v's [Thin@{t o h}] accepts only [Category@{o h h}], and
 the block [o <= t, h <= t] is [Thin]'s own.  [thin_coreflective] adds
 two levels [s f] with the strict bound [h < s].  [Coreflective] reaches
 two donors that introduce such a bound in their own blocks, and neither
 file requires the other: Construction/Subcategory.v's [Sub], the
 codomain of [Reflective]'s reflector, and Instance/Sets.v's [Sets]
 ([o < so]), where the hom-setoid isomorphism of [Adjunction] lives.
 The two are unified into [s].  The same two donors bring the stdlib
 caps [h <= compose.u0, compose.u1, compose.u2, ID.u0] (first carried
 by [Sets], whose own block has them at its level o) and
 [o <= Projections.u0, h <= Projections.u0, h <= Projections.u1]
 (from [Sub] and [Incl]).  The level [f] is [Coreflective]'s own u3,
 which occurs in neither the type nor the constraint block of
 Construction/Reflective.v's [Coreflective] (measured by [About]); it
 is named here so that it is not a level of the body alone.
 [thin_wcoalgebra_iff] destructures
 the pair of [thin_talgebra_iff] with [let] instead of applying [fst]
 and [snd]: the projections add the stdlib caps
 [h <= projections.u0, h <= projections.u1] (measured), and
 destructuring adds nothing.  No constant carries [Set].  [Thin] is
 declared twice in the tree (here in Structure/Thin.v, and again in
 Instance/Proset/Galois.v); this file imports only the first.

 NOT DELIVERED.  No thin-category statement for a category whose hom
 and proof universes differ, since [Thin] cannot express one.  No
 monad-side [thin_reflective]: it would be [Idempotent_Reflective] at
 [thin_IdempotentMonad], and the one consumer, Instance/Proset/Monad.v,
 uses the reflection adjunction [idem_reflective_adj] directly.  No
 lemma that a monad on a thin category is determined by its functor,
 although it is true at ≈ by the argument above. 

 --------
 nLab：https://ncatlab.org/nlab/show/closure+operator
 nLab：https://ncatlab.org/nlab/show/idempotent+monad
 书籍：Mac Lane，《为工作中的数学家而写的范畴论》，第2版，Springer GTM 5, 1998, 第VI.1节, 印刷第139页
 书籍：Awodey，《范畴论》（第1版，CMU预印本，2005年9月），第10.2节，例10.4，印刷第270页
 书籍：Fong和Spivak，《组合性中的七个草图》，arXiv v3，第1.4.4节，例1.122，印刷第34页
 书籍：Riehl，《上下文中的范畴论》，第2版，第5.1节，例5.1.7，印刷第186页Mac Lane 在第 139 页问道：“在一个预序 P 中，什么是单子？”，并回答说，当且仅当 x ≤ Tx, T(Tx) ≤ Tx（他的公式 (3)）时，单位和乘法才存在，“图 (2) 随之必然交换，因为在预序中，从这里到那里的箭头最多只有一个”。该论证除了最后一句话之外，并未使用关于预序的其他内容，因此本文件将其陈述为适用于任何细类（thin category），在 Structure/Thin.v 中的 [Thin]：[thin_monad] 仅通过一个自函子和两个箭头族构建单子，并且五条单子定律中的每一条都仅依赖于细性（thinness）。Mac Lane 继续说道：“(3) 的第一个方程给出了 Tx ≤ T(Tx)”，即 Tx 处的单位，并且在偏序中他得出结论 T(Tx) = Tx。Awodey 的例子 10.4（第 270 页）对偏序集合做了同样的处理：“P 上的一个单子是一个单调函数 T : P → P，满足 x ≤ Tx 且 T²x ≤ Tx。但随后 T² = T，即 T 是幂等的。” 如果没有反对称性，结论是一个同构，即 [thin_join_IsIso]：在 x 处的 join 的逆是 M x 处的 ret，并且两个逆定律都是薄性。归纳起来，[thin_IdempotentMonad] 表示每一个薄范畴上的单子在 Construction/Reflective/Idempotent.v 的意义下都是一个 [IdempotentMonad]。该文件将类作为一个假设；在这里它被导出，而这个导出是 #463 的两个部分之一，在此之前的树中没有对应的部分（另一个是 Construction/Reflective/Idempotent/Induced.v，由幂等反射引出的单子是原始单子）。[thin_talgebra_iff] 是 Mac Lane 对第 141 页代数的解读，“一个 T-代数就是一个 x ∈ P，满足 Tx ≤ x”：在瘦范畴中，一个代数恰好是一个箭头 T x ~> x。对偶，通过对偶。Riehl 的例子 5.1.7（第 186 页）补充道：“对偶地，偏序集范畴 (P, ≤) 上的余单子定义了一个核算子：一个保持序的函数 K，使得 Kp ≤ p 且 Kp = K²p。”关于余单子方面没有再做证明。Theory/Monad.v 将 [Comonad] 定义为 [@Monad (C^op) (W^op)]，而 Construction/Opposite.v 将 hom [C^op] x y 设置为 hom [C] y x，因此下面的每个对偶都是 C^op 上的单子端常量，输入 Structure/Thin.v 的 [Thin_Opposite]：
 - [thin_comonad] 是 C^op 上的 [thin_monad]，由转换类型化；
 - [thin_IdempotentComonad] 是 C^op 上的 [thin_IdempotentMonad]，并且落在 Construction/Reflective/FixedPoints.v 的 [IdempotentComonad] 中；
 - [thin_wcoalgebra_iff] 是 C^op 上的 [thin_talgebra_iff]，通过 Comonad/Coalgebra.v 的桥 [WCoalgebra_to_TAlgebra] 和 [TAlgebra_to_WCoalgebra] 读取；
 - [thin_coreflective] 是 FixedPoints.v 中的 [Idempotent_Coreflective]，在薄见证上：即对那些余单位可逆的对象的余反射，这对应于 Seven Sketches 示例 1.122 中闭包算子与其固定点包含之间的伴随的对偶。序理论的使用者是 Instance/Proset/Monad.v，其中预序上的单子被证明是闭包算子，Instance/Props/Modal.v 上的模态算子 B ⇒ − 作用于命题上；对于对偶，Instance/Proset/Monad/Interior.v 中的余单子被证明是一个内部算子，其在空间的子集上的实例在 Instance/Top/Interior.v 中。优势。[thin_monad] 的 ret 和 join 是由 [eq_refl]（[thin_monad_ret]，[thin_monad_join]）给出的族，并且 [thin_comonad]（[thin_comonad_extract]，[thin_comonad_duplicate]）的 extract 和 duplicate 也是如此：comonad 在 C^op 上就是 monad，完全一致，没有传输。代数和余代数结构映射通过 [eq_refl]（[thin_talgebra_round]，[thin_wcoalgebra_round]）可以来回转换。不同之处在于 [thin_monad] 与拥有相同 ret 和 join 的 monad [MM] 的比较：[thin_monad TC T ret join = MM] 被转换拒绝，因为可变 monad 的律域是固定投影，而 [thin_monad] 的律域是引用 [TC]。任何两个这样的 monad 在组件上都是一致的，在 hom-集同伦 ≈ 上，在薄范畴中，这是唯一的比较方式。宇宙，读出 [About]。每个常数将 [@{t o h}] 与 [C : Category@{o h h}] 绑定；hom 和 proof 被识别，因为 Structure/Thin.v 的 [Thin@{t o h}] 只接受 [Category@{o h h}]，并且块 [o <= t, h <= t] 是 [Thin] 自己的。[thin_coreflective] 添加了两个层级 [s f]，并严格绑定 [h < s]。[Coreflective] 达到两个在其自身块中引入此类绑定的捐献者，而且两个文件都不依赖对方：Construction/Subcategory.v 的 [Sub]，[Reflective] 反射器的余域，以及 Instance/Sets.v 的 [Sets]（[o < so]），其中 [Adjunction] 的 hom-集合同构存在。这两者被统一为 [s]。相同的两个捐献者带来了 stdlib caps [h <= compose.u0, compose.u1, compose.u2, ID.u0]（首先由 [Sets] 携带，其自身块在其级别 o 上有它们）和 [o <= Projections.u0, h <= Projections.u0, h <= Projections.u1]（来自 [Sub] 和 [Incl]）。级别 [f] 是 [Coreflective] 自己的 u3，它既不出现在 Construction/Reflective.v 的类型块，也不出现在约束块中的 [Coreflective]（由 [About] 测量）；这里命名它以使其不仅是主体的一个级别。[thin_wcoalgebra_iff] 用 [let] 解构 [thin_talgebra_iff] 的对，而不是应用 [fst] 和 [snd]：投影添加了 stdlib 上限 [h <= projections.u0, h <= projections.u1]（已测量），解构没有添加任何内容。没有常量携带 [Set]。[Thin] 在树中声明了两次（这里在 Structure/Thin.v 中，以及在 Instance/Proset/Galois.v 中再次声明）；此文件仅导入第一次声明。未交付。对于同构和证明宇宙不同的类别，没有薄类别的陈述，因为 [Thin] 无法表达它。没有单子侧的 [thin_reflective]：它将在 [thin_IdempotentMonad] 处是 [Idempotent_Reflective]，并且唯一的使用者 Instance/Proset/Monad.v 直接使用反射伴随 [idem_reflective_adj]。没有关于薄类别上的单子可以由其函子唯一确定的引理，尽管根据上述论证，它在 ≈ 上成立。
*)

(** ** Monads in a thin category / ** 薄范畴中的单子 *)

(*
 Mac Lane's display (3) in any thin category: an endofunctor with a
 unit family and a multiplication family IS a monad.  Each law is an
 equation between parallel arrows, hence one appeal to [TC]. 

 --------
 在任何纤维范畴中的 Mac Lane 展示 (3)：一个带有单位族和乘法族的自函子就是一个单子。每条定律都是平行箭头之间的一个方程，因此只需求助于 [TC]。
*)
Definition thin_monad@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x) :
  @Monad C T :=
  @Build_Monad C T u m
    (fun _ _ _ => TC _ _ _ _) (fun _ => TC _ _ _ _) (fun _ => TC _ _ _ _)
    (fun _ => TC _ _ _ _) (fun _ _ _ => TC _ _ _ _).

(* The unit and multiplication are the given families, on the nose. / 单位和乘法是给定的族，正好如此。 *)
Example thin_monad_ret@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x)
  (x : C) : @ret C T (thin_monad TC T u m) x = u x := eq_refl.

Example thin_monad_join@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (T : C ⟶ C) (u : ∀ x : C, x ~> T x) (m : ∀ x : C, T (T x) ~> T x)
  (x : C) : @join C T (thin_monad TC T u m) x = m x := eq_refl.

(*
 Mac Lane p. 141: an algebra is exactly its structure map T x ~> x;
 both algebra laws are thinness. 

 --------
 Mac Lane 第141页：一个代数恰好就是它的结构映射 T x ~> x；两个代数定律都是稀薄性。
*)
Definition thin_talgebra_iff@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {T : C ⟶ C} {MM : @Monad C T} (x : C) :
  @TAlgebra C T MM x ↔ (T x ~> x) :=
  (fun a => @t_alg C T MM x a,
   fun h => @Build_TAlgebra C T MM x h (TC _ _ _ _) (TC _ _ _ _)).

Example thin_talgebra_round@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {T : C ⟶ C} {MM : @Monad C T} (x : C)
  (h : T x ~> x) :
  match thin_talgebra_iff TC (MM := MM) x with
  | (to_arrow, of_arrow) => to_arrow (of_arrow h)
  end = h := eq_refl.

(* Idempotency from thinness. The inverse of join at x is ret at M x (Mac Lane's "Tx ≤ T(Tx)"), and both composites are endomorphisms, hence identities. / 由单薄性得幂等性。在 x 处的连接的逆是 M x 处的重投（Mac Lane 的“Tx ≤ T(Tx)”），且两个复合都是自同态，因此是恒等映射。 *)
Definition thin_join_IsIso@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {M : C ⟶ C} {MM : @Monad C M} (x : C) :
  IsIsomorphism (@join C M MM x) :=
  {| two_sided_inverse := @ret C M MM (M x)
   ; is_right_inverse  := TC _ _ _ _
   ; is_left_inverse   := TC _ _ _ _ |}.

Definition thin_IdempotentMonad@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {M : C ⟶ C} {MM : @Monad C M} :
  @IdempotentMonad C M MM :=
  {| idem_join_iso := thin_join_IsIso TC |}.

(* * ** The duals, as the monad constants at C^op / * ** 作为 C^op 处的单子常数的对偶 *)

(* The interior data: a counit W x ~> x and a comultiplication W x ~> W (W x). At C^op these ARE the unit and multiplication families, by conversion. / 内部数据：一个余单位 W x ~> x 和一个余乘法 W x ~> W (W x)。在 C^op 上，这些通过转换就是单位和乘法家族。 *)
Definition thin_comonad@{t o h} {C : Category@{o h h}} (TC : Thin@{t o h} C)
  (W : C ⟶ C) (e : ∀ x : C, W x ~> x) (d : ∀ x : C, W x ~> W (W x)) :
  @Comonad C W :=
  thin_monad (Thin_Opposite TC) (W^op) e d.

(* The comonad is the monad at C^op on the nose. / 余单子在 C^op 上就是单子本身。 *)
Example thin_comonad_extract@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) (W : C ⟶ C) (e : ∀ x : C, W x ~> x)
  (d : ∀ x : C, W x ~> W (W x)) (x : C) :
  @extract C W (thin_comonad TC W e d) x = e x := eq_refl.

Example thin_comonad_duplicate@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) (W : C ⟶ C) (e : ∀ x : C, W x ~> x)
  (d : ∀ x : C, W x ~> W (W x)) (x : C) :
  @duplicate C W (thin_comonad TC W e d) x = d x := eq_refl.

(*
 Every comonad on a thin category is idempotent: the monad-side
 constant at C^op. 

 --------
 每个薄范畴上的余单子都是幂等的：在 C^op 上的单子侧常数。
*)
Definition thin_IdempotentComonad@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} :
  IdempotentComonad W H :=
  @thin_IdempotentMonad (C^op) (Thin_Opposite TC) (W^op) H.

(*
 A coalgebra is exactly an arrow x ~> W x: [thin_talgebra_iff] at C^op,
 read through the bridges of Comonad/Coalgebra.v. 

 --------
 余代数恰好是一个箭头 x ~> W x:  [thin_talgebra_iff] 在 C^op 中，通过 Comonad/Coalgebra.v 的桥梁来阅读。
*)
Definition thin_wcoalgebra_iff@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} (x : C) :
  @WCoalgebra C W H x ↔ (x ~> W x) :=
  let (to_arrow, of_arrow) :=
    thin_talgebra_iff (Thin_Opposite TC) (MM := H) x in
  (fun c => to_arrow (WCoalgebra_to_TAlgebra c),
   fun h => TAlgebra_to_WCoalgebra (of_arrow h)).

Example thin_wcoalgebra_round@{t o h} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} (x : C)
  (h : x ~> W x) :
  match thin_wcoalgebra_iff TC (H := H) x with
  | (to_arrow, of_arrow) => to_arrow (of_arrow h)
  end = h := eq_refl.

(*
 The inclusion of the counit-fixed objects is coreflective: the dual
 of the reflection onto the closed elements. 

 --------
 包含余单位固定对象是共反射的：是对闭元素的反射的对偶。
*)
Definition thin_coreflective@{t o h s f | h < s +} {C : Category@{o h h}}
  (TC : Thin@{t o h} C) {W : C ⟶ C} {H : @Comonad C W} :
  Coreflective@{t t s t f h o h} (WLocal_Subcategory H) :=
  Idempotent_Coreflective H (thin_IdempotentComonad TC).
