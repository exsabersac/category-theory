(* * * The covariant power-set monad on [Sets] / * * [Sets] 上的协变幂集单子 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.2, Exercise 1(a), printed p. 142
 (PDF p. 151) — maclane:VI.2:ex1
 Book: Awodey, "Category Theory", Carnegie Mellon pre-print, September
 2005, §10.2, Example 10.5, printed p. 271 (PDF p. 280) —
 awodey:10.2:example5; and §10.6, Exercise 5, printed p. 291
 (PDF p. 300) — awodey:10:ex5
 Book: Riehl, "Category Theory in Context", 2nd ed., §5.1, Example
 5.1.5(i), printed p. 185 (PDF p. 205) — riehl:5.1:example5;
 with her Corollary 4.6.3, printed p. 167
 nLab: https://ncatlab.org/nlab/show/power+set
 nLab: https://ncatlab.org/nlab/show/monad

 The covariant power set is the monad whose algebras Mac Lane's §VI.2
 Exercise 1, "Complete semi-lattices (E. Manes; thesis)", asks for.
 All three books state the same data, read here from the page images.
 Mac Lane: "Let 𝒫 be the covariant power set functor on Set so that 𝒫X
 is the set of all subsets S ⊂ X, while for each function f : X → Y,
 (𝒫f)S is the direct image of S under f.  For each set X, let
 η_X : X → 𝒫X send each x ∈ X to the one point set {x}, while
 μ_X : 𝒫𝒫X → 𝒫X sends each set of sets into its union.  (a) Prove that
 ⟨𝒫, η, μ⟩ is a monad 𝒫 on Set."  Awodey's Example 10.5 sends each
 function f to "the image mapping im(f)", with η_X(x) = {x} and
 μ_X(α) = ⋃α, and says "The reader should verify as an exercise that
 these operations are in fact natural in X, and that this defines a
 monad (𝒫, {−}, ⋃) on Sets"; his Exercise 10.6.5, "Show that (P, s, ∪)
 is a monad on Sets", is that verification, with
 ∪_X(α) = {x ∈ X | ∃_{U∈α}. x ∈ U}.  Riehl's Example 5.1.5(i), under
 "Monads also arise in nature", has the same unit and multiplication,
 and notes that naturality of the multiplication "makes use of
 Corollary 4.6.3; the direct image function, as a left adjoint,
 preserves unions".  This file is part (a); parts (b), (c) and (d),
 the algebras, are Instance/SupLat.v.

 THE FUNCTOR AND THE UNIT ARE NOT REBUILT.  Instance/Sets/Powerset.v
 (#227) already has the endofunctor [Powerset_Prop : Sets ⟶ Sets]:
 a subset of a setoid is a [Prop]-valued predicate that respects ≈
 ([Powerset_Prop_obj]), two subsets are equal when they have the same
 members, and the action is the direct image with its existential
 squashed ([Powerset_Prop_image]).  It also has Riehl's
 [Powerset_Prop_Singleton : Id ⟹ Powerset_Prop], whose component at
 X sends x to {x} = λ z, squash (x ≈ z).  Both are used verbatim, and
 η IS that transformation's component ([Powerset_Monad_ret], at
 [eq_refl]).  The proof-relevant carrier of the same file,
 [Powerset], lands one universe up and is not an endofunctor, so no
 monad is formable over it (refused, below).

 THE UNION.  ⋃ SS is the predicate λ x, ∃ S, SS S ∧ S x
 ([Powerset_union_pred]).  Both memberships are [Prop]s, so the
 existential is the standard library's [ex] and needs no squash, and
 P(P X) stays at the level of X by the impredicativity of [Prop].
 [Powerset_union] is μ_X as an arrow of [Sets], its respect for ≈
 being [Powerset_union_respects].

 THE LAWS are four pointwise lemmas: μ ∘ Pμ ≈ μ ∘ μP
 ([Powerset_union_assoc]), μ ∘ Pη ≈ id
 ([Powerset_union_image_singleton]), μ ∘ ηP ≈ id
 ([Powerset_union_singleton]) and the naturality of μ
 ([Powerset_union_natural]); the naturality of η is #227's own
 [naturality_sym] field.  [Powerset_Monad] assembles them with
 Theory/Monad.v's [Build_Monad].  The naturality of μ is proved
 directly, by opening the squashed direct image: the union of the
 images is the image of the union.  Riehl's route, through the direct
 image as a left adjoint, needs Instance/Powerset.v (#382): with it
 the dependency closure grows from this file's thirty-two files to
 eighty-nine, and to ninety with the satellite itself (the transitive
 closure of the Category.* [Require] lines, each file counted once,
 the root included), so that route is kept apart, in the satellite
 Instance/Sets/Powerset/Monad/Riehl.v.
 Awodey's remark that "monads can, and often do, arise without coming
 from evident adjunctions" is taken up in Instance/SupLat/Free.v, which
 builds the free complete-semilattice adjunction and measures how far
 its induced monad is this one.  [Powerset_Monad_statement] inhabits
 the type [Powerset_Prop_Monad_statement], which Instance/Sets/
 Powerset.v entered to show that this monad had become statable.

 STRENGTHS.  By [eq_refl]: T X is [Powerset_Prop_obj X] and T f is
 [Powerset_Prop_map f] ([Powerset_Monad_obj], [Powerset_Monad_map]),
 and T f S at y is the squashed ∃ x, S x ∧ f x ≈ y
 ([Powerset_Monad_map_at]); η_X is #227's singleton component and its
 singleton map ([Powerset_Monad_ret], [Powerset_Monad_ret_map]), η x is
 {x} and x's singleton at z is squash (x ≈ z) ([Powerset_Monad_ret_at],
 [Powerset_Monad_ret_member]); μ_X is [Powerset_union]
 ([Powerset_Monad_join]) and μ SS at x is ∃ S, SS S ∧ S x
 ([Powerset_Monad_join_at]).  At ≈ only: the three monad laws and the
 two naturality squares, which compare different predicates with the
 same members.  Refused, each pinned in Test/ProbeSupLat466.v: each of
 those five at [eq_refl], namely associativity (M3), μ ∘ Pη ≈ id (M4),
 μ ∘ ηP ≈ id (M5), the naturality of η at one point (M6), and the
 naturality of μ at one set of subsets (M1) and as a function of the
 point (M7), all conversion refusals that stand in the probe's copy of
 its dependency closure with every [Qed] turned into [Defined] but those
 the probe's header names; and the statement
 [@Monad Sets Powerset] over the proof-relevant carrier (M2, a type
 mismatch between "Sets@{o so} ⟶ Sets@{so sso}" and "Sets@{o so} ⟶
 Sets@{o so}", which Rocq 9.1 and Coq 8.20 explain as the universe
 inconsistency "Cannot enforce so = o because o < so" and Coq 8.19
 prints without that explanation).

 UNIVERSES, read off [About].  The union and the four laws bind [@{o}],
 with the one bound [Set < o], first carried by Instance/Sets/
 Powerset.v's [Powerset_Prop_truth_equiv] ([Prop : Type@{Set+1}]).
 [Powerset_Monad] and its readbacks bind [@{o so}] with a block
 identical to [Powerset_Prop]'s: [Set < o], [o < so] (first carried by
 Instance/Sets.v's [Sets]), and the caps compose and ID from
 Instance/Sets.v's [setoid_morphism_compose] and [setoid_morphism_id].
 [Powerset_Monad_statement] binds [@{u so o}], in the order of
 [Powerset_Prop_Monad_statement]'s own universes, and adds [so <= u]
 and [o <= u], the bounds of that statement's type.  There is no
 equation and no further strict bound.

 NOT DELIVERED.  The Kleisli category of this monad (the category of
 sets and relations) is not identified.  The nearest construction in
 the tree is Instance/Concrete.v's [Rel_Powerset : Rel ⟶ Sets], out of
 Instance/Rel.v's [Rel], whose objects are Coq types and whose arrows
 A ~> Ensemble B are relations: it sends X to the predicates X → Prop
 under pointwise ↔ and a relation R to its direct image
 S ↦ { y | ∃ x ∈ S, R x y }, which is μ ∘ P R, so that, written out on
 types, it is the functor from the Kleisli category of a power-set monad
 to its base; it is faithful ([Rel_Powerset_Faithful]) and makes [Rel]
 concrete, and its comment calls it the Kleisli presentation of Rel over
 the powerset monad.  It is over bare types, every predicate a subset,
 and nothing compares it with this monad, whose subsets are the
 ≈-respecting predicates on a setoid.  Neither the finite power-set
 monad nor a strength or commutativity of this one is built.  No monad
 is built over the proof-relevant carrier, where none is formable.
 That [Powerset_Prop] has no initial algebra (#750, Lambek's lemma with
 Cantor's theorem) remains open. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，Springer GTM 5，1998年，第VI.2节，练习1(a)，印刷版第142页（PDF第151页）—— maclane:VI.2:ex1
 书籍：Awodey，《范畴论》，卡内基梅隆预印本，2005年9月，第10.2节，例子10.5，印刷版第271页（PDF第280页）—— awodey:10.2:example5；以及第10.6节，练习5，印刷版第291页（PDF第300页）—— awodey:10:ex5
 书籍：Riehl，《语境中的范畴论》，第2版，第5.1节，例子5.1.5(i)，印刷版第185页（PDF第205页）—— riehl:5.1:example5；以及她的推论4.6.3，印刷版第167页
 nLab：https://ncatlab.org/nlab/show/power+set
 nLab：https://ncatlab.org/nlab/show/monad协变幂集是麦克莱恩 §VI.2 练习1“完全半格（E. Manes；论文）”所要求的代数所对应的幺半群。三本书都陈述了相同的数据，这里从页面图像中读取。麦克莱恩：“设 𝒫 为集合上的协变幂集函子，使得 𝒫X 是 X 的所有子集 S ⊂ X 的集合，而对于每一个函数 f : X → Y，(𝒫f)S 是 S 在 f 下的直像。对于每个集合 X，设 η_X : X → 𝒫X 将每个 x ∈ X 映射到单点集 {x}，而 μ_X : 𝒫𝒫X → 𝒫X 将每个集合的集合映射为其并集。”(a) 证明 ⟨𝒫, η, μ⟩ 在 Set 上是一个单子 𝒫。 Awodey 的例子 10.5 将每个函数 f 发送为“像映射 im(f)”，其中 η_X(x) = {x} 且 μ_X(α) = ⋃α，并指出“读者应作为练习验证这些操作实际上在 X 中是自然的，并且这定义了 Set 上的单子 (𝒫, {−}, ⋃)”；他的练习 10.6.5，“证明 (P, s, ∪) 在 Set 上是单子”，就是该验证，其中 ∪_X(α) = {x ∈ X | ∃_{U∈α}. x ∈ U}。Riehl 的例子 5.1.5(i)，在“Monads 也自然出现”下，有相同的单位和乘法，并指出乘法的自然性“利用了推论 4.6.3；直接像函数，作为左伴随，保持并集”。这个文件是部分 (a)；部分 (b)、(c) 和 (d)，代数，见 Instance/SupLat.v。函子和单位没有被重建。Instance/Sets/Powerset.v (#227) 已经有了自函子 [Powerset_Prop : Sets ⟶ Sets]：集合族的一个子集是一个 [Prop] 值的谓词，它遵循 ≈ ([Powerset_Prop_obj])，当两个子集拥有相同成员时，它们被认为相等，作用是带有其存在性压缩的直接像 ([Powerset_Prop_image])。它还有 Riehl 的 [Powerset_Prop_Singleton : Id ⟹ Powerset_Prop]，其在 X 上的分量将 x 映射为 {x} = λ z, squash (x ≈ z)。这两者都被逐字使用，而 η 是该转换的分量 ([Powerset_Monad_ret], 在 [eq_refl] 上)。同一文件的与证明相关的承载 [Powerset] 位于一个更高宇宙，并且不是自函子，所以无法在其上形成 monad（如下所拒）。并集。⋃ SS 是谓词 λ x，∃ S，SS S ∧ S x ([Powerset_union_pred])。两个成员都是 [Prop]，因此存在量词是标准库的 [ex]，不需要缩减，并且 P(P X) 由于 [Prop] 的不可支配性保持在 X 的层次。[Powerset_union] 是 [Sets] 的箭头上的 μ_X，它对 ≈ 的保持是 [Powerset_union_respects]。定律是四个逐点引理：μ ∘ Pμ ≈ μ ∘ μP（[Powerset_union_assoc]）、μ ∘ Pη ≈ id（[Powerset_union_image_singleton]）、μ ∘ ηP ≈ id（[Powerset_union_singleton]）以及μ的自然性（[Powerset_union_natural]）；η的自然性是#227自有的[naturality_sym]领域。[Powerset_Monad]将它们与Theory/Monad.v的[Build_Monad]组合。μ的自然性通过直接展开压缩直像直接证明：像的并是并的像。Riehl的方法，通过将直像作为左伴随，需要Instance/Powerset.v（#382）：使用它，该文件的依赖封闭从三十二个文件增长到八十九个，如果包括卫星本身则为九十（Category.* [Require]行的传递闭包，每个文件只计一次，根文件包括在内），因此这一方法被独立保留在卫星Instance/Sets/Powerset/Monad/Riehl.v中。Awodey 的评论“单子可以，并且经常在没有明显伴随的情况下产生”在 Instance/SupLat/Free.v 中被引用，该文件构建了自由完全半格伴随，并衡量其所引出的单子与该单子相差多远。[Powerset_Monad_statement] 属于类型 [Powerset_Prop_Monad_statement]，该类型在 Instance/Sets/Powerset.v 中引入，以展示该单子已经可以被陈述。优势。作者 [eq_refl] ：T X 是 [Powerset_Prop_obj X] 并且 T f 是 [Powerset_Prop_map f] （[Powerset_Monad_obj]，[Powerset_Monad_map]），并且 y 处的 T f S 是压缩的 ∃ x, S x ∧ f x ≈ y （[Powerset_Monad_map_at]）；η_X 是 #227 的单例分量及其单例映射（[Powerset_Monad_ret]，[Powerset_Monad_ret_map]），η x 是 {x}，x 在 z 处的单例是 squash (x ≈ z)（[Powerset_Monad_ret_at]，[Powerset_Monad_ret_member]）；μ_X 是 [Powerset_union] （[Powerset_Monad_join]），并且 x 处的 μ SS 是 ∃ S, SS S ∧ S x（[Powerset_Monad_join_at]）。仅在 ≈ 下：三个单子律和两个自然性方格，它们比较具有相同成员的不同谓词。被拒绝，每个都固定在 Test/ProbeSupLat466.v 中：五个中的每一个在 [eq_refl] 中，即结合律 (M3)、μ ∘ Pη ≈ id (M4)、μ ∘ ηP ≈ id (M5)、η 在某一点的自然性 (M6)，以及 μ 在一组子集（M1）和作为该点的函数 (M7) 的自然性，所有这些转换拒绝都出现在探针副本的依赖闭包中，其中每个 [Qed] 都被转换为 [Defined]，但那些是探针的头部名称；并且声明 [@Monad Sets Powerset] 在与证明相关的承载体上 (M2，一个类型不匹配，“Sets@{o so} ⟶ Sets@{so sso}” 与 “Sets@{o so} ⟶ Sets@{o so}”，Rocq 9.1 和 Coq 8.20 将其解释为宇宙不一致性“无法强制 so = o 因为 o < so”，而 Coq 8.19 打印时没有该解释)。UNIVERSES，读取 [About]。联合和四条定律绑定 [@{o}]，使用被绑定的 [Set < o]，最初由 Instance/Sets/Powerset.v 的 [Powerset_Prop_truth_equiv]（[Prop : Type@{Set+1}]）携带。[Powerset_Monad] 及其回读绑定 [@{o so}]，使用与 [Powerset_Prop] 相同的块：[Set < o]，[o < so]（最初由 Instance/Sets.v 的 [Sets] 携带），并且帽子组合和 ID 来自 Instance/Sets.v 的 [setoid_morphism_compose] 和 [setoid_morphism_id]。[Powerset_Monad_statement] 绑定 [@{u so o}]，按照 [Powerset_Prop_Monad_statement] 自身宇宙的顺序，并添加 [so <= u] 和 [o <= u]，即该语句类型的界限。没有等式，也没有进一步严格的界限。未交付。该单子（集合与关系的范畴）的 Kleisli 范畴尚未被识别。树中最近的构造是在 Instance/Concrete.v 的 [Rel_Powerset : Rel ⟶ Sets]，它来自 Instance/Rel.v 的 [Rel]，其对象是 Coq 类型，其箭头 A ~> Ensemble B 是关系：它将 X 发送到谓词 X → Prop 下的逐点 ↔，并将关系 R 发送到它的直接像 S ↦ { y | ∃ x ∈ S, R x y }，即 μ ∘ P R，从而在类型上写出，它是从幂集单子的 Kleisli 范畴到其基范畴的函子；它是忠实的（[Rel_Powerset_Faithful]）并使 [Rel] 具体化，其注释称其为 Rel 在幂集单子上的 Kleisli 表示。它作用于简单类型，每个谓词都是一个子集，
 且没有什么能与这个单子相比较，其子集是集合上≈-保持的谓词。既没有构建有限幂集单子，也没有构建这个单子的强度或交换律。在证据相关的载体上没有构建单子，因为那里无法形成单子。[Powerset_Prop] 没有初始代数（#750，Lampek 引理与 Cantor 定理）这一点仍然未知。
*)

(* ------------------------------------------------------------------------ *)
(** ** The union of a set of subsets / ** 一组子集的并集 *)

(* ⋃ SS = { x | ∃ S ∈ SS, x ∈ S }. Both memberships are [Prop]s, so the existential is the standard library's [ex] and needs no squash. / ⋃ SS = { x | ∃ S ∈ SS, x ∈ S }。两个成员都是 [Prop] s，所以存在量词是标准库的 [ex]，无需压缩。 *)
Definition Powerset_union_pred@{o} {X : SetoidObject@{o o}}
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun S : carrier (Powerset_Prop_obj@{o} X) => SS S /\ S x))
       _).
  intros x y Hxy; split; intros [S [HS Hx]]; exists S; split; try exact HS.
  - exact (proj1 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
  - exact (proj2 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
Defined.

(* The union respects the equivalence of sets of subsets. / 并集尊重子集集合的等价性。 *)
Lemma Powerset_union_respects@{o} {X : SetoidObject@{o o}}
  (SS TT : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
  (H : SS ≈ TT) :
  Powerset_union_pred@{o} SS ≈ Powerset_union_pred@{o} TT.
Proof.
  intro x; split; intros [S [HS Hx]]; exists S; split; try exact Hx.
  - exact (proj1 (H S) HS).
  - exact (proj2 (H S) HS).
Qed.

(* μ_X : P(P X) → P X as an arrow of [Sets]. / μ_X : P(P X) → P X 作为 [Sets] 的一个箭头。 *)
Definition Powerset_union@{o} {X : SetoidObject@{o o}} :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))
                         (Powerset_Prop_obj@{o} X) :=
  @Build_SetoidMorphism@{o o o}
    (carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
    (is_setoid (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
    (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
    (λ SS, Powerset_union_pred@{o} SS) (@Powerset_union_respects@{o} X).

(* ------------------------------------------------------------------------ *)
(** ** The monad laws, pointwise / ** 单子定律，逐点 *)

(* μ ∘ Pμ ≈ μ ∘ μP: the union of the unions is the union of the union. / μ ∘ Pμ ≈ μ ∘ μP：联合的联合就是联合的联合。 *)
Lemma Powerset_union_assoc@{o} {X : SetoidObject@{o o}}
  (SSS : carrier (Powerset_Prop_obj@{o}
                    (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} Powerset_union@{o} SSS)
    ≈ Powerset_union_pred@{o} (Powerset_union_pred@{o} SSS).
Proof.
  intro x; split.
  - intros [S [HS Hx]]. hnf in HS. apply HS; intros [SS [HSS HSSS]].
    destruct (proj2 (HSSS x) Hx) as [T [HT HTx]].
    exists T; split; [ exists SS; split; assumption | exact HTx ].
  - intros [S [[SS [HSS HSS']] Hx]].
    exists (Powerset_union_pred@{o} SS); split.
    + apply Powerset_squash_intro. exists SS. split; [ exact HSS | ].
      reflexivity.
    + exists S; split; assumption.
Qed.

(* μ ∘ Pη ≈ id: the union of the singletons of the members of S is S. / μ ∘ Pη ≈ id：S 的各个元素的单元素集合的并集是 S。 *)
Lemma Powerset_union_image_singleton@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o}
    (Powerset_Prop_image@{o} (@Powerset_Prop_singleton_map@{o} X) S) ≈ S.
Proof.
  intro x; split.
  - intros [T [HT Hx]]. hnf in HT. apply HT; intros [y [Hy HyT]].
    assert (Hyx : Powerset_squash@{o} (@equiv _ (is_setoid X) y x))
      by exact (proj2 (HyT x) Hx).
    apply Hyx; intro E. exact (proj1 (@proper_morphism _ _ _ _ S y x E) Hy).
  - intro Hx. exists (Powerset_Prop_singleton_pred@{o} x); split.
    + apply Powerset_squash_intro. exists x; split; [ exact Hx | ].
      reflexivity.
    + apply Powerset_squash_intro; reflexivity.
Qed.

(* μ ∘ ηP ≈ id: the union of the one-point set {S} is S. / μ ∘ ηP ≈ id：单点集 {S} 的并集是 S。 *)
Lemma Powerset_union_singleton@{o} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  Powerset_union_pred@{o} (Powerset_Prop_singleton_pred@{o} S) ≈ S.
Proof.
  intro x; split.
  - intros [T [HT Hx]]. hnf in HT. apply HT; intro E.
    exact (proj2 (E x) Hx).
  - intro Hx. exists S; split; [ apply Powerset_squash_intro | exact Hx ].
    reflexivity.
Qed.

(* Naturality of μ, proved directly: the union of the images is the image of the union. / μ 的自然性，直接证明：像的并集就是并集的像。 *)
Lemma Powerset_union_natural@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y)
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X))) :
  Powerset_union_pred@{o} (Powerset_Prop_image@{o} (Powerset_Prop_map@{o} f) SS)
    ≈ Powerset_Prop_image@{o} f (Powerset_union_pred@{o} SS).
Proof.
  intro y; split.
  - intros [T [HT Hy]]. hnf in HT. apply HT; intros [S [HS E]].
    assert (Hy' : Powerset_Prop_image@{o} f S y) by exact (proj2 (E y) Hy).
    hnf in Hy'. apply Hy'; intros [x [Hx Hfx]].
    apply Powerset_squash_intro.
    exists x; split; [ exists S; split; assumption | exact Hfx ].
  - intro H. hnf in H. apply H; intros [x [[S [HS Hx]] Hfx]].
    exists (Powerset_Prop_image@{o} f S); split.
    + apply Powerset_squash_intro. exists S; split; [ exact HS | ].
      reflexivity.
    + apply Powerset_squash_intro. exists x; split; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The monad / ** 单子 *)

Definition Powerset_Monad@{o so} : @Monad Sets@{o so} Powerset_Prop@{o so}.
Proof.
  unshelve refine
    (@Build_Monad Sets@{o so} Powerset_Prop@{o so}
       (fun X => @transform _ _ _ _ Powerset_Prop_Singleton@{o so} X)
       (fun X => @Powerset_union@{o} X) _ _ _ _ _).
  - intros X Y f.
    exact (@naturality_sym _ _ _ _ Powerset_Prop_Singleton@{o so} X Y f).
  - intros X SSS. exact (Powerset_union_assoc@{o} SSS).
  - intros X S. exact (Powerset_union_image_singleton@{o} S).
  - intros X S. exact (Powerset_union_singleton@{o} S).
  - intros X Y f SS. exact (Powerset_union_natural@{o} f SS).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

Example Powerset_Monad_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[Powerset_Prop@{o so}] X = Powerset_Prop_obj@{o} X := eq_refl.

Example Powerset_Monad_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[Powerset_Prop@{o so}] f = Powerset_Prop_map@{o} f := eq_refl.

Example Powerset_Monad_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X
    = transform[Powerset_Prop_Singleton@{o so}] X := eq_refl.

Example Powerset_Monad_ret_map@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ Powerset_Monad@{o so} X = @Powerset_Prop_singleton_map@{o} X
  := eq_refl.

Example Powerset_Monad_ret_at@{o so} (X : SetoidObject@{o o})
  (x : carrier X) :
  @ret _ _ Powerset_Monad@{o so} X x = Powerset_Prop_singleton_pred@{o} x
  := eq_refl.

Example Powerset_Monad_join@{o so} (X : SetoidObject@{o o}) :
  @join _ _ Powerset_Monad@{o so} X = @Powerset_union@{o} X := eq_refl.

Example Powerset_Monad_join_at@{o so} (X : SetoidObject@{o o})
  (SS : carrier (Powerset_Prop_obj@{o} (Powerset_Prop_obj@{o} X)))
  (x : carrier X) :
  @join _ _ Powerset_Monad@{o so} X SS x
    = ex (fun S : carrier (Powerset_Prop_obj@{o} X) => SS S /\ S x)
  := eq_refl.

Example Powerset_Monad_map_at@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_Prop_obj@{o} X))
  (y : carrier Y) :
  fmap[Powerset_Prop@{o so}] f S y
    = Powerset_squash@{o}
        (∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y) := eq_refl.

Example Powerset_Monad_ret_member@{o so} (X : SetoidObject@{o o})
  (x z : carrier X) :
  @ret _ _ Powerset_Monad@{o so} X x z
    = Powerset_squash@{o} (@equiv _ (is_setoid X) x z) := eq_refl.

(*
 The formability statement Instance/Sets/Powerset.v entered for this
 monad is now inhabited, by the monad above. 

 --------
 为该 monad 输入的可形成性声明 Instance/Sets/Powerset.v 现在已被上面的 monad 占据。
*)
Example Powerset_Monad_statement@{u so o} :
  Powerset_Prop_Monad_statement@{u so o} := Powerset_Monad@{o so}.
