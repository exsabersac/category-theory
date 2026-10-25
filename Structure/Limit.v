Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.

Generalizable All Variables.

(* * * Limit of a diagram (terminal cone) / * * 图表的极限（终端锥） *)

(*
 nLab:      https://ncatlab.org/nlab/show/limit
 Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

 Wikipedia: "Let F : J ⟶ C be a diagram of shape J in a category C. A cone
 to F is an object N of C together with a family ψX : N ⟶ F(X) of morphisms
 indexed by the objects X of J, such that for every morphism f : X ⟶ Y in J,
 we have F(f) ∘ ψX = ψY.

 "A limit of the diagram F : J ⟶ C is a cone (L, φ) to F such that for any
 other cone (N, ψ) to F there exists a unique morphism u : N ⟶ L such that
 φX ∘ u = ψX for all X in J.

 "One says that the cone (N, ψ) factors through the cone (L, φ) with the
 unique factorization u. The morphism u is sometimes called the mediating
 morphism."

 Equivalently, the limit is the terminal object of the category of cones
 over F: the universal cone through which every other cone factors uniquely
 (nLab). The cone (L, φ) is recorded here as a [Cone F] (see
 [Structure/Cone.v]); a [Limit] bundles such a terminal cone with its
 universal property. In library notation the universal property reads:

 ∀ N : Cone F, ∃! u : vertex_obj[N] ~> vertex_obj[L],
 ∀ x : J, φ_x ∘ u ≈ ψ_x,

 where φ = vertex_map[L] are the limit's legs and ψ = vertex_map[N] are the
 competing cone's legs. (The same presheaf-representability view appears in
 [Structure/UniversalProperty/Limit.v], where representing [ConePresheaf F]
 is shown equivalent to being a limit.) 

 --------
 nLab:       https://ncatlab.org/nlab/show/limit 
 维基百科:  https://en.wikipedia.org/wiki/Limit_(category_theory) 

 维基百科: "设 F : J ⟶ C 为一个在范畴 C 中形状为 J 的图。F 的一个锥是 C 的一个对象 N 以及一族由 J 的对象 X 索引的态射 ψX : N ⟶ F(X)，使得对于 J 中的每一个态射 f : X ⟶ Y，都有 F(f) ∘ ψX = ψY。

 “图 F : J ⟶ C 的极限是一个对 F 的锥 (L, φ)，使得对于任何其他对 F 的锥 (N, ψ)，存在唯一的态射 u : N ⟶ L 使得对所有 X ∈ J，φX ∘ u = ψX。

 “人们说锥 (N, ψ) 通过锥 (L, φ) 并由唯一的分解 u 因式分解。态射 u 有时称为中介态射。”等价地，极限是 F 金字塔范畴的终对象：每个其他金字塔都可以唯一地通过它分解的通用金字塔（nLab）。这里的金字塔 (L, φ) 被记录为一个 [Cone F]（见 [Structure/Cone.v]）；一个 [Limit] 将这样的终金字塔与它的通用性质打包。在库记法中，通用性质表述为：

 ∀ N : Cone F, ∃! u : vertex_obj [N]  ~> vertex_obj [L] ,
 ∀ x : J, φ_x ∘ u ≈ ψ_x,

 其中 φ = vertex_map [L] 是极限的腿，ψ = vertex_map [N] 是竞争金字塔的腿。（同样的预层可表示性观点出现在 [Structure/UniversalProperty/Limit.v]，其中表征 [ConePresheaf F] 被证明与作为极限等价。）
*)

(*
 Where limits come from, and what they are for

 nLab:  https://ncatlab.org/nlab/show/colimit
 EoM:   https://encyclopediaofmath.org/wiki/Projective_limit
 Blog:  https://bartoszmilewski.com/2015/04/15/limits-and-colimits/
 Paper: Kan, "Adjoint functors", Transactions of the American
 Mathematical Society 87(2), 1958

 The concept is younger than its examples.  Inverse and direct limits
 over directed index sets were first studied as such in the 1930s, in
 connection with topological concepts such as Čech cohomology
 (Encyclopedia of Mathematics, "Projective limit"); the p-adic integers
 arise as the inverse limit of the rings Z/pⁿZ under remainder maps,
 and profinite groups, the Galois groups of infinite extensions among
 them, are inverse limits of finite groups (Wikipedia, "Inverse limit"
 and "Profinite group").  The formulation over an arbitrary diagram
 shape is due to Daniel Kan, in Chapter II of the 1958 paper that also
 introduced adjoint functors and Kan extensions (nLab, "colimit");
 those early articles still call colimits "direct limits", the directed
 special case lending the general notion its name for a while.

 The purpose of the general definition is economy: one universal
 property covers every construction that glues a diagram along a shape.
 Varying only J recovers the terminal object (J empty,
 Structure/Limit/Terminal.v), binary and indexed products (J discrete,
 Structure/Limit/Cartesian.v and Structure/Limit/Product.v), equalizers
 (J a parallel pair — Structure/Equalizer.v defines [Equalizer] as a
 [Limit] over [Parallel]), pullbacks (J a cospan,
 Structure/Pullback/Limit.v), and the classical inverse limits above
 (J a directed poset, read contravariantly).  Whatever is proved once
 about [Limit] — uniqueness up to unique isomorphism (Limit/Unique.v),
 preservation (Limit/Preservation.v), construction from products and
 equalizers (Limit/FromProducts.v) — specializes to each at no cost.

 Two reformulations knit the concept into the rest of the theory.
 Instance/Cones/Limit.v turns the terminal-cone slogan of the header
 into a theorem, extracting a [Limit F] from a terminal object of the
 category [Cones F] ([Limit_Cones]); Structure/Limit/Kan/Extension.v
 exhibits the limit as the right Kan extension of F along the unique
 functor J ⟶ 1, the other thread of Kan's 1958 paper.  When limits of
 every shape exist, they assemble into functors right adjoint to the
 constant-diagram functors Δ (Riehl, "Category Theory in Context",
 Dover 2016, Proposition 4.6.1).

 Downstream, the file is load-bearing in two ways.  Completeness — all
 small limits, quantified in Structure/Complete.v as [Complete] — is
 the standing hypothesis of the adjoint functor theorems, and
 Construction/Comma/Limit.v with Adjunction/GAFT.v concludes Freyd's
 theorem from it (Mac Lane, "Categories for the Working Mathematician",
 Springer GTM 5 1998, Chapter V).  The preservation vocabulary of
 Structure/Limit/Preservation.v ([PreservesLimit]) supports RAPL and
 LAPC — right adjoints preserve limits, left adjoints preserve
 colimits, with no size restriction (Riehl, Theorem 4.6.2) — proved
 in-tree as Adjunction/Continuity.v's [rapl_is_alimit] and its duals.
 Together with the existence theorem — a category with products and
 equalizers has all limits (Riehl, Theorem 3.5.11, dual form; in-tree
 [Complete_from_products_equalizers]) — these carry adjunction arguments.

 The computational reading is concrete.  Products are pair types and
 the terminal object is unit (the reading Instance/Coq.v realizes); an
 equalizer carves out the subset on which two functions agree; and a
 pullback computes a most general unifier, which is how Milewski frames
 Hindley–Milner type inference (Milewski, "Limits and Colimits", 2015).
 The existence theorem is in effect a program: a limit is the part of
 the product of all F x whose components are compatible along every
 arrow of J, exactly the shape of the funext-free end of
 Instance/Sets/End.v.  The inverse-limit technique that opened the
 history returns in semantics — Scott's D∞ model of the untyped
 λ-calculus is an inverse limit of function lattices solving
 D ≅ [D → D], an equation Cantor confines to singletons in Set (Scott,
 "Continuous Lattices", Springer LNM 274 1972) — while the ω-chain
 apparatus of Construction/Chain.v and Theory/Adamek.v is the in-tree
 colimit-side counterpart, building initial algebras. 

 --------
 极限的来源及其用途

 nLab:   https://ncatlab.org/nlab/show/colimit 
 EoM:    https://encyclopediaofmath.org/wiki/Projective_limit 
 博客:   https://bartoszmilewski.com/2015/04/15/limits-and-colimits/ 
 论文: Kan, “伴随函子”, 《美国数学会会刊》 87(2), 1958这个概念比它的例子更年轻。针对有向指标集的逆极限和直接极限在上世纪30年代首次以这种形式进行研究，与拓扑学概念如Čech上同调有关（《数学百科全书》，"射影极限"）；p进整数作为环 Z/pⁿZ 在余数映射下的逆极限而出现，而 profinite 群，其中包括无限扩张的伽罗瓦群，是有限群的逆极限（维基百科，"逆极限" 和 "Profinite 群"）。任意图形形式的表述归功于 Daniel Kan，在其1958年的论文第二章中提出，该论文还引入了伴随函子和 Kan 扩张（nLab，"余极限"）；那些早期文章仍然将余极限称为"直接极限"，有向的特殊情况一度为一般概念命名。一般定义的目的是为了经济性：一个通用的性质涵盖了沿某个形状粘合图表的所有构造。仅改变 J 就可以得到终对象（J 为空，Structure/Limit/Terminal.v）、二元和指标积（J 为离散，Structure/Limit/Cartesian.v 和 Structure/Limit/Product.v）、等化器（J 为平行对 — Structure/Equalizer.v 将 [Equalizer] 定义为 [Parallel] 上的 [Limit]）、拉回（J 为共尖，Structure/Pullback/Limit.v）以及上述经典的逆极限（J 为有向偏序集，逆变阅读）。关于 [Limit] 的任何一次证明——唯一性至唯一同构（Limit/Unique.v）、保持性（Limit/Preservation.v）、通过积和等化器的构造（Limit/FromProducts.v）——都可以无代价地专门应用于每一种情况。两个重新表述将该概念融入理论的其余部分。
 Instance/Cones/Limit.v 将标题中的终端锥口号变为一个定理，从类别 [Cones F]（[Limit_Cones]）的终端对象中提取 [Limit F]；Structure/Limit/Kan/Extension.v 将极限展示为沿唯一函子 J ⟶ 1 的 F 的右 Kan 拓展，这是 Kan 1958 年论文的另一条线索。当每种形状的极限存在时，它们会组装成与常值图函子 Δ 右伴随的函子（Riehl，《Category Theory in Context》，Dover 2016，第 4.6.1 命题）。在下游，该文件在两方面起着承重作用。完整性——所有小限制，在 Structure/Complete.v 中量化为 [Complete]——是伴随函子定理的基本假设，而 Construction/Comma/Limit.v 与 Adjunction/GAFT.v 则从它推导出 Freyd 定理（Mac Lane，《工作数学家的范畴论》，Springer GTM 5 1998，第五章）。Structure/Limit/Preservation.v（[PreservesLimit]）中的保持词汇支持 RAPL 和 LAPC——右伴随保留极限，左伴随保留余极限，无大小限制（Riehl，定理 4.6.2）——在树内证明为 Adjunction/Continuity.v 的 [rapl_is_alimit] 及其对偶。连同存在定理——一个具有积和等化子的范畴具有所有极限（Riehl，第3.5.11定理，对偶形式；in-tree [Complete_from_products_equalizers]）——这些支撑了伴随论证。计算阅读是具体的。积是成对类型，终对象是单位（阅读 Instance/Coq.v 实现）；等化器刻画出两个函数一致的子集；拉回计算最一般的统一子，这是 Milewski 描述 Hindley–Milner 类型推断的方式（Milewski，《Limits and Colimits》，2015）。存在性定理实际上就是一个程序：极限是所有 F x 的积中，其分量沿 J 的每条箭头兼容的部分，正好是 Instance/Sets/End.v 中无 funext 的端的形状。开创历史的逆极限技术在语义学中重现——斯科特的无类型 λ-演算 D∞ 模型是求解 D ≅ [D → D] 的函数格的逆极限，康托在 Set 中将该方程限制在单集合上（Scott，“连续格”，Springer LNM 274，1972）——而 Construction/Chain.v 和 Theory/Adamek.v 的 ω-链工具则是树内余极限的对应部分，用于构建初始代数。
*)
(*
   【Class Limit 语法与字段展开】/ Syntax & field walkthrough

   1) Class Limit (F : J ⟶ C)：对固定图 F 打包「极限锥 + UMP」。
      Packages a limiting cone for a fixed diagram F.

   2) 数据 / Data
      - limit_cone : Cone F  —— 极限锥（顶点 + 腿族）；见 Cone.v
        / the limiting cone (apex + legs); see Cone.v

   3) 普遍性质 / UMP
      - ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone,
          ∀ x, vertex_map[limit_cone] ∘ u ≈ vertex_map[N] x
        每个竞争锥经唯一中介态射分解。
        Every competing cone factors via a unique mediator.

   4) 对偶：Colimit F := Limit (F^op)（余极限 = 对偶图的极限）。
      Dual: Colimit F := Limit (F^op).

   阅读顺序：先 Cone.v（ACone/Cone）→ Limit → 特例 Equalizer/Pullback。
   Read Cone.v first, then Limit, then special cases.
*)

Class Limit `(F : J ⟶ C) := {
  (* The limit cone (L, φ): the terminal/universal cone over F. / 极限锥 (L, φ)：F 的终端/泛锥。 *)
  limit_cone : Cone F;

  (*
 Universal property: every cone N factors through the limit cone by a
 unique mediating morphism u on apexes, satisfying φ_x ∘ u ≈ ψ_x for
 every x in J. Here [N ~> limit_cone] is, via the [vertex_obj] coercion,
 a morphism vertex_obj[N] ~> vertex_obj[limit_cone] in C. 

 --------
 通用性质：每个锥 N 都通过极限锥以一个唯一的顶点中介态射 u 因子化，对于 J 中的每个 x 都满足 φ_x ∘ u ≈ ψ_x。这里 [N ~> limit_cone] 是通过 [vertex_obj] 强制转换，在 C 中是一个态射 vertex_obj [N] ~> vertex_obj [limit_cone]。
*)
  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x : J,
    vertex_map[limit_cone] ∘ u ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x
}.

(*
 [IsALimit F c] is the same universal property as [Limit], but with the
 apex pinned to a chosen object [c : C]: it is the (proof-relevant)
 predicate "c, with its leg family, is a limit of F". This apex-fixed form
 is the one consumed by [Structure/UniversalProperty/Limit.v]. 

 --------
 [IsALimit F c] 与 [Limit] 拥有相同的通用性质，不过顶点被固定到一个选定的对象 [c : C]：它是（证明相关的）谓词“c 及其腿族是 F 的极限”。这种顶点固定的形式就是 [Structure/UniversalProperty/Limit.v] 使用的形式。
*)
Class IsALimit `(F : J ⟶ C) (c : C) := {
    (* The limit's legs over the fixed apex c (the cone (c, φ)). / 极限在固定顶点 c 上的腿（圆锥 (c, φ)）。 *)
    limit_acone : ACone c F;
    (*
 Universal property at the fixed apex: every cone N factors through c by
 a unique u : vertex_obj[N] ~> c with φ_x ∘ u ≈ ψ_x for every x. The
 first [vertex_map] is φ (from [limit_acone]); the second is ψ (from N). 

 --------
 固定顶点处的泛性质：每个锥 N 都通过一个唯一的 u : 顶点对象 [N]  ~> c 分解，使得 φ_x ∘ u ≈ ψ_x 对每个 x 都成立。第一个 [vertex_map] 是 φ（来自 [limit_acone]）；第二个是 ψ（来自 N）。
*)
    ump_limit : ∀ N : Cone F, ∃! u : N ~> c, ∀ x : J,
    vertex_map _ ∘ u ≈ vertex_map x
  }.

(*
 Setoid on the limit witnesses at a fixed apex c: two witnesses are
 identified exactly when their leg families ([limit_acone]) agree as cones
 (pointwise up to ≈, via [AConeEquiv]); the universal-property proof is
 irrelevant to this equivalence. 

 --------
 在固定顶点 c 上的极限的 Setoid：当且仅当它们的腿家族（[limit_acone]）作为圆锥（逐点通过 [AConeEquiv] 近似）一致时，两个证人被认定为相同；普适性证明与此等价性无关。
*)
Program Definition LimitSetoid `(F : J ⟶ C) (c : C) : Setoid (IsALimit F c) :=
  {| equiv := fun l1 l2 => @limit_acone _ _ _ _ l1 ≈ @limit_acone _ _ _ _ l2 |}.
Next Obligation.
  abstract(equivalence;
           specialize X with j; specialize X0 with j;
           exact (Equivalence_Transitive _ _ _ X X0)).
Defined.

Coercion limit_cone : Limit >-> Cone.

Require Import Category.Functor.Opposite.

(*
 The colimit of F is the dual notion: a limit of the opposite diagram
 F^op, i.e. the universal cocone / initial object of the category of
 cocones over F (nLab, Wikipedia). 

 --------
 F 的余极限是对偶概念：即对偶图 F^op 的极限，也就是 F 上的余锥范畴中的普遍余锥 / 初始对象（nLab, Wikipedia）。
*)
Definition Colimit `(F : J ⟶ C) := Limit (F^op).
