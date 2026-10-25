Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.

Generalizable All Variables.

(*
   * The arrow category C^→ (also written Arr(C), C², or [2, C]). 

   --------
   * 箭头范畴 C^→（也写作 Arr(C)、C² 或 [2, C]）。
*)

(*
 nLab: https://ncatlab.org/nlab/show/arrow+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 The arrow category of C has as objects the morphisms of C and as morphisms
 the commuting squares of C: a morphism from (f : a₀ ~> a₁) to (g : b₀ ~> b₁)
 is a pair (u : a₀ ~> b₀, v : a₁ ~> b₁) with g ∘ u ≈ v ∘ f, i.e. the square

 a₀  --u-->  b₀
 |           |
 f            g           commute, i.e.  g ∘ u ≈ v ∘ f.
 v           v
 a₁  --v-->  b₁

 It is here defined as the comma category (Id[C] ↓ Id[C]) of the identity
 functor against itself (see Construction/Comma.v); taking S = T = Id[C] in
 the comma construction collapses its objects (a, b, h : S a ~> T b) to plain
 morphisms a ~> b of C and its morphisms to commuting squares as above.

 Equivalently the arrow category is the functor category [2, C], where 2 is
 the interval (walking-arrow) category {0 → 1}; the standard notations C^→,
 Arr(C), C², and [2, C] all denote this category. The domain and codomain
 functors C^→ ⟶ C are the comma projections comma_proj1 and comma_proj2 of
 Construction/Comma.v specialized to S = T = Id[C]. 

 --------
 nLab: https://ncatlab.org/nlab/show/arrow+category 
 维基百科: https://en.wikipedia.org/wiki/Comma_category 

 类别 C 的箭头范畴的对象是 C 的态射，态射则是 C 的交换方格：从 (f : a₀ ~> a₁) 到 (g : b₀ ~> b₁) 的态射是一个对 (u : a₀ ~> b₀, v : a₁ ~> b₁)，满足 g ∘ u ≈ v ∘ f，即方格

 a₀  --u-->  b₀
 |           |
 f            g 交换，即 g ∘ u ≈ v ∘ f。
 v           v
 a₁  --v-->  b₁

 这里将其定义为身为恒等函子自身的逗号范畴 (Id [C]  ↓ Id [C] )（参见 Construction/Comma.v）；在逗号构造中取 S = T = Id [C] 会将其对象 (a, b, h : S a ~> T b) 压缩为 C 的一般态射 a ~> b，并将其态射压缩为如上所述的交换方格。等价地，箭范畴是函子范畴 [2, C] ，其中 2 是
 区间（行走箭头）类别{0 → 1};标准符号C^→，
 Arr（C）、C² 和 [2, C] 都表示该范畴。定义域与陪域
 函子 C^→ ⟶ C 是 的逗号投影comma_proj1 和 comma_proj2
 Construction/逗号.v 专门用于 S = T = ID [C]。
*)

(*
 Morphisms as objects: lifting, factorization, and the self-indexing

 nLab: https://ncatlab.org/nlab/show/weak+factorization+system
 nLab: https://ncatlab.org/nlab/show/orthogonal+factorization+system
 nLab: https://ncatlab.org/nlab/show/codomain+fibration
 nLab: https://ncatlab.org/nlab/show/display+map
 nLab: https://ncatlab.org/nlab/show/adjoint+string

 The arrow category is the device that makes the morphisms of C
 first-class: statements about maps become ordinary category theory
 inside C ⃗.  A commuting square is no longer a diagram condition but a
 single morphism; a class of maps — monomorphisms, fibrations, display
 maps — is a full subcategory; and closure of such a class under
 retracts or under limits means retracts or limits computed in the
 arrow category.  Because Cat is cartesian closed, the [2, C] reading
 of the header exhibits the arrow category as an exponential, the
 directed path object of C: functors X ⟶ Arr(Y) correspond exactly to
 natural transformations between functors X ⟶ Y (nLab, arrow
 category), just as a natural transformation F ⟹ G is a functor out
 of C × 2 restricting to F and G at the two endpoints of the walking
 arrow (Riehl, "Category Theory in Context", Dover 2016) — a homotopy
 at the level of categories.  Defining [Arrow] as the comma
 (Id[C] ↓ Id[C]) obtains all of this from the already-proven comma
 machinery: the category laws arrive as instances, and
 [comma_proj_nat] of Construction/Comma.v specializes to the generic
 arrow, the natural transformation dom ⟹ cod whose component at an
 object f of the arrow category is f itself.  The projections moreover
 flank the identity-arrow functor x ↦ id[x] in an adjoint triple
 cod ⊣ ids ⊣ dom (nLab, adjoint string).

 The classical applications run through homotopy theory.  The lifting
 problems of Quillen's model categories (Quillen, "Homotopical
 Algebra", Springer Lecture Notes in Mathematics 43, 1967) are
 commuting squares — that is, morphisms e → m of the arrow category —
 and both classes of a weak factorization system are closed under
 retracts formed there, a model structure being precisely two
 interlocking such systems (nLab, weak factorization system; model
 category).  In this library, Theory/Orthogonality.v states unique
 lifting in exactly this square form and proves the retract closure
 [ortho_left_retract].  Orthogonal factorization systems — first
 studied by Mac Lane ("Duality for groups", Bull. AMS 56, 1950),
 essentially present in Freyd and Kelly ("Categories of continuous
 functors, I", J. Pure Appl. Algebra 2, 1972), and named by Bousfield
 ("Constructions of factorization systems in categories", J. Pure
 Appl. Algebra 9, 1977) — likewise live here: the two classes are
 replete subcategories of the arrow category (nLab, orthogonal
 factorization system), and the construction itself carries the
 classifying monad, an orthogonal factorization system on K being an
 Eilenberg–Moore algebra, appropriately defined, for the monad of the
 squaring endofunctor K ↦ K² on Cat (Korostenski and Tholen, "Factorization
 systems as Eilenberg-Moore algebras", J. Pure Appl. Algebra 85,
 1993).  In-tree the systems are the class [OFS] of
 Structure/Factorization.v.

 The codomain projection opens fibred category theory.  The codomain
 functor [comma_proj2] is always a Grothendieck opfibration, and is a
 fibration exactly when C has pullbacks — the cartesian lift of a map
 is its pullback square — with the slice categories C/c as fibres
 (Construction/Slice.v), whence its names "self-indexing" and
 "fundamental fibration" (nLab, codomain fibration).  This library
 proves the fibred presentation equivalent to the present one:
 Construction/Displayed/Codomain.v renders the arrow category
 displayed over C, establishes the isomorphism
 [Codomain_Total_Arrow_iso] in Cat, and builds the cartesian lifts
 from chosen pullbacks in [codomain_cleaving].  Pullback-closed full
 subcategories of the arrow category are Taylor's classes of display
 maps, the semantic counterpart of dependent types: a display map
 p : B → A models the judgement x:A ⊢ B(x), with substitution
 interpreted as pullback, and in homotopy type theory the display
 maps are the fibrations (Taylor, "Practical Foundations of
 Mathematics", CUP 1999; nLab, display map).  The [2, C] equivalence
 of the header is proven in Theory/Shapes.v as
 [Two_Fun_Arrow : [_2, C] ≅[Cat] Arrow C], over the walking arrow [_2]
 of Instance/Two.v, for [C : Category@{o Set Set}] -- a restriction that
 side genuinely forces, since Instance/Fun.v's [Fun] identifies the hom
 universes of source and target while [_2]'s homs live in [Set].  Read its strength precisely: [≅[Cat]] here is an
 EQUIVALENCE of categories, since Instance/Cat.v identifies functors up
 to natural isomorphism.  One of the two round trips is strict --
 [Arrow_Fun_Arrow_strict] there says the composite
 Arrow C -> [_2, C] -> Arrow C is [Functor_StrictEq_Setoid]-equal to the
 identity -- while the other is witnessed by a family of natural
 isomorphisms whose components are identities, and no more; that file's
 header records exactly what would be needed for a [StrictCat]
 isomorphism, which is not claimed.  The codomain isomorphism above is
 the separate comparison with the displayed presentation.

 Mac Lane's Exercise II.4.7 — functors INTO the arrow category are
 exactly natural transformations — is Construction/Arrow/Functor.v:
 extraction [Arrow_extract] (boundary functors plus the generic arrow
 assembled into a transformation), introduction [Arrow_intro] (a
 transformation materialized as a functor, naturality supplying the
 squares), and the bijection [Arrow_classification] as a setoid
 isomorphism in Sets; unlike the [_2] comparison it carries no
 Set-level universe pin (the library's ambient h = p constraint
 from [Functor] still applies), never leaving the comma
 presentation. 

 --------
 作为对象的态射：提升、分解与自我索引

 nLab:  https://ncatlab.org/nlab/show/weak+factorization+system 
 nLab:  https://ncatlab.org/nlab/show/orthogonal+factorization+system 
 nLab:  https://ncatlab.org/nlab/show/codomain+fibration 
 nLab:  https://ncatlab.org/nlab/show/display+map 
 nLab:  https://ncatlab.org/nlab/show/adjoint+string箭头范畴是使 C 的态射成为一等公民的装置：关于映射的陈述在 C ⃗ 中变为普通的范畴论。一个交换方形不再是图表条件，而是一个单态射；一类映射——单射、纤维化、展示映射——是一个满子范畴；并且在这种类下关于重tractions 或极限的封闭意味着在箭头范畴中计算重tractions 或极限。因为 Cat 是笛卡尔闭的，所以头部的 [2, C] 读取方式显示箭头范畴作为指数，即 C 的有向路径对象：函子 X ⟶ Arr(Y) 完全对应于函子 X ⟶ Y 之间的自然变换（nLab，箭头范畴），就像自然变换 F ⟹ G 是从 C × 2 出来的函子，在 walking arrow 的两个端点处分别限制为 F 和 G（Riehl，《Category Theory in Context》，Dover 2016）——在范畴层面上的一个同伦。将 [Arrow] 定义为逗号
 (Id [C]  ↓ Id [C] ) 可以从已证明的逗号
 机制中获得所有这些：范畴律作为实例出现，并且
 Construction/Comma.v 中的 [comma_proj_nat] 特化为通用
 箭头，自然变换 dom ⟹ cod，其在箭头范畴的对象 f 处的分量是 f 本身。此外，投影还在伴随三重中环绕恒等箭头函子 x ↦ id [x]
 cod ⊣ ids ⊣ dom (nLab，伴随串)。经典应用贯穿于同伦论。Quillen 模型范畴的提升问题（Quillen，《同伦理论代数》，Springer 数学讲义 43，1967）是交换方格——即箭头范畴中的态射 e → m——并且弱分解系统的两类在其形成的收回下都是封闭的，一个模型结构恰好是两个交错的此类系统（nLab，弱分解系统；模型范畴）。在这个库中，Theory/Orthogonality.v 正是以这种方格形式陈述唯一提升，并证明了收回闭性 [ortho_left_retract]。正交分解系统——最先由 Mac Lane 研究（“群的对偶性”，Bull. AMS 56, 1950），基本存在于 Freyd 和 Kelly（“连续函子的范畴，I”，J. Pure Appl.代数 2, 1972)，并由 Bousfield 命名（“范畴中分解系统的构造”，J. Pure Appl. Algebra 9, 1977）——同样存在于这里：这两个类是箭头范畴的充足子范畴（nLab，正交分解系统），并且构造本身携带分类模范畴，一个 K 上的正交分解系统是适当地定义为 Cat 上平方自函子 K ↦ K² 的模范畴的 Eilenberg–Moore 代数（Korostenski 和 Tholen，“分解系统作为 Eilenberg-Moore 代数”，J. Pure Appl. Algebra 85, 1993）。在树中，这些系统是 Structure/Factorization.v 的类 [OFS]。余域投射开启了纤维范畴理论。余域函子 [comma_proj2] 总是一个 Grothendieck 上纤维，并且当且仅当 C 具有拉回时才是一个纤维 —— 一个映射的笛卡尔升举就是它的拉回方格 —— 其纤维为切片范畴 C/c（Construction/Slice.v），因此其名称为“自索引”和“基本纤维”（nLab，余域纤维）。本库证明了与当前表述等价的纤维表示：Construction/Displayed/Codomain.v 将箭头范畴显示在 C 上，建立 Cat 中的同构 [Codomain_Total_Arrow_iso]，并从 [codomain_cleaving] 中选定的拉回构造笛卡尔升举。箭头范畴的拉回闭合子范畴是泰勒的展示映射类，它们是依赖类型的语义对应：一个展示映射 p : B → A 对应判定 x:A ⊢ B(x)，替换被解释为拉回，在同伦类型论中，展示映射是纤维化 (Taylor, 《数学的实际基础》，CUP 1999；nLab，展示映射)。标题中的 [2, C] 等价在 Theory/Shapes.v 中被证明为 [Two_Fun_Arrow : [_2, C] ≅ [Cat] Arrow C]，在 Instance/Two.v 的 walking arrow [_2] 上，对于 [C : Category@{o Set Set}] —— 这是一个侧面真正强制的限制，因为 Instance/Fun.v 的 [Fun] 识别了源和目标的同伦宇，而 [_2] 的同伦存在于 [Set] 中。准确地阅读它的强度：[≅[Cat] ] 这里是类别的等价，因为 Instance/Cat.v 确定函子直到自然同构。两次往返中的一次是严格的 -- [Arrow_Fun_Arrow_strict] 那里说复合箭头 C -> [_2, C] -> 箭头 C 是 [Functor_StrictEq_Setoid] -等于恒等映射 -- 而另一次则由一族其分量都是恒等映射的自然同构来见证，仅此而已；该文件的头部精确记录了 [StrictCat] 同构所需的内容，但并未声称存在。上面的陪域同构是与显示的表述的独立比较。Mac Lane 的练习 II.4.7 — 进入箭头范畴的函子正好是自然变换 — 是 Construction/Arrow/Functor.v：提取 [Arrow_extract]（边界函子加上组装成变换的通用箭头）、引入 [Arrow_intro]（作为函子物化的变换，自然性提供方格），以及作为集合等价同构的 [Arrow_classification]；不同于 [_2] 的比较，它没有携带 Set 级别的宇宙标记（库的环境 h = p 约束来自 [Functor] 仍然适用），且从未离开逗号表示法。
*)

(*
   【Arrow 范畴定义展开】/ Arrow walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Arrow C = C ⃗ := (Id[C] ↓ Id[C])：对象 = C 的态射；态射 = 交换方块。
      Objects are morphisms of C; morphisms are commuting squares.
      等价说法：[2, C]（行走箭头 2 = {0 → 1} 上的函子范畴）。
      Also [2, C] / Arr(C) / C².

   2) 一行定义 / One-liner
      不重写 Category 字段，直接特化逗号：S = T = Id。
      No new fields — specialize Comma to identity functors.

   3) 用途直觉 / Why care
      「关于映射的命题」变成 C ⃗ 里的普通范畴论（提升问题、分解系统、余域纤维…）。
      Statements about maps become ordinary category theory in C ⃗.

   阅读：先懂 Comma → 本定义一行 → 想到「态射当对象」。
   Read Comma first → this alias → morphisms-as-objects.
*)

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.
