Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(*
   * * The comma diagram over the arrow category, and its universal property 

   --------
   * * 箭头范畴上的逗号图及其泛性质
*)

(*
 Reference: Saunders Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., §II.6, pp. 47-48: the projections and the diagram of
 displays (5) and (6) [maclane:II.6:construction1], their
 arrow-level definitions [maclane:II.6:ex3], and the universal
 property [maclane:II.6:ex5].  Every statement summary below is
 the catalog's paraphrase (doc/plan/books/maclane/inventory/
 II.json), not the book's own wording.
 nLab:      https://ncatlab.org/nlab/show/comma+category
 nLab:      https://ncatlab.org/nlab/show/arrow+category
 nLab:      https://ncatlab.org/nlab/show/comma+object
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 In the catalog's paraphrase of [maclane:II.6:construction1], the comma
 category carries projection functors to the two domains -- on objects
 <e, d, f> giving e and d -- together with a functor to C^2 giving the
 arrow f itself, all fitting into a commutative diagram over the row

 E --T--> C <--∂0-- C^2 --∂1--> C <--S-- D

 where ∂0 and ∂1, induced by the two functors 1 ⟶ 2, send each arrow of C
 to its domain and to its codomain.  Exercise 3 asks for the three functors
 on arrows; Exercise 5 asks that any category X with functors making the
 same diagram commute factor uniquely through the comma category, which is
 what exhibits it as a “pullback”-style limit.

 ** Dictionary

 Mac Lane writes (T ↓ S) for T : E ⟶ C and S : D ⟶ C; this tree writes
 (S ↓ T) for S : A ⟶ C and T : B ⟶ C (Construction/Comma.v).  The letters
 are interchanged and nothing else differs:

 Mac Lane      here                            defined in
 ----------------------------------------------------------------------
 T : E ⟶ C     S : A ⟶ C
 S : D ⟶ C     T : B ⟶ C
 P             [comma_proj1]                   Construction/Comma.v
 Q             [comma_proj2]                   Construction/Comma.v
 R             [Comma_to_Arrow]                this file
 C^2           [Arrow C] = (Id[C] ↓ Id[C])     Construction/Arrow.v
 C^{d0}        [Arrow_dom]                     this file
 C^{d1}        [Arrow_cod]                     this file

 [Arrow_dom] and [Arrow_cod] are not wrappers: they are [comma_proj1] and
 [comma_proj2] instantiated at S = T = Id[C], and the two [Example]s below
 pin that by [eq_refl].  Exercise 3 is answered the same way: on a
 commuting square, each of P, Q, ∂0 and ∂1 returns the relevant leg and R
 returns the pair of S- and T-images of the two legs, all definitionally,
 so the arrow-level definitions are [eq_refl] readings rather than proofs
 ([comma_proj1_fmap], [comma_proj2_fmap], [Arrow_dom_fmap],
 [Arrow_cod_fmap], [Comma_to_Arrow_dom_leg], [Comma_to_Arrow_cod_leg]).

 ** What the diagram equations cost

 Both squares of display (5) commute at STRICT strength, at
 [Functor_StrictEq_Setoid] -- equal object maps with [fmap] agreeing after
 transport -- and with the object component [fun _ => eq_refl], i.e. the
 two composites have literally the same object map:
 [comma_diagram_dom] and [comma_diagram_cod].  This is the strongest form
 available: Leibniz equality of the functor RECORDS is not provable, the
 [fmap_respects]/[fmap_id]/[fmap_comp] fields being proof terms built
 differently on the two sides.  The [≈[Cat]] readings
 [comma_diagram_dom_Cat]/[comma_diagram_cod_Cat] are strictly weaker
 corollaries obtained through [strict_equiv_implies_fun_equiv]
 (Instance/StrictCat/ToCat.v); recall that [≈[Cat]] identifies functors
 only up to natural isomorphism (Instance/Cat.v).

 ** Exercise 5, and where proof relevance bites

 The hypotheses on a competitor (X, P', Q', R') are taken STRICT, as
 Mac Lane's diagram is: the two composites agree at
 [Functor_StrictEq_Setoid].  The mediator [comma_mediator] then sends x to
 the comma object (P' x, Q' x) whose mediating arrow is that of R' x
 transported along the two object equalities the hypotheses supply, and the
 three factorizations hold at strict strength:
 [comma_mediator_proj1] and [comma_mediator_proj2] with object component
 [eq_refl], and [comma_mediator_arrow] with object component built from the
 hypotheses' own object equalities.  Its morphism half spends exactly the
 hypotheses' arrow components and nothing else.  So EXISTENCE is on the
 nose in Mac Lane's sense.

 UNIQUENESS is where a proof-relevant setting differs from the book's, and
 the difference is not an artifact of the formalization.  The three
 equations are INDEPENDENT data.  From [Comma_to_Arrow ◯ L' ≈ R'] one
 recovers only [S (fst ``(L' x)) = fst ``(R' x)], an equation in C; since S
 need not be injective on objects, no equation in A follows, so
 [comma_proj1 ◯ L' ≈ P'] is genuinely additional information, and
 symmetrically for B.  A competitor therefore arrives carrying two
 INDEPENDENT proofs of one and the same object equation
 [S (fst ``(L' x)) = S (P' x)] -- one obtained by [f_equal S] from the
 first equation, one by composing the third with the hypothesis on R'.
 Identifying them is uniqueness of identity proofs on the objects of C, and
 identifying the morphisms they induce is that same principle again.  In
 Mac Lane's set-based reading the question does not arise, equality of
 objects being proof-irrelevant there.

 Rather than assume UIP, [MediatesDiagram] states the third equation
 RELATIVE to the first two: the mediating arrow of L x, transported to
 S (P' x) ~> T (Q' x) along the object equalities the first two equations
 supply, agrees up to [≈] with the one R' supplies.  That is the [≈]-level
 content of “R' = R ◯ L'” with only one family of object proofs in play; it
 is satisfied on the nose by the mediator built here
 ([comma_mediator_mediates], whose third clause is [reflexivity]); and from
 it uniqueness follows at [≈[Cat]] ([comma_mediator_unique]), the natural
 isomorphism having the object-equality casts as its components.  The two
 halves are packaged as [comma_diagram_ump].

 Three things are therefore NOT delivered, and are named rather than left
 to inference.  First, strict uniqueness -- “L' x = L x as objects of
 S ↓ T” -- which beyond the proof reconciliation above would demand Leibniz
 equality of two mediating MORPHISMS, since a comma object carries its
 morphism as data and a setoid library supplies only [≈] between morphisms.
 Second, the PSEUDO version, in which the hypotheses commute only up to
 natural isomorphism: that is the comma OBJECT in the 2-categorical sense,
 which Construction/Comma.v already records as documentation-level
 only -- comma objects are PIE-limits, constructible from pullbacks and the
 power C^2 (nLab, “comma object”) -- and Mac Lane's Exercise 5 is the
 strict statement, which is what is proven here.  Third, and a consequence
 of the first: the uniqueness clause quantifies over [MediatesDiagram]
 competitors, a class INCOMPARABLE with Mac Lane's literal one -- weaker on
 the mediating morphism ([≈] where an equality of Arrow-objects would
 demand Leibniz) and stated relative to the competitor's own k1/k2 proof
 families -- so his uniqueness statement is rendered, not subsumed.

 [comma_diagram_self] and [comma_diagram_self_via_ump] close the loop and
 keep BOTH halves of the universal property from being vacuous: the comma
 category's own diagram is a competitor -- its hypotheses are literally
 [comma_diagram_dom] and [comma_diagram_cod] -- the mediator produced there
 is [≈[Cat]] the identity (and strictly so, [comma_diagram_self_strict]),
 and the identity itself satisfies [MediatesDiagram] by three
 reflexivities ([comma_id_mediates]), so the UNIQUENESS theorem is
 exercised at the one competitor whose answer is forced.

 ** Reuse, and two small kits

 [comma_proj_nat] (Construction/Comma.v) is Mac Lane's R in
 transformation form, and this file relates itself to it rather than
 duplicating it.  It cannot simply be plugged in: its component is a
 [Program] obligation that MATCHES on the comma object, and neither [sigT]
 nor [prod] carries definitional eta in this development, so
 [comma_proj_nat x] is not convertible with [`2 x].  [Comma_to_Arrow] takes
 [`2 x] directly -- which is what keeps the diagram equations definitional
 -- and the agreement is recorded as [Comma_to_Arrow_is_proj_nat], a
 Leibniz equality proved by one [destruct].  The commuting square that
 makes [fmap[Comma_to_Arrow]] well typed IS the naturality of that
 transformation, and [Comma_to_Arrow_naturality] says so in
 [comma_proj_nat]'s own vocabulary, by [naturality_sym].

 [Functor_StrictEq_Setoid] spells its morphism condition with raw
 [transport]/[transport_r]; every proof below works instead with the
 [hom_cast] kit of Construction/Quotient.v, over the one-line bridge
 [hom_cast_of_transports]/[transports_of_hom_cast] and the two derived
 helpers [strict_fmap_cast] and [Build_strict_eq].  This is the same trade
 Theory/Skeleton.v makes with [transport_square] and
 [strict_equiv_of_id_cast_nat]; those are phrased with [id_cast] rather
 than [hom_cast] and are not reused here only because that file's
 dependency cone is far heavier than this one's.

 Every principal is universe-polymorphic with nothing pinned to [Set].  The
 universal property does identify the hom/proof universes of A, B, C and X,
 which is forced by the statement: the comma category's own homs live at
 C's hom universe, and the statement composes functors in both directions
 across it (the equalities first appear at [comma_mediator]; the comma
 construction itself carries only inequalities).

 ** Neighbours

 Construction/Comma/Special.v settles Mac Lane's §II.6 remark on the
 specializations of the construction (slice, coslice, arrow category, and
 the discrete category on a hom-set), and its header carries the closed
 list; Construction/Comma/Natural/Transformation.v is Exercise 4, Huq's
 correspondence between natural transformations and functors sectioning
 both projections.  Construction/Arrow/Functor.v is the neighbouring
 Exercise II.4.7 -- functors INTO the arrow category are natural
 transformations -- and Theory/Shapes.v's [Two_Fun_Arrow] is the
 [[_2, C] ≅[Cat] Arrow C] comparison; neither is needed below. 

 --------
 参考文献：Saunders Mac Lane，《Categories for the Working Mathematician》，第2版，§II.6，第47-48页：显示（5）和（6）[maclane:II.6:construction1]的投影和图表，它们的箭头级定义[maclane:II.6:ex3]，以及泛性质[maclane:II.6:ex5]。下面的每条陈述总结都是目录的释义（doc/plan/books/maclane/inventory/II.json），而非书中的原文。
 nLab: https://ncatlab.org/nlab/show/comma+category
 nLab: https://ncatlab.org/nlab/show/arrow+category
 nLab: https://ncatlab.org/nlab/show/comma+object
 维基百科: https://en.wikipedia.org/wiki/Comma_category

 在[maclane:II.6:construction1]的目录释义中，逗号范畴携带指向两个域的投影函子——在对象上<e, d, f>给出e和d——以及到C^2的函子，给出箭头f本身，所有这些都构成一个在该行上可交换的图表。E --T--> C <--∂0-- C^2 --∂1--> C <--S-- D

 其中 ∂0 和 ∂1 是由两个函子 1 ⟶ 2 引出，将 C 的每个箭头分别映射到它的定义域和值域。练习 3 要求三种箭头上的函子；练习 5 要求任何带有使该图表交换的函子的类别 X 唯一地通过逗号范畴进行分解，这就是将其表现为“拉回”式极限的方式。

 ** 词典

 Mac Lane 对于 T : E ⟶ C 和 S : D ⟶ C 写作 (T ↓ S)；这棵树写作 (S ↓ T) 对 S : A ⟶ C 和 T : B ⟶ C（Construction/Comma.v）。字母互换，其余没有区别：Mac Lane      在此处定义
 ----------------------------------------------------------------------
 T : E ⟶ C     S : A ⟶ C
 S : D ⟶ C     T : B ⟶ C
 P              [comma_proj1]                    Construction/Comma.v
 Q              [comma_proj2]                    Construction/Comma.v
 R              [Comma_to_Arrow]                 本文件
 C^2            [Arrow C]  = (Id [C]  ↓ Id [C] )     Construction/Arrow.v
 C^{d0}         [Arrow_dom]                      本文件
 C^{d1}         [Arrow_cod]                      本文件[Arrow_dom] 和 [Arrow_cod] 不是封装器：它们是 [comma_proj1] 和 [comma_proj2] 在 S = T = Id [C] 下的实例化，下面的两个 [Example] 由 [eq_refl] 固定。练习 3 的答案方式相同：在一个交换方格上，每个 P、Q、∂0 和 ∂1 都返回相关的边，而 R 返回两条边的 S 和 T 映射对，所有这些都是定义上的，因此箭头级别的定义是 [eq_refl] 读数而非证明（[comma_proj1_fmap]、[comma_proj2_fmap]、[Arrow_dom_fmap]、[Arrow_cod_fmap]、[Comma_to_Arrow_dom_leg]、[Comma_to_Arrow_cod_leg]）。

 ** 图表方程的代价显示（5）的两个平方在严格强度下交换，在 [Functor_StrictEq_Setoid] —— 等同的对象映射，并且在传输后与 [fmap] 一致 —— 并且具有对象分量 [fun _ => eq_refl]，即两个复合体在对象映射上完全相同：[comma_diagram_dom] 和 [comma_diagram_cod]。这是可用的最强形式：函数 RECORDS 的莱布尼茨等式不可证明，[fmap_respects] / [fmap_id] / [fmap_comp] 字段作为证明项在两边被不同地构建。[≈[Cat]] 的读数 [comma_diagram_dom_Cat] / [comma_diagram_cod_Cat] 是通过 [strict_equiv_implies_fun_equiv] (Instance/StrictCat/ToCat.v) 得到的严格较弱的推论；回想一下 [≈[Cat]] 仅在自然同构意义下识别函子 (Instance/Cat.v)。

 ** 练习 5，以及证明相关性作用的地方对竞争者 (X, P', Q', R') 的假设是严格的，因为 Mac Lane 的图是：两个复合在 [Functor_StrictEq_Setoid] 上一致。中介者 [comma_mediator] 然后将 x 发送到逗号对象 (P' x, Q' x)，其中介箭头是 R' x 沿着假设提供的两个对象等式传输的，并且三个分解在严格强度下成立：[comma_mediator_proj1] 和 [comma_mediator_proj2]，其对象分量为 [eq_refl]，[comma_mediator_arrow]，其对象分量由假设自身的对象等式构成。它的态射部分完全使用了假设的箭头分量，没有其他。因此，就 Mac Lane 的意义而言，存在性是完全准确的。唯一性是证明相关设置与书中设置不同之处，这种差异不是形式化的产物。这三个方程是独立的数据。从 [Comma_to_Arrow ◯ L' ≈ R'] 只能恢复 [S (fst ``(L' x)) = fst ``(R' x)]，这是 C 中的一个方程；由于 S 在对象上不必是单射，因此 A 中没有方程可以推出，所以 [comma_proj1 ◯ L' ≈ P'] 确实是附加的信息，对 B 也是对称的。因此，一个竞争者会带来两个独立的证明，针对同一个对象方程 [S (fst ``(L' x)) = S (P' x)] —— 一个是通过 [f_equal S] 从第一个方程得到的，另一个是通过将第三个方程与 R' 上的假设组合得到的。将它们认同就是 C 对象上的身份证明唯一性，而认同它们所引出的态射则是相同的原理。在麦克·莱恩基于集合的理解中，这个问题不会出现，因为对象的相等性在这里是与证明无关的。

 [MediatesDiagram] 并不是假设 UIP，而是相对于前两个方程提出第三个方程：L x 的中介箭头，在沿着前两个方程所提供的对象等式传输到 S (P' x) ~> T (Q' x) 时，与 R' 提供的箭头在 [≈] 意义上是一致的。也就是说，“R' = R ◯ L'”的 [≈] 级内容，只涉及一族对象证明；这里构建的中介者（[comma_mediator_mediates]，其第三条款是 [reflexivity]）正好满足这个条件；由此，其唯一性在 [≈[Cat] 处（[comma_mediator_unique]）得到，因此自然同构的分量是对象等式转换。两个部分被包装为 [comma_diagram_ump]。因此，有三件事没有被提供，而是被命名而不是留给推理。首先，严格的唯一性——“L' x = L x 作为 S ↓ T 的对象”——除了上面证明的协调之外，还需要两个中介态射的莱布尼茨相等性，因为逗号对象将其态射作为数据，而集合同类库仅在态射之间提供 [≈]。第二，伪版本，其中假设只是自然同构意义下可交换：即二维范畴意义下的逗号对象，Construction/Comma.v 已经仅作为文档记录——逗号对象是 PIE 极限，可以由拉回和幂 C^2 构造（nLab, “comma object”）——而 Mac Lane 的练习 5 是严格的陈述，这就是这里所证明的内容。第三，这是第一个的一个结果：唯一性条款量化了 [MediatesDiagram] 竞争者，这个类别与麦克·莱恩的字面类别无法相比——在中介态射（[≈]，若箭头对象相等则需要莱布尼茨）上更弱，并且是相对于竞争者自己的 k1/k2 证明族陈述的——因此他的唯一性声明被呈现出来，而不是被涵盖。[comma_diagram_self] 和 [comma_diagram_self_via_ump] 闭合了环路，并保持了通用性质的两半不为空：逗号范畴自身的图是一个竞争者——它的假设字面上是 [comma_diagram_dom] 和 [comma_diagram_cod] ——在那里产生的中介是 [≈[Cat] ] 恒等映射（严格地说是 [comma_diagram_self_strict]），而恒等映射本身通过三次自反性（[comma_id_mediates]）满足 [MediatesDiagram]，因此唯一性定理在唯一的竞争者上得以使用，其答案是强制的。

 ** 重用，以及两个小套件[comma_proj_nat]（Construction/Comma.v）是 Mac Lane 的 R 的变换形式，这个文件与它相关，而不是重复它。它不能简单地插入：它的组件是一个在逗号对象上匹配的 [Program] 义务，而且在这个发展过程中 [sigT] 和 [prod] 都不携带定义性的 eta，因此 [comma_proj_nat x] 与 [`2 x] 不可转换。[Comma_to_Arrow] 直接采用 [`2 x] —— 这使得图形方程是定义性的 —— 并且这一一致性被记录为 [Comma_to_Arrow_is_proj_nat]，一个通过一个 [destruct] 证明的 Leibniz 等式。使 [fmap[Comma_to_Arrow] ] 类型良好的交换方形是该变换的自然性，而 [Comma_to_Arrow_naturality] 在 [comma_proj_nat] 自身的词汇中，通过 [naturality_sym] 说明了这一点。[Functor_StrictEq_Setoid] 使用原始的 [transport] / [transport_r] 拼写其同态条件；下面的每个证明都改为使用 Construction/Quotient.v 的 [hom_cast] 工具包，而不是单行桥 [hom_cast_of_transports] / [transports_of_hom_cast] 以及两个派生辅助 [strict_fmap_cast] 和 [Build_strict_eq]。这与 Theory/Skeleton.v 对 [transport_square] 和 [strict_equiv_of_id_cast_nat] 所做的权衡相同；那些使用 [id_cast] 表述，而不是 [hom_cast]，并且这里只是因为该文件的依赖锥比这个文件的要重而没有复用。每个主元都是宇宙多态的，没有固定在 [Set] 上。
 普适性确实标识了 A、B、C 和 X 的同态/证明宇宙，这由以下陈述所强制：逗号范畴自身的同态存在于 C 的同态宇宙中，并且该陈述在逗号范畴上双向组合函子（这些等式首次出现在 [comma_mediator]；逗号构造本身仅携带不等式）。

 ** 邻居Construction/Comma/Special.v 解决了 Mac Lane §II.6 关于构造的特例（切片、余切片、箭头范畴以及 Hom-集上的离散范畴）的评论，其标题包含封闭列表；Construction/Comma/Natural/Transformation.v 是练习 4，即 Huq 的自然变换与分段两个投影函子对应的章节。Construction/Arrow/Functor.v 是相邻的练习 II.4.7 —— 进入箭头范畴的函子就是自然变换 —— 而 Theory/Shapes.v 的 [Two_Fun_Arrow] 是 [[_2, C] ≅ [Cat] [Arrow C] 比较；下面都不需要它们。
*)

(*
   * ** Transport and [hom_cast]: the two spellings of strict functor equality 

   --------
   * ** 传输与 [hom_cast]：严格函子相等的两种拼写
*)

Section StrictCastKit.

Context {D : Category}.

Lemma hom_cast_of_transports {a a' b b' : D}
      (ea : a = a') (eb : b = b') (f : a ~{D}~> b) (g : a' ~{D}~> b') :
  transport (fun z => a ~{D}~> z) eb f
    ≈ transport_r (fun z => z ~{D}~> b') ea g
  → hom_cast ea eb f ≈ g.
Proof. destruct ea, eb; simpl; unfold transport_r; simpl; auto. Qed.

Lemma transports_of_hom_cast {a a' b b' : D}
      (ea : a = a') (eb : b = b') (f : a ~{D}~> b) (g : a' ~{D}~> b') :
  hom_cast ea eb f ≈ g
  → transport (fun z => a ~{D}~> z) eb f
      ≈ transport_r (fun z => z ~{D}~> b') ea g.
Proof. destruct ea, eb; simpl; unfold transport_r; simpl; auto. Qed.

End StrictCastKit.

Definition strict_fmap_cast {C D : Category} {F G : C ⟶ D}
           (H : @equiv _ (@Functor_StrictEq_Setoid C D) F G)
           {x y : C} (f : x ~> y) :
  hom_cast (`1 H x) (`1 H y) (fmap[F] f) ≈ fmap[G] f :=
  hom_cast_of_transports _ _ _ _ (`2 H x y f).

Definition Build_strict_eq {C D : Category} {F G : C ⟶ D}
           (eo : ∀ x : C, F x = G x)
           (em : ∀ (x y : C) (f : x ~> y),
                   hom_cast (eo x) (eo y) (fmap[F] f) ≈ fmap[G] f) :
  @equiv _ (@Functor_StrictEq_Setoid C D) F G :=
  (eo; fun x y f => transports_of_hom_cast _ _ _ _ (em x y f)).

(* * ** The domain and codomain functors of the arrow category / * ** 箭头范畴的定义域和陪域函子 *)

Definition Arrow_dom {C : Category} : @Arrow C ⟶ C := @comma_proj1 C C C Id[C] Id[C].
Definition Arrow_cod {C : Category} : @Arrow C ⟶ C := @comma_proj2 C C C Id[C] Id[C].

Example Arrow_dom_is_comma_proj1 {C : Category} :
  @Arrow_dom C = @comma_proj1 C C C Id[C] Id[C] := eq_refl.

Example Arrow_cod_is_comma_proj2 {C : Category} :
  @Arrow_cod C = @comma_proj2 C C C Id[C] Id[C] := eq_refl.

Example Arrow_dom_fobj {C : Category} (x : @Arrow C) :
  Arrow_dom x = fst ``x := eq_refl.

Example Arrow_cod_fobj {C : Category} (x : @Arrow C) :
  Arrow_cod x = snd ``x := eq_refl.

Example Arrow_dom_fmap {C : Category} (x y : @Arrow C) (f : x ~> y) :
  fmap[Arrow_dom] f = fst ``f := eq_refl.

Example Arrow_cod_fmap {C : Category} (x y : @Arrow C) (f : x ~> y) :
  fmap[Arrow_cod] f = snd ``f := eq_refl.

Lemma Arrow_square {C : Category} (x y : @Arrow C) (f : x ~> y) :
  `2 y ∘ fmap[Arrow_dom] f ≈ fmap[Arrow_cod] f ∘ `2 x.
Proof. exact (`2 f). Qed.

(*
   * ** Mac Lane's functor [R] : the comma category over the arrow category 

   --------
   * ** 麦克莱恩的函子  [R] ：箭头范畴上的逗号范畴
*)

Section CommaToArrow.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition Comma_to_Arrow : (S ↓ T) ⟶ @Arrow C := {|
  fobj := fun x => ((S (fst ``x), T (snd ``x)); `2 x);
  fmap := fun _ _ f => ((fmap[S] (fst ``f), fmap[T] (snd ``f)); _)
|}.
Next Obligation. intros x y f; exact (`2 f). Defined.
Next Obligation.
  intros x y f g [e0 e1]; split; simpl.
  - now rewrite e0.
  - now rewrite e1.
Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

Example Comma_to_Arrow_fobj (x : S ↓ T) :
  Comma_to_Arrow x = ((S (fst ``x), T (snd ``x)); `2 x) := eq_refl.

Example Comma_to_Arrow_mediating (x : S ↓ T) :
  `2 (Comma_to_Arrow x) = `2 x := eq_refl.

Example Comma_to_Arrow_dom_leg (x y : S ↓ T) (f : x ~> y) :
  fmap[Arrow_dom] (fmap[Comma_to_Arrow] f) = fmap[S] (fst ``f) := eq_refl.

Example Comma_to_Arrow_cod_leg (x y : S ↓ T) (f : x ~> y) :
  fmap[Arrow_cod] (fmap[Comma_to_Arrow] f) = fmap[T] (snd ``f) := eq_refl.

(*
 Exercise 3 for [P] and [Q] as well: both projections act on a comma
 morphism -- a commuting square -- by returning its leg in the relevant
 factor, definitionally. 

 --------
 练习 3 对 [P] 和 [Q] 也适用：两个投影都作用于逗号态射——一个交换平方——通过返回其在相关因子中的边，这是根据定义的。
*)
Example comma_proj1_fmap (x y : S ↓ T) (f : x ~> y) :
  fmap[comma_proj1] f = fst ``f := eq_refl.

Example comma_proj2_fmap (x y : S ↓ T) (f : x ~> y) :
  fmap[comma_proj2] f = snd ``f := eq_refl.

Lemma Comma_to_Arrow_is_proj_nat (x : S ↓ T) :
  `2 (Comma_to_Arrow x) = comma_proj_nat x.
Proof. destruct x as [[a b] h]; reflexivity. Qed.

Lemma Comma_to_Arrow_naturality (x y : S ↓ T) (f : x ~> y) :
  comma_proj_nat y ∘ fmap[S ◯ comma_proj1] f
    ≈ fmap[T ◯ comma_proj2] f ∘ comma_proj_nat x.
Proof. apply naturality_sym. Qed.

(*
   * ** The commuting diagram, Mac Lane's displays (5)-(6) 

   --------
   * ** 交换图，Mac Lane 的展示 (5)-(6)
*)

(*
 [Defined], not [Qed], for the same reason as [comma_mediator_proj1] below:
 [comma_diagram_self] feeds these two back in as the hypotheses of the
 universal property and needs their object components to reduce. 

 --------
 [Defined]，而不是 [Qed]，原因与下面的 [comma_mediator_proj1] 相同：
 [comma_diagram_self] 将这两个作为范畴性质的假设反馈回来，并且需要它们的对象部分来化简。
*)
Theorem comma_diagram_dom :
  @equiv _ (@Functor_StrictEq_Setoid (S ↓ T) C)
         (Arrow_dom ◯ Comma_to_Arrow) (S ◯ comma_proj1).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Theorem comma_diagram_cod :
  @equiv _ (@Functor_StrictEq_Setoid (S ↓ T) C)
         (Arrow_cod ◯ Comma_to_Arrow) (T ◯ comma_proj2).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Example comma_diagram_dom_obj (x : S ↓ T) : `1 comma_diagram_dom x = eq_refl
  := eq_refl.

Example comma_diagram_cod_obj (x : S ↓ T) : `1 comma_diagram_cod x = eq_refl
  := eq_refl.

Corollary comma_diagram_dom_Cat :
  Arrow_dom ◯ Comma_to_Arrow ≈[Cat] S ◯ comma_proj1.
Proof. apply strict_equiv_implies_fun_equiv, comma_diagram_dom. Qed.

Corollary comma_diagram_cod_Cat :
  Arrow_cod ◯ Comma_to_Arrow ≈[Cat] T ◯ comma_proj2.
Proof. apply strict_equiv_implies_fun_equiv, comma_diagram_cod. Qed.

End CommaToArrow.

(*
   * ** Rebuilding a comma / arrow object from its cast components 

   --------
   * ** 从其转换组件重新构建逗号/箭头对象
*)

Lemma arrow_eta_cast {C : Category} (z : @Arrow C) {d0 d1 : C}
      (p : Arrow_dom z = d0) (q : Arrow_cod z = d1) :
  (((d0, d1); hom_cast p q (`2 z)) : @Arrow C) = z.
Proof. destruct z as [[c0 c1] h]; simpl in *; destruct p, q; reflexivity. Defined.

(*
 A [hom_cast] between two arrow objects presented through [arrow_eta_cast]
 is settled by its two legs, which is all the hom-setoid of the arrow
 category records.  Every endpoint here is a variable, so the whole proof is
 a [destruct] of the four object equalities; the lemma is then applied — not
 rewritten with — so that unification may unfold [Arrow] to [Id ↓ Id]. 

 --------
 通过 [arrow_eta_cast] 展示的两个箭头对象之间的 [hom_cast]，由它的两条腿来确定，这就是箭头范畴记录的整个同等集。这里的每个端点都是一个变量，所以整个证明是四个对象等式的 [destruct]；然后应用引理——而不是用它重写——以便统一可以将 [Arrow] 展开为 [Id ↓ Id]。
*)
Lemma arrow_eta_cast_legs {C : Category} (z w : @Arrow C) {d0 d1 e0 e1 : C}
      (p : Arrow_dom z = d0) (q : Arrow_cod z = d1)
      (p' : Arrow_dom w = e0) (q' : Arrow_cod w = e1)
      (u : (((d0, d1); hom_cast p q (`2 z)) : @Arrow C)
             ~> (((e0, e1); hom_cast p' q' (`2 w)) : @Arrow C))
      (v : z ~{@Arrow C}~> w) :
  hom_cast p p' (fmap[Arrow_dom] v) ≈ fmap[Arrow_dom] u
  → hom_cast q q' (fmap[Arrow_cod] v) ≈ fmap[Arrow_cod] u
  → hom_cast (arrow_eta_cast z p q) (arrow_eta_cast w p' q') u ≈ v.
Proof.
  destruct z as [[c0 c1] h], w as [[c0' c1'] h']; simpl in *.
  destruct p, q, p', q'; simpl.
  intros H0 H1; split; [ now symmetry | now symmetry ].
Qed.

(*
   * ** Mac Lane §II.6 Exercise 5: the universal property 

   --------
   * ** Mac Lane §II.6 练习 5：泛性质
*)

Section UMP.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.
Context {X : Category}.
Context {P' : X ⟶ A}.
Context {Q' : X ⟶ B}.
Context {R' : X ⟶ @Arrow C}.

Context (Hdom : @equiv _ (@Functor_StrictEq_Setoid X C)
                       (Arrow_dom ◯ R') (S ◯ P')).
Context (Hcod : @equiv _ (@Functor_StrictEq_Setoid X C)
                       (Arrow_cod ◯ R') (T ◯ Q')).

Definition ump_dom_obj (x : X) : Arrow_dom (R' x) = S (P' x) := `1 Hdom x.
Definition ump_cod_obj (x : X) : Arrow_cod (R' x) = T (Q' x) := `1 Hcod x.

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition comma_mediator : X ⟶ (S ↓ T) := {|
  fobj := fun x => ((P' x, Q' x);
                    hom_cast (ump_dom_obj x) (ump_cod_obj x) (`2 (R' x)));
  fmap := fun _ _ g => ((fmap[P'] g, fmap[Q'] g); _)
|}.
Next Obligation.
  intros x y g; simpl.
  rewrite <- (strict_fmap_cast Hdom g), <- (strict_fmap_cast Hcod g).
  rewrite !hom_cast_comp.
  apply hom_cast_respects.
  exact (`2 (fmap[R'] g)).
Qed.
Next Obligation.
  intros x y f g e; split; simpl; now rewrite e.
Qed.
Next Obligation. intros x; split; simpl; apply fmap_id. Qed.
Next Obligation. intros x y z f g; split; simpl; apply fmap_comp. Qed.

(*
 [Defined], not [Qed]: [comma_mediator_mediates] below projects out the
 object-equality component and needs it to reduce to [eq_refl]. 

 --------
 [Defined]，而不是 [Qed]：下面的 [comma_mediator_mediates] 提取了对象相等性组件，并需要将其简化为 [eq_refl]。
*)
Theorem comma_mediator_proj1 :
  @equiv _ (@Functor_StrictEq_Setoid X A) (comma_proj1 ◯ comma_mediator) P'.
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Theorem comma_mediator_proj2 :
  @equiv _ (@Functor_StrictEq_Setoid X B) (comma_proj2 ◯ comma_mediator) Q'.
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Example comma_mediator_proj1_obj (x : X) : `1 comma_mediator_proj1 x = eq_refl
  := eq_refl.

Example comma_mediator_proj2_obj (x : X) : `1 comma_mediator_proj2 x = eq_refl
  := eq_refl.

Theorem comma_mediator_arrow :
  @equiv _ (@Functor_StrictEq_Setoid X (@Arrow C))
         (Comma_to_Arrow ◯ comma_mediator) R'.
Proof.
  apply (Build_strict_eq (F := Comma_to_Arrow ◯ comma_mediator) (G := R')
           (fun x => arrow_eta_cast (R' x) (ump_dom_obj x) (ump_cod_obj x))).
  intros x y g.
  apply arrow_eta_cast_legs.
  - exact (strict_fmap_cast Hdom g).
  - exact (strict_fmap_cast Hcod g).
Qed.

(** The three commuting equations for a competing mediator. / 对于竞争介质的三个对易方程。 *)
Definition MediatesDiagram (L : X ⟶ (S ↓ T)) : Type :=
  { k1 : @equiv _ (@Functor_StrictEq_Setoid X A) (comma_proj1 ◯ L) P' &
  { k2 : @equiv _ (@Functor_StrictEq_Setoid X B) (comma_proj2 ◯ L) Q' &
    ∀ x : X,
      hom_cast (f_equal S (`1 k1 x)) (f_equal T (`1 k2 x)) (`2 (L x))
        ≈ hom_cast (ump_dom_obj x) (ump_cod_obj x) (`2 (R' x)) }}.

Lemma comma_mediator_mediates : MediatesDiagram comma_mediator.
Proof.
  exists comma_mediator_proj1, comma_mediator_proj2.
  intro x; reflexivity.
Qed.

Theorem comma_mediator_unique (L : X ⟶ (S ↓ T)) :
  MediatesDiagram L → L ≈[Cat] comma_mediator.
Proof.
  intros [k1 [k2 k3]].
  unshelve eexists.
  - intro x.
    unshelve refine
      (@Build_Isomorphism (S ↓ T) (L x) (comma_mediator x)
         ((id_cast (`1 k1 x), id_cast (`1 k2 x)); _)
         ((id_cast (eq_sym (`1 k1 x)), id_cast (eq_sym (`1 k2 x))); _)
         _ _).
    + simpl.
      rewrite !fmap_id_cast.
      rewrite <- (k3 x), hom_cast_decompose.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
    + simpl.
      rewrite !fmap_id_cast, <- !eq_sym_map_distr.
      rewrite <- (k3 x), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l.
      now rewrite id_left.
    + split; simpl; apply id_cast_inv_r.
    + split; simpl; apply id_cast_inv_l.
  - intros x y g; split; simpl.
    + rewrite <- (strict_fmap_cast k1 g), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l, id_left.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
    + rewrite <- (strict_fmap_cast k2 g), hom_cast_decompose.
      rewrite !comp_assoc, id_cast_inv_l, id_left.
      rewrite <- !comp_assoc, id_cast_inv_l.
      now rewrite id_right.
Qed.

Theorem comma_diagram_ump :
  { L : X ⟶ (S ↓ T)
  & (MediatesDiagram L * (∀ L' : X ⟶ (S ↓ T), MediatesDiagram L' → L' ≈[Cat] L))%type }.
Proof.
  exists comma_mediator.
  split.
  - exact comma_mediator_mediates.
  - exact comma_mediator_unique.
Defined.

End UMP.

(*
   * ** Non-vacuity: the comma category is its own mediator 

   --------
   * ** 非虚空性：逗号范畴是其自身的媒介者
*)

(*
 The hypotheses of the universal property are inhabited -- by the diagram
 the comma category itself carries, where they are literally
 [comma_diagram_dom] and [comma_diagram_cod] -- and at that competitor the
 mediator produced is [≈[Cat]] the identity functor (strictly so, in fact:
 [comma_diagram_self_strict]).  The identity moreover satisfies
 [MediatesDiagram] outright ([comma_id_mediates], three reflexivities), so
 [comma_mediator_unique] can be EXERCISED at it
 ([comma_diagram_self_via_ump]) -- with that, both halves of Exercise 5 are
 checked against the one case whose answer is forced. 

 --------
 普遍性质的假设是可充满的——由箭头图本身所携带的逗号范畴给出，它们字面上是 [comma_diagram_dom] 和 [comma_diagram_cod]——在该竞争者处，产生的中介子是 [≈[Cat]，也就是恒等函子（严格来说确实如此：[comma_diagram_self_strict]）。此外，恒等函子满足 [MediatesDiagram]（[comma_id_mediates]，三个自反性），因此 [comma_mediator_unique] 可以在其上执行（[comma_diagram_self_via_ump]）——通过这个，两部分练习5都可以在那个答案被强制的一种情况下验证。
*)
Section SelfMediation.

Context {A B C : Category}.
Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

Definition comma_self_mediator : (S ↓ T) ⟶ (S ↓ T) :=
  comma_mediator (P' := comma_proj1) (Q' := comma_proj2) (R' := Comma_to_Arrow)
                 comma_diagram_dom comma_diagram_cod.

Example comma_self_mediator_fobj (x : S ↓ T) :
  comma_self_mediator x = ((fst ``x, snd ``x); `2 x) := eq_refl.

Theorem comma_diagram_self : comma_self_mediator ≈[Cat] Id[S ↓ T].
Proof.
  unshelve eexists.
  - intro x.
    unshelve refine
      (@Build_Isomorphism (S ↓ T) (comma_self_mediator x) x
         ((id, id); _) ((id, id); _) _ _).
    + abstract (simpl; rewrite !fmap_id, id_left; now rewrite id_right).
    + abstract (simpl; rewrite !fmap_id, id_left; now rewrite id_right).
    + split; simpl; apply id_left.
    + split; simpl; apply id_left.
  - intros x y g; split; simpl; now rewrite id_left, id_right.
Qed.

(*
 The strict form is also available: the self-mediator and the identity
 have literally the same object map, and their fmaps agree by the
 category laws. 

 --------
 严格形式也是可用的：自我中介者和恒等映射在字面上有相同的对象映射，并且它们的函子映射根据范畴律是相符的。
*)
Theorem comma_diagram_self_strict :
  @equiv _ Functor_StrictEq_Setoid comma_self_mediator Id[S ↓ T].
Proof.
  unshelve eexists.
  - intro x; destruct x as [[a b] h]; reflexivity.
  - intros [[a b] h] [[a' b'] h'] f; split; simpl; cat.
Qed.

(*
 The identity functor satisfies [MediatesDiagram] at the comma's own
 diagram by three reflexivities -- which lets the UNIQUENESS half of the
 universal property be exercised, not merely stated: [comma_mediator_unique]
 at this competitor re-derives [comma_diagram_self] from the other side.
 (Adapted from the adversarial audit's probe, with thanks.) 

 --------
 恒等函子在逗号自身的图上通过三个自反性满足 [MediatesDiagram] —— 这使得普遍性质的唯一性部分能够被实际应用，而不仅仅是陈述：[comma_mediator_unique] 在这个竞争者处从另一边重新推导出 [comma_diagram_self]。（改编自对抗性审计的探测，表示感谢。）
*)
Lemma comma_id_mediates :
  MediatesDiagram (P' := comma_proj1) (Q' := comma_proj2) (R' := Comma_to_Arrow)
                  comma_diagram_dom comma_diagram_cod (Id[S ↓ T]).
Proof.
  unshelve eexists.
  - exists (fun _ => eq_refl); intros; reflexivity.
  - unshelve eexists.
    + exists (fun _ => eq_refl); intros; reflexivity.
    + intro x; reflexivity.
Qed.

Theorem comma_diagram_self_via_ump : Id[S ↓ T] ≈[Cat] comma_self_mediator.
Proof. exact (comma_mediator_unique _ _ _ comma_id_mediates). Qed.

End SelfMediation.
