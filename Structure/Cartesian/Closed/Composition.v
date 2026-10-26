Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.Coend.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.

Generalizable All Variables.

(* * * Internal composition in a cartesian closed category / * * 在笛卡尔闭范畴中的内部复合 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., Springer
 GTM 5, 1998, §IV.6, printed p. 98, Exercise 4 (`maclane:IV.6:ex4`),
 verbatim from the printed page:

 “4. In any cartesian closed category obtain a natural transformation
 c^b × b^a → c^a which agrees in Set with composition of functions.
 Prove it (like composition) associative.”

 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
 nLab: https://ncatlab.org/nlab/show/dinatural+transformation
 nLab: https://ncatlab.org/nlab/show/enriched+category

 NOTATION.  Mac Lane's c^b is this tree's [exponent_obj b c], and the
 tree's notation [y ^ x] abbreviates [exponent_obj x y]
 (Structure/Cartesian/Closed.v).  The two spellings therefore agree on
 the DISPLAY -- [internal_compose : c^b × b^a ~> c^a] reads the same in
 both -- while the [exponent_obj] argument pairs are (b,c), (a,b) and
 (a,c) respectively; [internal_compose_obj] pins that by [eq_refl].

 THE CONSTRUCTION.  [internal_compose] is the transpose of the double
 evaluation

 (c^b × b^a) × a --to prod_assoc--> c^b × (b^a × a)
 --second eval---->  c^b × b
 --eval----------->  c.

 The DEFINITION spends exactly two [Closed] fields, [exponent_obj]
 and [exp_iso]: [curry], [uncurry] and [eval] are all
 derived from [exp_iso].  The beta law [ump_exponents']
 is what the PROOFS below spend, through [eval_curry] and
 [ump_exponents].  [internal_id x : 1 ~> x^x] is the transpose of the
 projection [exr : 1 × x ~> x].

 Every equation below is a bounded number of rewrites with three
 [eval]-level rules, then the fork algebra -- [exl_fork]/[exr_fork]
 where the composite is already a fork, [unfork] where a whole fork has
 to be split.  [eval_internal_compose_fork]
 strips one [internal_compose] from inside an evaluation,
 [eval_internal_id_fork] one [internal_id], and [eval_ihom_fork] one
 [ihom]; each is [eval_curry] at the respective transpose.  The unit
 laws take the shorter route through [uncurry_internal_compose], the
 transpose read at a pair of generalized elements.

 WHAT “NATURAL” CAN AND CANNOT MEAN HERE, which is the one place where
 the exercise's own wording has to be read with care.  In [c^b × b^a]
 the object [b] occurs CONTRAVARIANTLY in [c^b] and COVARIANTLY in
 [b^a].  An arrow [f : b1 ~> b2] therefore acts on the two factors in
 OPPOSITE directions and the resulting morphism runs between the MIXED
 objects [c^b2 × b1^a] and [c^b1 × b2^a]; there is no functor of [b]
 alone for a natural transformation in [b] to run BETWEEN, and “natural
 in all three objects” is not a well-typed demand.  Genuine naturality
 is available in [a] and in [c], and both are delivered as squares AND
 as transformations:

 - [internal_compose_natural_c] between the covariant functors
 [ComposeSrcC a b] and [ExpBase a], packaged as
 [compose_Transform_c];
 - [internal_compose_natural_a] between the contravariant functors
 [ComposeSrcA b c] and [ExpExp c], both [C^op ⟶ C], packaged as
 [compose_Transform_a].

 For [b] the honest statement is DINATURALITY, and it is delivered as
 an inhabitant of the tree's own vocabulary rather than as a bare
 equation: [internal_compose_dinatural] is the equation,
 [internal_compose_Cowedge_cond] is that equation read as
 Structure/Coend.v's [Cowedge_cond] at the mixed-variance
 bifunctor [ComposeB a c : C^op ∏ C ⟶ C],
 [ComposeB a c (b1, b2) = c^b1 × b2^a], with constant apex [c^a], and
 [internal_compose_Wedge] is the resulting
 [Wedge (Opposite_Functor (ComposeB a c))] -- a cowedge for
 [ComposeB a c].  NOTHING here claims naturality in [b];
 Test/ProbeComposition391.v pins the non-statement as a TYPING negative
 (the mixed-object mismatch above), with the dinaturality equation
 beside it as the passing control.

 ASSOCIATIVITY is Mac Lane's own closing demand, “prove it (like
 composition) associative”.  It is stated in exactly the shape
 Construction/Enriched.v's [ecompose_assoc] field needs, that is
 through the associator, so that the enrichment below discharges that
 field by [exact] rather than by a restatement:

 internal_compose ∘ split internal_compose id
 ≈ internal_compose ∘ split id internal_compose ∘ to prod_assoc.

 Over [CC_Monoidal] the tensor of morphisms IS [split], the associator
 IS the cartesian one and the two unitors ARE the projections, all at
 [eq_refl]; Structure/Ring.v records the same identifications
 and [assoc_bimap_is_split], [assoc_tensor_is_prod],
 [assoc_unit_left_is_exr] and [assoc_unit_right_is_exl] re-check them
 here, so a later change to either side would be caught.

 THE PAYOFF is [CCC_Enriched : @Enriched C CC_Monoidal], a cartesian
 closed category enriched over ITSELF, with [eobj := obj[C]],
 [ehom x y := y^x], [eid := internal_id] and
 [ecompose := internal_compose]; all three law fields are [exact] of
 the unit and associativity theorems above, so the enrichment adds no
 equational content of its own.  [Sets_Enriched] instantiates it.
 Self-enrichment as such is NOT new in tree --
 Construction/Enriched/Ab.v's [Enriched_Ab_itself] is an
 [@Enriched Ab Ab_Monoidal] -- so the gap this closes is the narrower
 one: no CARTESIAN CLOSED category was enriched over itself.  Nor is
 [CC_Monoidal] a first, and the reason it looks like one is an ALIAS:
 Construction/Enriched/Two.v's [Enriched_of_TwoPreorder] is an
 [@Enriched _2 Two_Monoidal], and [Two_Monoidal] IS
 [@CC_Monoidal _2 Two_Cartesian Two_Terminal] at [eq_refl] through the
 plain Definition at Structure/Monoidal/Cartesian.v, so a name grep
 for [CC_Monoidal] -- which returns 18 files -- does not see it.  That
 instance is not self-enrichment: its [eobj] is [tpre_carrier P], an
 arbitrary preorder carrier rather than the objects of [_2].

 THE [Set] CLAUSE, at its measured grade.  Mac Lane asks that the
 transformation “agree in Set with composition of functions”.  [Sets]
 is this library's category of setoids, whose exponential [c^b] is the
 setoid of ≈-respecting maps, so the statement is pointwise on setoid
 morphisms, and [sets_internal_compose] holds at [eq_refl]: the value
 of [internal_compose (g, f)] at [t] IS [g (f t)].  So does
 [sets_internal_id].  At the level of whole MORPHISMS of [Sets] the
 grade drops to [≈] ([sets_internal_compose_morphism]), and the cause
 is located rather than guessed: the two underlying FUNCTIONS are the
 same term ([sets_internal_compose_underlying], [eq_refl]), so what
 differs is exactly the [proper_morphism] certificate the two sides
 rebuild.  The strict form is refuted and pinned in the probe.

 AN ENGINEERING HAZARD, met again and measured more narrowly than the
 donor states it.  Structure/Cartesian/Closed/Natural.v records
 that elaborating a functor's object action INSIDE its own [Program
 Definition] lets [Program] defer an unresolved instance argument of
 [product_obj] into an obligation, which Lib/Foundation.v's [Unset
 Transparent Obligations] makes opaque, after which [fobj] converts
 with nothing.  The five functors here therefore give their object and
 arrow actions as ordinary definitions first.  The boundary is narrower
 than “any inline object action”: an inline [exponent_obj] alone DOES
 reduce, and it is [product_obj] -- the [Cartesian] instance -- that is
 deferred, which is the donor's attribution rather than a fact
 re-derived here.  What the probe machine-checks is the SEPARATION, the
 exponent-only functor as a passing control and the product one as a
 CONVERSION negative.  The four [*_fobj] Examples record that FOUR of
 the five shipped functors reduce; [ComposeB] reduces as well, but that
 is measured rather than pinned by an Example.

 UNIVERSES, off BOTH binder and block.  Every constant is over
 [C : Category@{u u0 u0}] -- hom identified with proof -- in the
 BINDER, while not one constraint BLOCK contains a universe equation:
 reading the blocks alone would report no identification.  It is
 inherited, and [Cartesian] alone already forces it, which the probe
 pins as a FORMABILITY negative against the category, its objects, its
 hom-sets, its identities and its composition all accepted at hom and
 proof declared strictly apart.  No word-bounded [Set] occurs in any
 binder or block.

 AXIOMS.  All 71 constants of this file -- the 53 named declarations
 plus the 18 [Program] obligations of the five functors and the
 enrichment, which no source sweep sees -- report “Closed under the
 global context”.  [Sets_Closed] obtains its exponentials with no axiom
 (Instance/Coq.v records the contrast), so the [Set] clause costs
 nothing; the axiom-carrying [Coq_Closed] (Instance/Coq.v) is
 deliberately NOT instantiated here and Instance/Coq.v is not required.

 PRIOR ART, measured.  [internal_compose], [internal_comp],
 [comp_internal] and [internal_id] have zero occurrences anywhere else
 in the tree, and no declaration elsewhere has an object action of the
 shape [c^b × b^a].  Structure/Closed.v does declare a [hom_compose]
 field, but the whole [Class Closed] block there sits inside the
 comment opened at Structure/Closed.v by a dated deferral marker
 and closed, and its shape is the CURRIED Eilenberg-Kelly one,
 [[y, z] ~> [[x, y], [x, z]]], which is not the shape this
 exercise asks for; it is not revived here.  What did exist, and is
 CONSUMED rather than rebuilt, is Structure/Cartesian/Closed/Natural.v's
 [ihom f h := curry (h ∘ eval ∘ second f)] -- the internal hom's
 own two-variable action, which IS [fmap[InternalHomFunctor]] at
 [eq_refl] -- together with [ihom_id], [ihom_comp] and the
 [opobj]/[oparr] readings of a contravariant slot.

 NOT DELIVERED.  No coend or end of [ComposeB], so nothing says the
 cowedge is universal; no [EnrichedFunctor] and no comparison of
 [CCC_Enriched] with Construction/Enriched.v's
 [Category_is_Enriched_over_Set]; no relation between [ExpBase] and
 Structure/Cartesian/Closed/Adjunction.v's [Exp_Functor], which
 would need that module -- see the note before the functors for what
 is read off its source and what requiring it would cost; no
 monoidal-closed generalisation, so nothing here is stated over
 Structure/Monoidal/Closed.v; no witness at a cartesian closed category
 other than [Sets]; and nothing is registered as an [Instance]. 

 --------
 Mac Lane，《为工作数学家准备的范畴论》，第2版，Springer GTM 5, 1998，第IV.6节，印刷第98页，练习4 (`maclane:IV.6:ex4`)，逐字印刷内容：

 “4. 在任何笛卡尔闭范畴中，得到一个自然变换 c^b × b^a → c^a，其在Set中与函数组合一致。证明它（像组合一样）是结合的。”

 nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
 nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
 nLab: https://ncatlab.org/nlab/show/dinatural+transformation
 nLab: https://ncatlab.org/nlab/show/enriched+category

 符号：Mac Lane 的 c^b 对应该树的 [exponent_obj b c]，而该树的符号 [y ^ x] 缩写表示 [exponent_obj x y]（Structure/Cartesian/Closed.v）。因此，这两种写法在显示上是一致的——[internal_compose : c^b × b^a ~> c^a] 在两者中读法相同——而 [exponent_obj] 的参数对分别为 (b,c)、(a,b) 和 (a,c)；[internal_compose_obj] 通过 [eq_refl] 将其固定。构造。[internal_compose] 是双重求值的转置

 (c^b × b^a) × a --to prod_assoc--> c^b × (b^a × a)
 --second eval----> c^b × b
 --eval-----------> c。

 定义正好使用了两个 [Closed] 字段，[exponent_obj] 和 [exp_iso]：[curry]、[uncurry] 和 [eval] 都是从 [exp_iso] 推导出来的。beta 法则 [ump_exponents'] 是以下证明中通过 [eval_curry] 和 [ump_exponents] 使用的。[internal_id x : 1 ~> x^x] 是投影 [exr : 1 × x ~> x] 的转置。下面的每个方程都是通过一个有限次数的三个 [eval] 级规则的重写，然后是分叉代数 -- [exl_fork] / [exr_fork]，其中复合已经是一个分叉，ZW27WZZ，其中整个分叉必须被拆分。ZW28WZZ 从评估内部去掉一个 [internal_compose]，ZW30WZZ 去掉一个 [internal_id]，ZW32WZZ 去掉一个 [ihom]；每个在各自的转置处都是 [eval_curry]。单位律通过 [uncurry_internal_compose] 采取更短的路径，转置在一对广义元素上读取。在这里“自然（NATURAL）”可以和不可以意味着什么，这是唯一一个需要仔细阅读练习自身措辞的地方。在 [c^b × b^a] 中，对象 [b] 在 [c^b] 中是逆变出现的，在 [b^a] 中是协变出现的。因此，一个箭头 [f : b1 ~> b2] 对两个因子作用的方向相反，得到的态射在混合对象 [c^b2 × b1^a] 和 [c^b1 × b2^a] 之间运行；没有仅在 [b] 上的函子让 [b] 中的自然变换进行“运行”，并且“在所有三个对象中自然”不是一个类型正确的要求。真正的自然性存在于 [a] 和 [c]，并且两者都以平方图形式和变换的形式提供：-  在协变函子  [ComposeSrcC a b]  和  [ExpBase a]  之间的  [internal_compose_natural_c] ，封装为 [compose_Transform_c]；
 -  在逆变函子  [ComposeSrcA b c]  和  [ExpExp c]  之间的  [internal_compose_natural_a] ，两者都是  [C^op ⟶ C] ，封装为 [compose_Transform_a]。对于 [b]，诚实的陈述是 DINATURALITY，并且它是以树自身词汇的居民身份呈现的，而不是以一个简单的方程式呈现：[internal_compose_dinatural] 是方程式，[internal_compose_Cowedge_cond] 是将该方程式按 Structure/Coend.v 的 [Cowedge_cond] 在混合方差双函子 [ComposeB a c : C^op ∏ C ⟶ C]、[ComposeB a c (b1, b2) = c^b1 × b2^a]、常数顶点 [c^a] 下读取，[internal_compose_Wedge] 是产生的 [Wedge (Opposite_Functor (ComposeB a c))] —— [ComposeB a c] 的一个共楔。这里没有任何内容声称 [b] 的自然性；Test/ProbeComposition391.v 将非陈述固定为一个 TYPING 负值（上述混合对象不匹配），旁边的 dinaturality 方程作为通过控制。结合性（ASSOCIATIVITY）是 Mac Lane 自己最后的要求，“证明它（像组合一样）是结合的”。它正是以 Construction/Enriched.v 中 [ecompose_assoc] 字段所需要的形式来陈述的，即通过结合子（associator），这样下面的增广通过 [exact] 而不是通过重新陈述来完成该字段：

 internal_compose ∘ split internal_compose id
 ≈ internal_compose ∘ split id internal_compose ∘ to prod_assoc。

 在 [CC_Monoidal] 上，态射的张量是 [split]，结合子是笛卡尔结合子，两单位子是投影，都在 [eq_refl] 上；Structure/Ring.v 记录了相同的等同，[assoc_bimap_is_split]、[assoc_tensor_is_prod]、[assoc_unit_left_is_exr] 和 [assoc_unit_right_is_exl] 在此重新检查它们，因此对任一边的后续更改都能被捕捉到。回报是 [CCC_Enriched : @Enriched C CC_Monoidal]，一个在自身上增广的笛卡尔闭类，具有 [eobj := obj[C]、[ehom x y := y^x]、[eid := internal_id] 和 [ecompose := internal_compose]；这三条律域都是以上单位律和结合律定理的 [exact]，因此增广本身没有增加任何方程内容。[Sets_Enriched] 对其进行了实例化。作为自身增广在 tree -- Construction/Enriched/Ab.v 中并不是新的概念 [Enriched_Ab_itself] 是一个 [@Enriched Ab Ab_Monoidal] ——因此它所填补的空白更狭窄：没有笛卡尔闭类在自身上被增广。[CC_Monoidal] 也不是第一个，而且它看起来像第一个的原因是一个别名（ALIAS）：Construction/Enriched/Two.v 的 [Enriched_of_TwoPreorder] 是一个 [@Enriched _2 Two_Monoidal]，而 [Two_Monoidal] 在 [eq_refl] 通过 Structure/Monoidal/Cartesian.v 中的普通定义是 [@CC_Monoidal _2 Two_Cartesian Two_Terminal]，因此对 [CC_Monoidal] 的名字搜索——返回18个文件——看不到它。该实例不是自我增强：它的 [eobj] 是 [tpre_carrier P]，一个任意的预序承载体，而不是 [_2] 的对象。[Set] 条款，在其测量等级下。Mac Lane 要求该变换“在集合上与函数复合一致”。[Sets] 是该库的集合等价类类别，其指数 [c^b] 是 ≈-保持映射的集合等价类，所以该声明在集合等价类的态射上是逐点的，并且 [sets_internal_compose] 在 [eq_refl] 上成立：[internal_compose (g, f)] 在 [t] 的值是 [g (f t)]。[sets_internal_id] 也是如此。在 [Sets] 的整个态射级别上，等级下降到 [≈]（[sets_internal_compose_morphism]），原因可以定位而不是猜测：两个底层函数是相同的项（[sets_internal_compose_underlying]，[eq_refl]），所以不同的正是两边重建的 [proper_morphism] 证书。严格形式在探针中被驳斥并固定。一个工程危险，再次遇到并比捐赠者声明的更严格地测量。Structure/Cartesian/Closed/Natural.v 记录了在自身的 [Program Definition] 内展开函子对象动作会让 [Program] 将 [product_obj] 的未解析实例参数推迟为一个义务，而 Lib/Foundation.v 的 [Unset Transparent Obligations] 会使其变得不透明，然后 [fobj] 在没有任何操作下进行转换。因此，这里的五个函子首先将它们的对象和箭头动作作为普通定义给出。边界比“任何内联对象动作”更窄：单独的内联 [exponent_obj] 确实会减少，而被推迟的是 [product_obj] —— 即 [Cartesian] 实例 —— 这是捐赠者的归属，而不是此处重新得出的事实。探针机检查的是分离，即作为通过控制的仅指数函子，以及作为转换负面的积函子。四个 [*_fobj] 示例记录了五个已发运函子中有四个会约简；[ComposeB] 也会约简，但这是通过测量而不是通过示例固定的。UNIVERSES，既不在 BINDER 也不在 BLOCK。每个常量都在 BINDER 中超出了 [C : Category@{u u0 u0}] -- 同态带证明的识别 --，而没有一个约束 BLOCK 包含宇宙方程：单独读取这些块不会报告任何识别。这是继承的，而单独 [Cartesian] 已经强制它，其探针将其标记为针对类别、其对象、其同态集、其恒等式及其组成的可形成性负面，所有这些都在同态和证明中严格分开。没有任何带字界限的 [Set] 出现在任何 binder 或 block 中。公理。这个文件的所有71个常量——53个命名声明加上五个函子及其扩展的18个[Program]义务（没有任何源扫描可以看到）——都报告“在全局上下文中封闭”。[Sets_Closed]在没有公理的情况下获得其指数（Instance/Coq.v记录了这种对比），因此[Set]条款没有任何成本；承载公理的[Coq_Closed]（Instance/Coq.v）在此处故意未被实例化，并且不需要Instance/Coq.v。先前技术，已测量。[internal_compose]、[internal_comp]、[comp_internal] 和 [internal_id] 在树的其他任何地方都没有出现过，也没有其他声明具有 [c^b × b^a] 形状的对象动作。Structure/Closed.v 确实声明了一个 [hom_compose] 字段，但整个 [Class Closed] 块位于 Structure/Closed.v 中由日期延期标记打开并关闭的注释内，并且其形状是 CURRIED Eilenberg-Kelly 形式，[[y, z] ~> [[x, y], [x, z] ]，这不是本练习所要求的形状；此处未被恢复。确实存在的，并且是被消耗而非重建的是 Structure/Cartesian/Closed/Natural.v 的 [ihom f h := curry (h ∘ eval ∘ second f)] ——内部同构自身的二变量作用，即 [fmap[InternalHomFunctor] ] 在 [eq_refl] ——以及 [ihom_id]、[ihom_comp] 和 [opobj] / [oparr] 对逆变槽的读数。未交付。没有 [ComposeB] 的 coend 或 end，因此没有任何东西表明 cowedge 是通用的；没有 [EnrichedFunctor]，也没有将 [CCC_Enriched] 与 Construction/Enriched.v 的 [Category_is_Enriched_over_Set] 进行比较；[ExpBase] 与 Structure/Cartesian/Closed/Adjunction.v 的 [Exp_Functor] 之间没有关系，这需要该模块——请参见函子前的注释，了解从其源读取的内容以及需要它的代价；没有单体闭一般化，因此此处没有内容是在 Structure/Monoidal/Closed.v 上陈述的；除了 [Sets] 外，在笛卡尔闭类别中没有见证；并且没有任何东西注册为 [Instance]。
*)

Section Composition.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(* * ** The composition and identity morphisms / * ** 复合和恒等态射 *)

(*
 Mac Lane's c^b × b^a ~> c^a: transpose the double evaluation. 

 --------
 Mac Lane 的 c^b × b^a ~> c^a：转置双重求值。
*)
Definition internal_compose {a b c : C} : c^b × b^a ~> c^a :=
  curry (eval ∘ second eval ∘ to prod_assoc).

(*
 [unfork] and [cat] both call [simpl]; without this they would unfold
 [internal_compose] into its transpose and destroy every rewrite below.
 Same discipline as Structure/Cartesian/Closed/Natural.v for [ihom]. 

 --------
 [unfork] 和 [cat] 都调用 [simpl]；没有这个它们会将 [internal_compose] 展开为其转置并破坏下面的每个重写。与 Structure/Cartesian/Closed/Natural.v 中的 [ihom] 使用相同的规则。
*)
Arguments internal_compose : simpl never.

(*
 The three exponentials, pinned in their [exponent_obj] spelling, so that
 the argument order of the header's notation note is machine-checked. 

 --------
 这三个指数，在它们的 [exponent_obj] 拼写中固定，使得标题符号注释的参数顺序经过机器检查。
*)
Example internal_compose_obj (a b c : C) :
  (c^b × b^a ~{C}~> c^a)
    = (exponent_obj b c × exponent_obj a b ~{C}~> exponent_obj a c)
  := eq_refl.

(** ** The beta laws / ** 测试版法律 *)

Lemma uncurry_internal_compose_raw {a b c : C} :
  uncurry (@internal_compose a b c)
    ≈ eval ∘ second eval ∘ to prod_assoc.
Proof. apply uncurry_curry. Qed.

Lemma eval_internal_compose {a b c : C} :
  eval ∘ first (@internal_compose a b c)
    ≈ eval ∘ second eval ∘ to prod_assoc.
Proof. rewrite eval_first; apply uncurry_internal_compose_raw. Qed.

(*
 The workhorse.  For any pair of generalized elements [h] and [k] of the
 two exponentials, the transpose of the composite is “apply [h] to the
 result of applying [k]”.  Every law below is an instance. 

 --------
 干活的主力。对于两个指数的任意一对广义元素 [h] 和 [k]，复合的转置是“将 [h] 应用于应用 [k] 的结果”。下面的每条定律都是一个实例。
*)
Lemma uncurry_internal_compose {w a b c : C}
      (h : w ~> c^b) (k : w ~> b^a) :
  uncurry (internal_compose ∘ (h △ k))
    ≈ uncurry h ∘ (exl △ uncurry k).
Proof.
  rewrite uncurry_comp.
  rewrite uncurry_internal_compose_raw.
  rewrite <- !eval_first.
  unfork.
Qed.

(*
 The rewrite rule that strips one [internal_compose] from inside an
 evaluation: this is [eval_curry] at the transpose, followed by the fork
 algebra of [prod_assoc].  Associativity, both naturality squares and
 dinaturality are this rule and its two companions applied a bounded
 number of times and then [exl_fork]/[exr_fork] to [reflexivity]. 

 --------
 重写规则会从一个求值中去掉一个 [internal_compose]：这是转置处的 [eval_curry]，随后是 [prod_assoc] 的分叉代数。结合性，包括自然性平方和二自然性，是该规则及其两个伴随规则应用有限次，然后将 [exl_fork] / [exr_fork] 转为 [reflexivity]。
*)
Lemma eval_internal_compose_fork {w a b c : C}
      (g : w ~> c^b × b^a) (k : w ~> a) :
  eval ∘ ((internal_compose ∘ g) △ k)
    ≈ eval ∘ ((exl ∘ g) △ (eval ∘ ((exr ∘ g) △ k))).
Proof.
  unfold internal_compose.
  rewrite eval_curry.
  rewrite <- !comp_assoc.
  unfork.
Qed.

Context `{@Terminal C}.

(*
 Mac Lane's identity arrow of the internal category: 1 ~> x^x. 

 --------
 Mac Lane 的内部范畴恒等箭头：1 ~> x^x。
*)
Definition internal_id {x : C} : 1 ~> x^x := curry exr.

Arguments internal_id : simpl never.

Lemma uncurry_internal_id {x : C} :
  uncurry (@internal_id x) ≈ exr.
Proof. apply uncurry_curry. Qed.

Lemma eval_internal_id_fork {w x : C} (g : w ~> 1) (k : w ~> x) :
  eval ∘ ((internal_id ∘ g) △ k) ≈ k.
Proof.
  unfold internal_id.
  rewrite eval_curry.
  now rewrite exr_fork.
Qed.

(** ** The unit laws / ** 单位法 *)

(*
 [1 × y^x ~> y^x]: composing with the internal identity on the left is
 the projection, which is [to unit_left] over [CC_Monoidal]. 

 --------
 [1 × y^x ~> y^x] ：在左边与内部恒等映射进行组合是投影，它是 [to unit_left] 在 [CC_Monoidal] 上的投影。
*)
Theorem internal_compose_id_left {x y : C} :
  @internal_compose x y y ∘ split internal_id id ≈ exr.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite uncurry_internal_compose.
  rewrite (uncurry_comp (@internal_id y) exl).
  rewrite uncurry_internal_id.
  rewrite <- !eval_first.
  unfork.
  rewrite !exr_fork.
  now rewrite id_left.
Qed.

(*
 [y^x × 1 ~> y^x]: composing with the internal identity on the right is
 the other projection, which is [to unit_right] over [CC_Monoidal]. 

 --------
 [y^x × 1 ~> y^x]：在右侧与内部身份组成就是另一个投影，即 [to unit_right] 在 [CC_Monoidal] 上的投影。
*)
Theorem internal_compose_id_right {x y : C} :
  @internal_compose x x y ∘ split id internal_id ≈ exl.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite uncurry_internal_compose.
  rewrite (uncurry_comp (@internal_id x) exr).
  rewrite uncurry_internal_id.
  rewrite <- !eval_first.
  unfork.
  rewrite !exr_fork.
  cat.
Qed.

(** ** Associativity / ** 结合律 *)

(*
 The two projections of the associator, in the composed shape the fork
 algebra below actually meets. 

 --------
 结合子的两个投影，在组合形状中，下面的叉代数实际上是相交的。
*)
Lemma exl_prod_assoc_r {v a b c : C} (h : v ~> (a × b) × c) :
  exl ∘ (to (@prod_assoc C _ a b c) ∘ h) ≈ exl ∘ (exl ∘ h).
Proof. rewrite !comp_assoc; simpl; now rewrite exl_fork. Qed.

Lemma exr_prod_assoc_r {v a b c : C} (h : v ~> (a × b) × c) :
  exr ∘ (to (@prod_assoc C _ a b c) ∘ h)
    ≈ (exr ∘ (exl ∘ h)) △ (exr ∘ h).
Proof.
  rewrite comp_assoc; simpl; rewrite exr_fork.
  rewrite <- fork_comp.
  now rewrite !comp_assoc.
Qed.

(*
 Mac Lane's “prove it (like composition) associative”, in exactly the
 shape [ecompose_assoc] demands: the associator on the right. 

 --------
 麦克莱恩的“证明它（像组合一样）是结合的”，严格按照形状 [ecompose_assoc] 要求：右侧的结合子。
*)
Theorem internal_compose_assoc {x y z w : C} :
  @internal_compose x y w ∘ split internal_compose id
    ≈ @internal_compose x z w ∘ split id internal_compose
        ∘ to prod_assoc.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite <- !eval_first.
  unfold first.
  rewrite <- !comp_assoc.
  rewrite !eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !id_left.
  rewrite !exl_prod_assoc_r, !exr_prod_assoc_r.
  rewrite !eval_internal_compose_fork.
  rewrite !exl_fork, !exr_fork.
  reflexivity.
Qed.

(** ** Naturality in [a] and in [c] / ** [a] 和 [c] 的自然性 *)

(*
 The companion of [eval_internal_compose_fork] for the internal hom's own
 action: it strips one [ihom] from inside an evaluation. 

 --------
 [eval_internal_compose_fork] 的伴随，用于内部 Hom 自身的作用：它会从一次求值中剥离一个 [ihom]。
*)
Lemma eval_ihom_fork {v a b c d : C} (f : b ~> a) (h : c ~> d)
      (g : v ~> c^a) (m : v ~> b) :
  eval ∘ ((ihom f h ∘ g) △ m) ≈ h ∘ (eval ∘ (g △ (f ∘ m))).
Proof.
  unfold ihom.
  rewrite eval_curry.
  rewrite <- !comp_assoc.
  unfork.
Qed.

(*
 Naturality in the base [c], at fixed [a] and [b]: both sides are
 morphisms [c^b × b^a ~> c'^a]. 

 --------
 在固定 [a] 和 [b] 的情况下，基 [c] 中的自然性：两边都是 [c^b × b^a ~> c'^a] 的态射。
*)
Theorem internal_compose_natural_c {a b c c' : C} (g : c ~> c') :
  ihom id g ∘ @internal_compose a b c
    ≈ @internal_compose a b c' ∘ first (ihom id g).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite eval_internal_compose_fork.
  rewrite eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(*
 Naturality in the exponent [a], at fixed [b] and [c]: the variable is
 CONTRAVARIANT, so the square runs against an arrow [f : a' ~> a] and
 both sides are morphisms [c^b × b^a ~> c^a']. 

 --------
 指数 [a] 的自然性，在固定 [b] 和 [c] 时：变量是逆变的，因此平方与箭头 [f : a' ~> a] 相反，并且双方都是态射 [c^b × b^a ~> c^a']。
*)
Theorem internal_compose_natural_a {a a' b c : C} (f : a' ~> a) :
  ihom f id ∘ @internal_compose a b c
    ≈ @internal_compose a' b c ∘ second (ihom f id).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first, second.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite eval_internal_compose_fork.
  rewrite eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(*
   * ** The two naturality squares, packaged as transformations

   The four functors below are built here rather than imported, and the
   reason is NOT that nothing else would serve.  Two in-tree candidates
   do: Functor/Bifunctor/Partial.v's [Partial_l] and [Partial_r], applied to Functor/Hom/Internal.v's
   [InternalHomFunctor C], give functors agreeing with [ExpBase] and
   [ExpExp] on BOTH actions at [eq_refl] -- object and arrow alike, with
   no residue, only the whole functor RECORD refused because [Program]
   rebuilds the law fields (all measured out of tree).  The marginal
   closure cost is ONE module, 43 to 44: [InternalHomFunctor] is already
   inside the 43, and only Functor/Bifunctor/Partial.v is new.
   They are not adopted here only because doing so is a refactor rather
   than a correction; nothing below depends on the hand-built forms
   beyond their being these functors.  A THIRD candidate,
   Structure/Cartesian/Closed/Adjunction.v's [Exp_Functor S], fits
   worse: read off its source its object action is [ExpBase]'s but its
   arrow action is [curry (f ∘ eval)] where [ihom id f] is
   [curry (f ∘ eval ∘ second id)], and requiring that module takes
   this file's transitive closure from 43 modules to 47 (measured).
   Neither of the two SOURCE functors has an in-tree counterpart: no
   declaration elsewhere has an object action of the shape [c^b × b^a],
   the other products of two exponentials in tree being the isomorphism
   statements [y^x × z^x] and [x^y × x^z], where the two exponentials
   share their exponent or their base rather than meeting base to
   exponent. 

   --------
   * ** 两个自然性方格，封装为变换下面的四个函子是在这里构建的，而不是导入的，原因不是因为没有其他选择。树内有两个候选项可以使用：Functor/Bifunctor/Partial.v 的 [Partial_l] 和 [Partial_r]，应用于 Functor/Hom/Internal.v 的 [InternalHomFunctor C]，会得到与 [ExpBase] 和 [ExpExp] 在 [eq_refl] 上两种作用（对象和箭头）完全一致的函子——没有残余，只有整个函子 RECORD 被拒绝，因为 [Program] 重新建立了定律字段（这些都是树外测量的）。边际关闭成本是一个模块，43 到 44：[InternalHomFunctor] 已经在 43 内，而 Functor/Bifunctor/Partial.v 是新的。它们在这里没有被采用仅仅因为这样做是重构而不是修正；下面的内容除了需要这些手工构建的函子本身之外，并不依赖它们。第三个候选者，
   Structure/Cartesian/Closed/Adjunction.v 的 [Exp_Functor S]，适配得更差：从其源代码可以读出，其对象作用是 [ExpBase]，但箭头作用是 [curry (f ∘ eval)]，其中 [ihom id f] 是 [curry (f ∘ eval ∘ second id)]，并且要求该模块从 43 个模块的传递闭包增加到 47 个（经测量）。这两个 SOURCE 函子都没有树内对应项：在其他地方没有声明具有 [c^b × b^a] 形状的对象作用，树中两个指数的其他乘积是同构声明 [y^x × z^x] 和 [x^y × x^z]，其中两个指数共享其指数或其底，而不是将底与指数相连。
*)

(*
 The object and arrow actions are given as ordinary definitions and only
 then assembled into functor records.  Elaborating them inside the
 [Program Definition] would not do: [Program] defers the unresolved
 [Cartesian] instance argument of [product_obj] into an OBLIGATION,
 which Lib/Foundation.v's [Unset Transparent Obligations] makes opaque,
 and the resulting [fobj] then converts with nothing -- in particular
 not with the endpoints of [internal_compose].  This is the hazard
 Structure/Cartesian/Closed/Natural.v records; it was met again
 here, and the probe measures its boundary: an inline [exponent_obj]
 alone reduces, an inline [product_obj] does not. 

 --------
 对象和箭头操作被作为普通定义给出，然后才组装到函子记录中。在 [Program Definition] 内部展开它们是不可行的：[Program] 将 [product_obj] 的未解决的 [Cartesian] 实例参数延迟为一个义务（OBLIGATION），而 Lib/Foundation.v 的 [Unset Transparent Obligations] 将其设为不透明，结果 [fobj] 随后无法进行任何转换——特别是无法与 [internal_compose] 的端点进行转换。这就是 Structure/Cartesian/Closed/Natural.v 记录的风险；这里再次遇到它，探测测量它的边界：只有内联的 [exponent_obj] 能够化简，内联的 [product_obj] 则不能。
*)

Definition expBase_obj (a c : C) : C := c^a.

Definition expBase_map (a : C) {c c' : C} (g : c ~> c') :
  expBase_obj a c ~> expBase_obj a c' := ihom id g.

Program Definition ExpBase (a : C) : C ⟶ C := {|
  fobj := expBase_obj a;
  fmap := fun _ _ g => expBase_map a g
|}.
Next Obligation.
  proper; unfold expBase_map, expBase_obj; now rewrites.
Qed.
Next Obligation. unfold expBase_map, expBase_obj; apply ihom_id. Qed.
Next Obligation.
  unfold expBase_map, expBase_obj.
  rewrite ihom_comp; now rewrite id_left.
Qed.

Definition composeSrcC_obj (a b c : C) : C := c^b × b^a.

Definition composeSrcC_map (a b : C) {c c' : C} (g : c ~> c') :
  composeSrcC_obj a b c ~> composeSrcC_obj a b c' :=
  first (ihom id g).

Program Definition ComposeSrcC (a b : C) : C ⟶ C := {|
  fobj := composeSrcC_obj a b;
  fmap := fun _ _ g => composeSrcC_map a b g
|}.
Next Obligation.
  proper; unfold composeSrcC_map, composeSrcC_obj; now rewrites.
Qed.
Next Obligation.
  unfold composeSrcC_map, composeSrcC_obj.
  rewrite ihom_id; apply first_id.
Qed.
Next Obligation.
  unfold composeSrcC_map, composeSrcC_obj.
  rewrite <- first_comp, ihom_comp; now rewrite id_left.
Qed.

Definition expExp_obj (c : C) (a : C^op) : C := c^(opobj a).

Definition expExp_map (c : C) {a a' : C^op} (f : a ~> a') :
  expExp_obj c a ~> expExp_obj c a' := ihom (oparr f) id.

Program Definition ExpExp (c : C) : C^op ⟶ C := {|
  fobj := expExp_obj c;
  fmap := fun _ _ f => expExp_map c f
|}.
Next Obligation.
  proper; unfold expExp_map, expExp_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold expExp_map, expExp_obj, oparr; apply ihom_id.
Qed.
Next Obligation.
  unfold expExp_map, expExp_obj, oparr.
  rewrite ihom_comp; now rewrite id_left.
Qed.

Definition composeSrcA_obj (b c : C) (a : C^op) : C :=
  c^b × b^(opobj a).

Definition composeSrcA_map (b c : C) {a a' : C^op} (f : a ~> a') :
  composeSrcA_obj b c a ~> composeSrcA_obj b c a' :=
  second (ihom (oparr f) id).

Program Definition ComposeSrcA (b c : C) : C^op ⟶ C := {|
  fobj := composeSrcA_obj b c;
  fmap := fun _ _ f => composeSrcA_map b c f
|}.
Next Obligation.
  proper; unfold composeSrcA_map, composeSrcA_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold composeSrcA_map, composeSrcA_obj, oparr.
  rewrite ihom_id; apply second_id.
Qed.
Next Obligation.
  unfold composeSrcA_map, composeSrcA_obj, oparr.
  rewrite <- second_comp, ihom_comp; now rewrite id_left.
Qed.

(*
 The four object actions read back on the nose, which is what makes the
 two transformations typecheck with no transport -- and what the hazard
 above would have destroyed. 

 --------
 四个对象操作正好按原样读取，这正是使得这两种变换在没有传输的情况下类型检查通过的原因——也是上面提到的危险本会破坏的原因。
*)
Example expBase_fobj (a c : C) : fobj[ExpBase a] c = c^a := eq_refl.

Example composeSrcC_fobj (a b c : C) :
  fobj[ComposeSrcC a b] c = c^b × b^a := eq_refl.

Example expExp_fobj (c : C) (a : C^op) :
  fobj[ExpExp c] a = c^(opobj a) := eq_refl.

Example composeSrcA_fobj (b c : C) (a : C^op) :
  fobj[ComposeSrcA b c] a = c^b × b^(opobj a) := eq_refl.

(* Mac Lane's “natural transformation”, in [c]. / Mac Lane 的“自然变换”，在 [c] 中。 *)
Definition compose_Transform_c (a b : C) :
  ComposeSrcC a b ⟹ ExpBase a :=
  @Build_Transform' C C (ComposeSrcC a b) (ExpBase a)
    (fun c => @internal_compose a b c)
    (fun c c' g => @internal_compose_natural_c a b c c' g).

(* And in [a], where the variable is contravariant. / 并且在 [a] 中，变量是逆变的。 *)
Definition compose_Transform_a (b c : C) :
  ComposeSrcA b c ⟹ ExpExp c :=
  @Build_Transform' (C^op) C (ComposeSrcA b c) (ExpExp c)
    (fun a => @internal_compose a b c)
    (fun a a' f => @internal_compose_natural_a a a' b c f).

(*
 The components ARE [internal_compose], on the nose. 

 --------
 组件是 [internal_compose]，正是如此。
*)
Example compose_Transform_c_component (a b c : C) :
  transform (compose_Transform_c a b) c = @internal_compose a b c
  := eq_refl.

Example compose_Transform_a_component (a b c : C) :
  transform (compose_Transform_a b c) a = @internal_compose a b c
  := eq_refl.

(** ** Dinaturality in [b] / ** 在 [b] 中的自然性 *)

(*
 [b] occurs contravariantly on the left of the product and covariantly on
 the right, so there is no functor of [b] for a natural transformation in
 [b] to run between.  What holds is the COWEDGE condition: for
 [f : b1 ~> b2] the two routes out of [c^b2 × b1^a] into [c^a] agree. 

 --------
 [b] 在乘积的左边是逆变的，在右边是协变的，因此没有 [b] 的函子可以让 [b] 中的自然变换运行。成立的是 COWEDGE 条件：对于 [f : b1 ~> b2]，从 [c^b2 × b1^a] 到 [c^a] 的两条路径是一致的。
*)
Theorem internal_compose_dinatural {a c b1 b2 : C} (f : b1 ~> b2) :
  @internal_compose a b1 c ∘ split (ihom f id) id
    ≈ @internal_compose a b2 c ∘ split id (ihom id f).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first, split.
  rewrite <- !comp_assoc.
  rewrite !eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !id_left.
  rewrite !eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(*
 The mixed-variance bifunctor the dinaturality is dinaturality FOR:
 [ComposeB a c (b1, b2) = c^b1 × b2^a], contravariant in the first slot
 and covariant in the second.  Object and arrow actions first, per the
 hazard recorded above. 

 --------
 混合方差双函子中的自然变性是针对以下的自然变性：
 [ComposeB a c (b1, b2) = c^b1 × b2^a]，在第一个位置上是逆变的，
 在第二个位置上是协变的。先进行对象和箭头作用，如上文记录的风险所示。
*)

Definition composeB_obj (a c : C) (p : C^op ∏ C) : C :=
  c^(opobj (fst p)) × (snd p)^a.

Definition composeB_map (a c : C) {x y : C^op ∏ C} (m : x ~> y) :
  composeB_obj a c x ~> composeB_obj a c y :=
  split (ihom (oparr (fst m)) id) (ihom id (snd m)).

Program Definition ComposeB (a c : C) : C^op ∏ C ⟶ C := {|
  fobj := composeB_obj a c;
  fmap := fun _ _ m => composeB_map a c m
|}.
Next Obligation.
  proper; unfold composeB_map, composeB_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold composeB_map, composeB_obj, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold composeB_map, composeB_obj, oparr; simpl.
  now rewrite split_comp, !ihom_comp, !id_left.
Qed.

(*
 The constant family [internal_compose] satisfies the tree's own covariant
 cowedge condition (Structure/Coend.v) at that bifunctor, with apex
 [c^a]. 

 --------
 常量族 [internal_compose] 在该双函子处满足树自身的协变共楔条件（Structure/Coend.v），顶点为 [c^a]。
*)
Definition internal_compose_Cowedge_cond (a c : C) :
  @Cowedge_cond C C (ComposeB a c) (c^a)
    (fun x => @internal_compose a x c).
Proof.
  intros x y f.
  simpl; unfold composeB_map, composeB_obj, oparr, op; simpl.
  rewrite !ihom_id.
  apply internal_compose_dinatural.
Defined.

(*
 ... and therefore assembles into an inhabitant of [Wedge]. 

 --------
 ... 因此组装成 [Wedge] 的一个居民。
*)
Definition internal_compose_Wedge (a c : C) :=
  @covariant_cowedge C C (ComposeB a c) (c^a)
    (fun x => @internal_compose a x c)
    (internal_compose_Cowedge_cond a c).

(* * ** A cartesian closed category is enriched over itself / * ** 一个笛卡尔闭类是自身增强的 *)

(*
 The four identifications the enrichment rests on, re-checked here: over
 [CC_Monoidal] the tensor of morphisms IS [split], the associator IS the
 cartesian one, and the two unitors ARE the projections. 

 --------
 这里重新检查一下丰富所依赖的四个确认：在 [CC_Monoidal] 上，态射的张量是 [split]，结合子是笛卡尔的，而两个单位子是投影。
*)
Example assoc_bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example assoc_tensor_is_prod {x y z : C} :
  to (@tensor_assoc C CC_Monoidal x y z) = to (@prod_assoc C _ x y z)
  := eq_refl.

Example assoc_unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Example assoc_unit_right_is_exl {x : C} :
  to (@unit_right C CC_Monoidal x) = exl := eq_refl.

(*
 The payoff: [C] enriched over itself, with hom-objects the
 exponentials. 

 --------
 回报：[C] 自身上得到丰富化，具有指数的同对象。
*)
Program Definition CCC_Enriched : @Enriched C CC_Monoidal := {|
  eobj := obj[C];
  ehom := fun x y => y^x;
  eid := fun x => internal_id;
  ecompose := fun x y z => internal_compose
|}.
Next Obligation. exact internal_compose_id_left. Qed.
Next Obligation. exact internal_compose_id_right. Qed.
Next Obligation. exact internal_compose_assoc. Qed.

End Composition.

(* * * Agreement with composition of functions in [Set] / * * 与 [Set] 中函数组合的一致性 *)

(*
 Mac Lane's remaining clause: the transformation “agrees in Set with
 composition of functions”.  [Sets] is this library's category of
 setoids, whose exponential [c^b] is the setoid of ≈-respecting maps, so
 the statement is pointwise on setoid morphisms. 

 --------
 Mac Lane 剩下的结论：这个变换“在 Set 中与函数的组合一致”。[Sets] 是这个库的集合同态范畴，其指数 [c^b] 是 ≈-保持映射的集合同态，因此该陈述在集合同态映射上是逐点成立的。
*)

Example sets_internal_compose (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) (t : a) :
  @internal_compose Sets _ _ a b c (g, f) t = g (f t) := eq_refl.

(*
 At the level of whole morphisms of [Sets] the identification is [≈] and
 not Leibniz, and the cause is located rather than guessed: the two
 UNDERLYING FUNCTIONS are the same term (next [Example]), so what differs
 is exactly the rebuilt [proper_morphism] certificate.  The strict form is
 refuted and pinned in Test/ProbeComposition391.v. 

 --------
 在 [Sets] 的整体态射层面上，这种识别是 [≈]，而不是莱布尼茨，其原因是明确定位的，而不是猜测的：两个基本函数是相同的项（接下来的 [Example]），因此不同的恰好是重建的 [proper_morphism] 证书。严格形式在 Test/ProbeComposition391.v 中被驳斥并固定。
*)
Example sets_internal_compose_underlying (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (fun t : a => @internal_compose Sets _ _ a b c (g, f) t)
    = (fun t : a => (g ∘[Sets] f) t) := eq_refl.

Example sets_internal_compose_morphism (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  @internal_compose Sets _ _ a b c (g, f) ≈[Sets] g ∘ f.
Proof. intro t; reflexivity. Qed.

(*
 And the identity: [internal_id] is the identity function of [Sets]. 

 --------
 而且恒等式：[internal_id] 是 [Sets] 的恒等函数。
*)
Example sets_internal_id (x : Sets)
        (u : @terminal_obj Sets Sets_Terminal) (t : x) :
  @internal_id Sets _ _ Sets_Terminal x u t = t := eq_refl.

(*
 [Sets] is therefore enriched over itself, with hom-objects the function
 setoids. 

 --------
 因此，[Sets] 在自身上是增广的，同态对象是函数集族。
*)
Definition Sets_Enriched : @Enriched Sets CC_Monoidal := CCC_Enriched.
