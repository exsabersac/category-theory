Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Orthogonality.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Regular.
Require Import Category.Instance.Two.

Generalizable All Variables.

(* * * Projective and injective objects / * * 投射对象和单射对象 *)

(*
 Mac Lane §V.4 Definitions 3 and 4 (book p. 118; maclane:V.4:def3,
 maclane:V.4:def4); Awodey §2.4's prose definition of a projective object
 (awodey:2.4:def-projective).
 nLab: https://ncatlab.org/nlab/show/projective+object
 https://ncatlab.org/nlab/show/injective+object

 BACKGROUND.  An object p is projective when every arrow out of it lifts
 through every epimorphism — equivalently, when the covariant hom-functor
 C(p, −) carries epis to epis, i.e. to surjections of hom-setoids — and q
 is injective when every arrow into it extends along every monomorphism,
 the dual.  These are the two lifting notions under homological algebra
 (enough projectives, resolutions), none of which is built here.

 STALE PREMISES, RE-MEASURED.
 - "No projectivity or injectivity notion exists": TRUE (0 declarations
 matching Projective/Injective; the issue's own occurrence counts are
 off — 'projective' occurs in 9 lines of 6 [.v] files, all prose:
 projective limits (Structure/Limit.v, Instance/Sets/
 InverseLimit.v), a free module (Instance/Mod/Free.v),
 projective geometry (Construction/Opposite.v), the
 projective tensor product of Banach spaces (Structure/Closed.v) and
 "enough projectives" (Structure/Abelian.v, the one line about this
 file's notion); and 'injective' in 437 lines of 100 files, all but
 one the SETOID-MAP notion — Lib/Setoid.v [injective],
 Instance/Sets.v [injectivity_is_monic], Theory/Concrete/
 Morphisms.v [concrete_injective_monic],
 Adjunction/LeftInverse.v [InjectiveOnObjects], … — the
 exception being Structure/
 Abelian.v's "injective resolutions", prose about the categorical
 notion).  (An earlier revision glossed the nine as "limits or modules"
 and the 437 as all setoid-map; corrected to the measured lists.)
 - "No lifting property beyond Theory/Orthogonality.v": PARTIAL.
 [Orthogonal e m] (unique filler, two arrows, over [≈]) is also what
 Structure/Factorization/StrongEpi.v's [strong_lift] and
 Theory/Morphisms/Stability.v's cobase change route through; every
 lifting statement in the tree carries the uniqueness clause, so the
 lift-EXISTENCE notion was indeed absent.
 - "No lemma about hom-functors preserving epis": TRUE (Theory/
 Functor.v has REFLECTION, [faithful_reflects_monic] and
 [faithful_reflects_epic]; Functor/Hom/Limit.v has preservation of
 limits, not of epis).
 - What the issue does not mention and this file rests on:
 Instance/Sets.v [surjectivity_is_epic : (∀ b, ∃ a, h a ≈ b) ↔
 Epic h], BOTH directions, constructively
 ([surjective_implies_epic] and [epic_implies_surjective], the
 latter through that file's cokernel-pair probe), which makes
 both halves of the hom-functor characterization provable.
 - "As data or as an ∃-statement, disclosing which": in this library
 there is no choice.  [∃] IS [sigT] (Lib/Foundation.v rebinds
 [exists] and defines [∃] from it), and a Prop-valued existential
 over [≈] cannot even be stated, [≈] on morphisms being Type-valued
 (probe N6).  The lift is data, written [∃ h, g ∘ h ≈ f] as
 Structure/Pullback.v's [ump_pullbacks] and Theory/Morphisms.v's
 witnesses already are.

 WHAT IS DELIVERED (45 named constants plus 3 [Program] obligations,
 every one closed under the global context).
 (1) [Projective p] — a [Class] like [Epic]/[Monic], one field
 [projective_lift {b c} (g : b ~> c) (He : Epic g) (f : p ~> c) : ∃ h
 : p ~> b, g ∘ h ≈ f] — with the accessors [proj_lift] /
 [proj_lift_comm].
 (2) [Injective C] as a NOTATION for [@Projective (C^op)] (with the
 [@Injective C] form), the idiom of Structure/Initial.v and
 Structure/Cocartesian.v; covariant accessors
 [injective_extend m Hm f : ∃ h : b ~> q, h ∘ m ≈ f] (through
 Theory/Morphisms/Duality.v's [op_Epic_of_Monic] — [Monic] in
 C and [Epic] in [C^op] are DISTINCT records, probe N4-N5, though
 the objects and homs of the duality convert), [inj_extend],
 [inj_extend_comm]; readbacks [inj_is_op_proj] and
 [inj_stmt_readback] (the C-facing statement IS the [C^op] one) at
 [eq_refl].
 (3) THE HOM-FUNCTOR CHARACTERIZATION, both directions.
 [proj_is_hom_surjectivity] ([eq_refl]: "surjections of hom-setoids"
 is the definition unfolded, [fmap[[Hom p ,─]] g h = g ∘ h] being
 [hom_fmap_is_postcomp]), [projective_hom_surjective] (Lib/Setoid.v's
 [surjective] class), [projective_hom_epic] (Epic in Sets, by
 [surjective_implies_epic]), [hom_epic_projective] (the converse, by
 [epic_implies_surjective]), and the issue's pinned
 [projective_iff_hom_preserves_epi].  Dually [cohom_is_op_hom]
 ([eq_refl]: [[Hom ─, q]] over C IS [[Hom q ,─]] over [C^op]),
 [injective_cohom_epic], [cohom_epic_injective],
 [injective_iff_cohom_preserves_mono] — each a [:=] of the
 projective form at [C^op] plus one Duality.v bridge.
 (4) ORTHOGONALITY.  [ortho_lift_exists] (Theory/Orthogonality.v's
 [Orthogonal] with its uniqueness clause dropped, one projection);
 and, over an [Initial] object — the arrow whose left lifting
 property is at issue is [zero : 0 ~> p] — [ortho_zero_Projective]
 (orthogonality against every epi gives projectivity) and
 [Projective_ortho_weak] (projectivity gives a filler, not
 necessarily unique, for every such square).  No implication
 between projectivity and [StrongEpi] is claimed: the latter lifts a
 MORPHISM against monos, a different class.
 (5) CLOSURE.  [Retraction_Projective] and [Section_Projective]
 (Theory/Morphisms.v's [Section]/[Retraction]; the tree has
 no [Retract] name), [Coprod_Projective] (binary, through
 [merge_comp] / [merge_inl_inr]), [IndexedCoprod_Projective]
 (Structure/Limit/Coproduct.v's [IsIndexedCoproduct], the lift at
 each index chosen by [icoprod_desc] — the case that shows why the
 lift must be data), and the duals [Prod_Injective],
 [Section_Injective], [IndexedProd_Injective], [terminal_obj_Injective]
 as [:=] instantiations at [C^op] with the readbacks
 [op_op_Cartesian : @Cartesian C = @Cocartesian (C^op)] and
 [op_Coprod_is_product] at [eq_refl].
 (6) WITNESSES.  [initial_obj_Projective] (the lift is [zero]),
 [Retraction_lifts] and [every_epi_splits_Projective] (a split epi
 lifts everything), [Sets_Leibniz_Projective : ∀ T : Type, Projective
 (LeibnizSetoid T)] — every setoid whose [≈] is Leibniz equality is
 projective in Sets, CONSTRUCTIVELY: the preimage is
 [epic_implies_surjective]'s and respectfulness is free on a Leibniz
 carrier — and, on the walking arrow, [TwoX_Projective] (through
 [two_X_initial : @Initial _2]) with [TwoY_not_Projective]
 ([TwoXY] is epic, [id[TwoY]] has no lift, Instance/Two.v's
 [TwoHom_Y_X_absurd] closes it), packaged as
 [two_projective_not_all]: the property is neither vacuous nor
 universal in one category.  The three witnesses' lifts COMPUTE
 (probe readbacks at [eq_refl]).
 (7) THE PRICE OF "EVERY OBJECT IS PROJECTIVE".
 [Projective_codomain_splits] (the identity lifts, so the epi
 splits), [all_projective_iff_every_epi_splits], and over Sets
 [sets_all_projective_entails_splitting] and
 [sets_all_projective_entails_LEM : (∀ p : Sets, Projective p) → ∀ P
 : Prop, P + (P → False)] through Instance/Sets/Regular.v's
 [BlanketSplitting] and its Diaconescu-shaped [blanket_splitting_
 entails_LEM] — "every set is projective" decides every proposition,
 so Awodey's examples of that shape (awodey:2.4:example15,
 awodey:2:ex3) are not discharged here and cannot be constructively.

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 45
 constants).
 - [Projective@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] →
 Type@{max(u,u0)}] with an EMPTY constraint block: C's hom and proof
 levels are identified, and every constant of the file is over a
 [Category@{a b b}] binder with NO equation in its block.  The
 identification is [Epic]'s (and [Monic]'s), not this development's:
 probe N1-N3 refuse [@Epic Cu x y f], [@Monic Cu x y f] and
 [@Projective Cu x] alike under [Constraint vh < vp], with [Cu], its
 hom type and [f] accepted as controls.  Object levels are only
 bounded.
 - The hom characterizations sit at the usual Sets shape:
 [projective_iff_hom_preserves_epi@{u u0 u1 u2 u3}] over [C :
 Category@{u3 u2 u2}] with [u2 < u1] (Sets' object level strictly
 above C's hom level), [injective_iff_cohom_preserves_mono] likewise;
 [IndexedCoprod_Projective] carries [A : Type@{u}] with [u <= u3],
 bounded and identified with nothing; [Sets_Leibniz_Projective@{h p}]
 carries [p < h] ([epic_implies_surjective@{h p}]'s own shape, with
 [A B : SetoidObject@{p p}]) and the stdlib bounds [eq_ind], [eq_ind_r],
 [eq_rect_r], [prod_rect] and [Logic_lemmas.equality] from
 [LeibnizSetoid]'s Leibniz setoid and the surjectivity donor.
 - [Set] appears in exactly five blocks or types, all inherited: the
 four [_2] witnesses ([two_X_initial], [TwoX_Projective],
 [TwoY_not_Projective], [two_projective_not_all]) because [_2]
 (Instance/Two.v) is declared bare with a [Set]-valued hom, and
 [sets_all_projective_entails_LEM@{u}] with [Set < u], from
 [bool_setoid_object] inside [blanket_splitting_entails_LEM] — which
 STRENGTHENS the reading: the entailment holds already at [Set]-sized
 carriers.  No other constant names [Set].

 COUNTS AND CONVENTIONS.
 - 45 [.glob] declaration heads (40 [def], 3 [prf], the class [rec] and
 its [proj]) plus 3 [Program] obligations ([LeibnizSetoid] 1,
 [two_X_initial] 2), all "Closed under the global context", zero
 [Axioms:] lines; the gate carries the 45 heads, fully qualified, the
 issue's [Projective], [Injective]'s carrier [injective_extend] and
 [projective_iff_hom_preserves_epi] among them ([Injective] itself is
 a notation, not a constant).
 - Twelve [Defined], each flipped to [Qed] alone in a copy of the file
 with the probe recompiled against it: THREE are load-bearing —
 [Retraction_lifts], [initial_obj_Projective],
 [Sets_Leibniz_Projective], whose lifts the probe reads back at
 [eq_refl] — and the other nine (the hom characterizations, the
 orthogonality and closure constants) compile with the probe unchanged
 and stay transparent because they produce lifts.  Two [Qed]
 ([TwoY_not_Projective], a negation; [two_X_initial]'s uniqueness
 obligation).
 - Closure 34 files excluding self: Structure/Limit/Coproduct.v costs 8
 at the margin (the indexed case), Functor/Hom.v 3, Theory/Morphisms/
 Duality.v 2, Instance/Sets/Regular.v 1, Instance/Two.v 1,
 Structure/Cocartesian.v 1, Theory/Orthogonality.v 1, the other ten
 [Require]s 0.  [[Hom p ,─]] is used directly rather than
 Functor/Hom/Limit.v's [HomFrom], which would add 23 files for the
 same functor (an earlier revision said 12; measured 34 → 57).
 [two_X_initial : @Initial _2] DUPLICATES
 Theory/Equivalence/Strict.v's [Two_Initial], whose [Require]
 would add 17 files; the consolidation of both into Instance/Two.v is
 surfaced for the maintainer, not done.  Name collisions: [Projective]
 occurs as a word in Structure/Limit.v's prose ("projective limit"),
 not as a declaration; every other name has 0 occurrences elsewhere.
 - NAME HAZARD, RECORDED.  The [@Injective C] notation claims the lexer
 token [@Injective], as Structure/Initial.v's [@Initial C] and
 Structure/Cocartesian.v's [@Cocartesian C] claim theirs: no constant
 whose name begins with [Injective], [Initial] or [Cocartesian] can be
 written with an [@] prefix while those notations are in scope (probe
 N7-N8; the tree's [InjectiveOnObjects] is currently never written with
 [@]; [@Terminal…] and [@Coproduct…] ARE accepted — no such notation
 exists — an earlier revision listed them as blocked).  The names below
 avoid every blocked prefix.
 - Test/ProbeProjective429.v mirrors the [Require] list and carries 9
 refutation commands (1 instrument + N1-N3 UNIVERSE + N4 CONVERSION +
 N5-N6 TYPING + N7-N8 PARSING), each stripped one at a time in a copy
 of the whole file and each beside its accepted controls; ten
 [eq_refl] readbacks (an earlier revision said eleven, counting the N4
 negative's own [eq_refl]); guard coverage 28 identifier tokens inside
 the refutations / 22 also named outside, comments stripped, with six
 exhaustive exceptions (the keyword, a binder, the three refuted
 declarations' names, the absent name); rename-simulated 5/5 over the
 library names the negatives use ([Projective], [Epic], [Monic],
 [op_Epic_of_Monic], [Category]; module paths excluded), every first
 break on a positive line — the two parsing negatives concern a lexer
 token, so renaming their probe-local placeholders is uninformative
 and is not counted.  [make todo] grows by those 9 lines only (2237 →
 2246 over f86ebdbe, master 1de68608 with #428), so the issue's "adds
 no new hits" box is not met as written; disclosed.  (An earlier
 revision of the probe
 wrote the Prelude's [ex] as [Corelib.Init.Logic.ex], which Coq
 8.19/8.20 do not know — their prelude is [Coq.] — and the Nix source
 builds stopped there; the unqualified name is used now, and the guard
 figure moved from 31/25 to the 28/22 above with it.)

 NOT DELIVERED.
 - Enough projectives, projective or injective resolutions, injective
 hulls, Baer's criterion (Structure/Abelian.v frames these as
 background prose; nothing built).
 - Free modules are projective (Instance/Mod/Free.v records the
 absence; it needs that module's machinery).
 - Any relation between projectivity and [StrongEpi] (different
 classes; none holds without further hypotheses).
 - "Every object of Sets is projective" — refuted as a constructive
 goal by (7); Awodey's examples of that shape stay open.
 - Anything registered as an [Instance]: [Projective] is a class, but
 no instance is declared, so nothing becomes globally resolvable.
 - No edit to Theory/Morphisms.v, Theory/Morphisms/Duality.v,
 Theory/Orthogonality.v, Instance/Sets.v, Instance/Sets/Regular.v or
 Instance/Two.v. 

 --------
 Mac Lane §V.4 定义 3 和 4（书页 118；maclane:V.4:def3, maclane:V.4:def4）；Awodey §2.4 对投射对象的散文定义（awodey:2.4:def-projective）。
 nLab: https://ncatlab.org/nlab/show/projective+object
 https://ncatlab.org/nlab/show/injective+object

 背景。 当一个对象 p 对每个射出它的箭头都能通过每个满射提升时，它是投射的——等价地，当协变 Hom 函子 C(p, −) 将满射映射为满射，即映射到 Hom 集合的满射时——而对象 q 是单射的，当每个指向它的箭头都能沿每个单射延拓时，这为对偶。这些是同调代数下的两种提升概念（有足够的投射对象、分解解析），这里没有构建其中任何一个。陈旧场所，重新测量。- “不存在投射性或单射性概念”：正确（没有匹配 Projective/Injective 的声明；该问题自身的出现次数也不对——'projective' 出现在 6 个 [.v] 文件的 9 行中，全部为正文：投射极限（Structure/Limit.v, Instance/Sets/InverseLimit.v）、自由模（Instance/Mod/Free.v）、射影几何（Construction/Opposite.v）、Banach 空间的射影张量积（Structure/Closed.v）以及“足够的投射对象”（Structure/Abelian.v，本文件概念的一行）；而 'injective' 出现在 100 个文件的 437 行中，除一例外全部为 SETOID-MAP 的概念——Lib/Setoid.v  [injective]、Instance/Sets.v  [injectivity_is_monic]、Theory/Concrete/Morphisms.v  [concrete_injective_monic]、Adjunction/LeftInverse.v  [InjectiveOnObjects] …… ——例外的是 Structure/Abelian.v 的“单射分解”，关于范畴概念的散文。(早期版本将数字九释为“极限或模”，将437释为全setoid-映射；现已更正为测量列表。)
 - “没有超过 Theory/Orthogonality.v 的提升性质”：部分正确。[Orthogonal e m]（唯一填充，两箭头，在 [≈] 之上）也是 Structure/Factorization/StrongEpi.v 的 [strong_lift] 和 Theory/Morphisms/Stability.v 的余基变换途径；树中的每个提升陈述都带有唯一性条款，因此 lift-EXISTENCE 的概念确实缺失。
 - “没有关于Hom函子保持满射的引理”：正确（Theory/Functor.v 有 REFLECTION、[faithful_reflects_monic] 和 [faithful_reflects_epic]；Functor/Hom/Limit.v 具有保持极限的性质，而非保持满射）。- 问题未提及且此文件依赖于的内容：
 Instance/Sets.v [surjectivity_is_epic : (∀ b, ∃ a, h a ≈ b) ↔
 Epic h]，两个方向，构造性地
 ([surjective_implies_epic] 和 [epic_implies_surjective]，后者通过该文件的余核对探针)，这使得同态函子特征的两半可被证明。 - “作为数据或作为 ∃-语句，披露哪一个”：在该库中没有选择。[∃] 是 [sigT]（Lib/Foundation.v 重新绑定
 [exists] 并从中定义 [∃]），并且无法甚至陈述关于 [≈] 的命题型存在量词，[≈] 在态射上是类型型的
 (探针 N6)。提升是数据，写作 [∃ h, g ∘ h ≈ f]，正如 Structure/Pullback.v 的 [ump_pullbacks] 和 Theory/Morphisms.v 的
 witnesses 已经是的那样。交付内容是什么（45 个命名常量加上 3 个 [Program] 义务，每一个都在全局上下文中封闭）。(1) [Projective p] — 一个类似 [Epic] / [Monic] 的 [Class]，一个字段 [projective_lift {b c} (g : b ~> c) (He : Epic g) (f : p ~> c) : ∃ h : p ~> b, g ∘ h ≈ f] — 具有访问器 [proj_lift] / [proj_lift_comm]。(2) [Injective C] 作为 [@Projective (C^op)]（带有 [@Injective C] 形式）的符号表示；Structure/Initial.v 和 Structure/Cocartesian.v 的惯用法；协变访问器 [injective_extend m Hm f : ∃ h : b ~> q, h ∘ m ≈ f]（通过 Theory/Morphisms/Duality.v 的 [op_Epic_of_Monic] —— 在 C 中的 [Monic] 和在 [C^op] 中的 [Epic] 是不同的记录，探测 N4-N5，尽管对偶的对象和同态会转换）、[inj_extend]、[inj_extend_comm]；回读 [inj_is_op_proj] 和 [inj_stmt_readback]（面向 C 的语句即 [C^op]）在 [eq_refl]。 (3) HOM-函子刻画，两个方向。[proj_is_hom_surjectivity]  ( [eq_refl]：“同类集合的满射”定义展开, [fmap[[Hom p ,─] ] g h = g ∘ h] 即 [hom_fmap_is_postcomp] ), [projective_hom_surjective] （Lib/Setoid.v 的 [surjective] 类), [projective_hom_epic] （在集合中为 Epic, 由 [surjective_implies_epic] ), [hom_epic_projective] （反之, 由 [epic_implies_surjective] ), 以及该问题固定的 [projective_iff_hom_preserves_epi] 。相反地 [cohom_is_op_hom] ( [eq_refl] : [[Hom ─, q] ] 在 C 上是 [[Hom q ,─] ] 在 [C^op] ), [injective_cohom_epic] , [cohom_epic_injective] , [injective_iff_cohom_preserves_mono] — 每个都是在 [C^op] 的投射形式加上一个 Duality.v 桥的 [:=] 。(4) 正交性。[ortho_lift_exists]（Theory/Orthogonality.v 中的 [Orthogonal]，去掉了它的唯一性条款，一个投影）；并且，对于一个 [Initial] 对象——其左提升性质有争议的箭头是 [zero : 0 ~> p]——[ortho_zero_Projective]（对每个上射的正交性给出可投影性）以及 [Projective_ortho_weak]（可投影性为每个这样的方形提供一个填充，不一定唯一）。没有声称可投影性与 [StrongEpi] 之间有任何蕴涵关系：后者针对单射提升一个态射，这是不同的类别。（5）闭包。[Retraction_Projective] 和 [Section_Projective]（Theory/Morphisms.v 的 [Section] / [Retraction]；该树没有 [Retract] 名称），[Coprod_Projective]（二元，通过 [merge_comp] / [merge_inl_inr]），[IndexedCoprod_Projective]（Structure/Limit/Coproduct.v 的 [IsIndexedCoproduct]，每个索引的提升由 [icoprod_desc] 选择——该情况显示了为什么提升必须是数据），以及对偶 [Prod_Injective]、[Section_Injective]、[IndexedProd_Injective]、[terminal_obj_Injective] 作为 [:=] 在 [C^op] 上的实例化，并在 [eq_refl] 处有 [op_op_Cartesian : @Cartesian C = @Cocartesian (C^op)] 和 [op_Coprod_is_product] 的回读。(6) 见证者。[initial_obj_Projective]（提升是 [zero]），[Retraction_lifts] 和 [every_epi_splits_Projective]（一个分裂上同态提升一切），[Sets_Leibniz_Projective：∀ T：类型, Projective (LeibnizSetoid T)] — 每个其 [≈] 是 Leibniz 等式的集合同构在集合中都是射影的，构造性地：原像是 [epic_implies_surjective]，并且对 Leibniz 承载的尊重性是自由的 — 在行箭头上，[TwoX_Projective]（通过 [two_X_initial : @Initial _2]）与 [TwoY_not_Projective]（[TwoXY] 是满射, [id[TwoY]] 没有提升，Instance/Two.v 的 [TwoHom_Y_X_absurd] 完成它），打包为 [two_projective_not_all]：该属性在一个范畴中既非空也非普遍。三个见证者的提升会计算（在 [eq_refl] 处探测回读）。(7) “每个对象都是射影的” 的代价。[Projective_codomain_splits] （同一性提升，因此正射分裂），[all_projective_iff_every_epi_splits]，以及在集合上 [sets_all_projective_entails_splitting] 和 [sets_all_projective_entails_LEM ：(∀ p : Sets, Projective p) → ∀ P : Prop, P + (P → False)] 通过 Instance/Sets/Regular.v 的 [BlanketSplitting] 及其 Diaconescu 形式的 [blanket_splitting_entails_LEM] — “每个集合都是投射的”决定每个命题，所以 Awodey 那些形状的例子（awodey:2.4:example15, awodey:2:ex3）在这里没有解决，且在构造上无法实现。宇宙（通过 [About] 在所有 45 个常量上根据 [Set Printing Universes] 测量）。- [Projective@{u u0} : ∀ {C : Category@{u u0 u0}}, obj[C] → 类型@{max(u,u0)}] 带有一个空的约束块：C 的同态和证明级别已被识别，并且文件中的每个常量都在一个 [Category@{a b b}] 绑定器之上，其块中没有方程。该识别是 [Epic]（和 [Monic]）的，而不是此开发的：探针 N1-N3 拒绝 [@Epic Cu x y f]、[@Monic Cu x y f] 和 [@Projective Cu x] 在 [Constraint vh < vp] 下，同时接受 [Cu]，它的同态类型和 [f] 作为控制。对象级别仅有限定。- 同态表征位于常见的 Sets 形状：
 [projective_iff_hom_preserves_epi@{u u0 u1 u2 u3}] 在 [C : Category@{u3 u2 u2}] 上方，ZW122WZZ （Sets 的对象层次严格高于 C 的 Hom 层次），ZW123WZZ 同样如此；
 [IndexedCoprod_Projective] 承载 [A : Type@{u}] 与 [u <= u3]，
 有界且未与任何东西标识；ZW127WZZ
 承载 [p < h]（ZW129WZZ 自身的形状，带 ZW130WZZ）及 stdlib 界 [eq_ind]、ZW132WZZ、
 ZW133WZZ、ZW134WZZ 和 ZW135WZZ 来自 [LeibnizSetoid] 的 Leibniz 集合等价类和满射供给者。- [Set] 出现在恰好五个块或类型中，全部为继承：四个 [_2] 的见证（[two_X_initial]、[TwoX_Projective]、[TwoY_not_Projective]、[two_projective_not_all]），因为 [_2]（Instance/Two.v）以 [Set] 值的 hom 声明裸露，以及 [sets_all_projective_entails_LEM@{u}] 与 [Set < u]，来自 [bool_setoid_object] 内的 [blanket_splitting_entails_LEM] — 这加强了该读法：该蕴涵已经在 [Set] 大小的承载者上成立。没有其他常量名称 [Set]。计数和约定。- 45个[.glob]声明头（40个[def]，3个[prf]，类[rec]及其[proj]）加上3个[Program]义务（[LeibnizSetoid] 1，[two_X_initial] 2），所有均“在全局上下文下封闭”，零[Axioms:]行；该网关携带45个头，完全限定，该问题的[Projective]、[Injective]的承载器[injective_extend]及其中的[projective_iff_hom_preserves_epi]（[Injective]本身是符号，而不是常量）。- 十二个 [Defined]，每一个在文件的副本中单独翻转为 [Qed]，并针对其重新编译探针：三个是承重的——[Retraction_lifts]、[initial_obj_Projective]、[Sets_Leibniz_Projective]，其升值由探针读取为 [eq_refl]——其余九个（同态特性、正交性和闭包常数）在探针不变的情况下编译，并保持透明因为它们产生升值。两个 [Qed]（[TwoY_not_Projective]，一个否定；[two_X_initial] 的唯一性义务）。 - 不包括自身的闭包34个文件：Structure/Limit/Coproduct.v 在边际（索引情况下）成本为8，Functor/Hom.v 3，Theory/Morphisms/Duality.v 2，Instance/Sets/Regular.v 1，Instance/Two.v 1，Structure/Cocartesian.v 1，Theory/Orthogonality.v 1，其余十个 [Require] 为0。[[Hom p ,─] 被直接使用，而不是 Functor/Hom/Limit.v 的 [HomFrom]，这将为同一个函子增加 23 个文件（早期版本说是 12 个；测量为 34 → 57）。[two_X_initial : @Initial _2] 重复了 Theory/Equivalence/Strict.v 的 [Two_Initial]，其 [Require] 将增加 17 个文件；两者合并到 Instance/Two.v 是为维护者显示的，而没有实际完成。命名冲突：[Projective] 出现在 Structure/Limit.v 的文本中（"projective limit"），不是声明；其他所有名字在其他地方出现次数为 0。- 名称风险，已记录。[@Injective C] 表示法声明了词法分析器标记 [@Injective]，就像 Structure/Initial.v 的 [@Initial C] 和 Structure/Cocartesian.v 的 [@Cocartesian C] 声明它们的那样：没有名称以 [Injective]、[Initial] 或 [Cocartesian] 开头的常量可以在这些表示法作用域内使用 [@] 前缀书写（探测 N7-N8；该树的 [InjectiveOnObjects] 当前从未用 [@] 写出；[@Terminal…] 和 [@Coproduct…] 被接受——不存在这样的表示法——早期版本将它们列为阻止）。下面的名称避免了每一个被阻止的前缀。- Test/ProbeProjective429.v 反映了 [Require] 列表，并包含 9 个反驳命令（1 个工具 + N1-N3 UNIVERSE + N4 CONVERSION + N5-N6 TYPING + N7-N8 PARSING），每个命令在整个文件的副本中逐一剥离，并且每个旁边都有其接受的控制；十个 [eq_refl] 读回（早期修订版说是十一，计算 N4 否定本身的 [eq_refl]）；在反驳内部涵盖 28 个标识符标记 / 外部也命名了 22 个，已去掉评论，有六个详尽的例外（关键字、一个绑定器、三个被反驳声明的名字、缺失的名字）；重命名模拟覆盖否定使用的库名 5/5（[Projective]、[Epic]、[Monic]、[op_Epic_of_Monic]、[Category]；不包括模块路径），每个首次中断都在正行上e——这两个解析否定涉及一个词法分析器符号，因此重命名它们的探针本地占位符没有信息量，也不计入统计。[make todo] 仅通过那 9 行增长（2237 → 2246 在 f86ebdbe 上，master 1de68608 带 #428），所以按照原文写法，问题的“没有新增命中”框并未满足；已披露。（探针的早期修订版本将 Prelude 的 [ex] 写成了 [Corelib.Init.Logic.ex]，Coq 8.19/8.20 不认识——它们的 prelude 是 [Coq.]——并且 Nix 源代码的构建在此停止；现在使用了未限定的名称，守护图也随之从 31/25 移动到上面的 28/22。）未交付。 - 足够的投射模、投射或内射分解、内射壳、Baer判据（Structure/Abelian.v 将这些作为背景散文处理；没有构建任何内容）。 - 自由模是投射的（Instance/Mod/Free.v 记录了缺失；它需要该模的机制）。 - 投射性与 [StrongEpi] 之间的任何关系（不同类型；没有进一步假设下都不成立）。 - “Sets 的每个对象都是投射的”——作为构造性目标被 (7) 反驳；Awodey 的那个形状的例子仍然开放。 - 任何登记为 [Instance] : [Projective] 的内容都是一个类，但没有声明任何实例，因此没有任何东西可以全局可解。- 不对 Theory/Morphisms.v、Theory/Morphisms/Duality.v、Theory/Orthogonality.v、Instance/Sets.v、Instance/Sets/Regular.v 或 Instance/Two.v 进行任何编辑。
*)

Class Projective {C : Category} (p : C) := {
  projective_lift {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) :
    ∃ h : p ~> b, g ∘ h ≈ f
}.

Definition proj_lift {C : Category} {p : C} `{P : @Projective C p}
  {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) : p ~> b :=
  `1 (projective_lift g He f).

Definition proj_lift_comm {C : Category} {p : C} `{P : @Projective C p}
  {b c : C} (g : b ~> c) (He : Epic g) (f : p ~> c) :
  g ∘ proj_lift g He f ≈ f :=
  `2 (projective_lift g He f).

Notation "'Injective' C" := (@Projective (C^op))
  (at level 9) : category_theory_scope.
Notation "@Injective C" := (@Projective (C^op))
  (at level 9) : category_theory_scope.

Definition injective_extend {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) :
  ∃ h : b ~> q, h ∘ m ≈ f :=
  @projective_lift (C^op) q Q b a m (op_Epic_of_Monic m Hm) f.

Definition inj_extend {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) : b ~> q :=
  `1 (injective_extend m Hm f).

Definition inj_extend_comm {C : Category} {q : C} `{Q : @Injective C q}
  {a b : C} (m : a ~> b) (Hm : Monic m) (f : a ~> q) :
  inj_extend m Hm f ∘ m ≈ f :=
  `2 (injective_extend m Hm f).

Example inj_is_op_proj {C : Category} (q : C) :
  @Injective C q = @Projective (C^op) q := eq_refl.

Example inj_stmt_readback {C : Category} {q a b : C} (m : a ~> b) (f : a ~> q) :
  (∃ h : b ~{C}~> q, h ∘[C] m ≈ f)
    = (∃ h : q ~{C^op}~> b, m ∘[C^op] h ≈ f) := eq_refl.

(* * ** The hom-functor characterization / * ** Hom函子刻画 *)

Example hom_fmap_is_postcomp {C : Category} (p : C) {b c : C} (g : b ~> c)
  (h : p ~> b) : fmap[[Hom p ,─]] g h = g ∘ h := eq_refl.

(* The "surjections of hom-setoids" reading is the DEFINITION unfolded: the lifting clause and the surjectivity of [fmap] agree at [eq_refl]. / “同态集合的满射”读法是展开的定义：提升条款和 [fmap] 的满射性在 [eq_refl] 处一致。 *)
Example proj_is_hom_surjectivity {C : Category} (p : C) {b c : C}
  (g : b ~> c) :
  (∀ f : p ~> c, ∃ h : p ~> b, fmap[[Hom p ,─]] g h ≈ f)
    = (∀ f : p ~> c, ∃ h : p ~> b, g ∘ h ≈ f) := eq_refl.

Definition projective_hom_surjective {C : Category} {p : C}
  (P : @Projective C p) {b c : C} (g : b ~> c) (He : Epic g) :
  surjective (fmap[[Hom p ,─]] g) :=
  {| surj := fun f => @projective_lift C p P b c g He f |}.

Theorem projective_hom_epic {C : Category} {p : C} (P : @Projective C p)
  {b c : C} (g : b ~> c) (He : Epic g) :
  @Epic Sets _ _ (fmap[[Hom p ,─]] g).
Proof.
  apply surjective_implies_epic.
  intro f.
  exact (@projective_lift C p P b c g He f).
Defined.

Theorem hom_epic_projective {C : Category} (p : C)
  (H : ∀ (b c : C) (g : b ~> c), Epic g → @Epic Sets _ _ (fmap[[Hom p ,─]] g)) :
  @Projective C p.
Proof.
  construct.
  exact (epic_implies_surjective (fmap[[Hom p ,─]] g) (H b c g He) f).
Defined.

Definition projective_iff_hom_preserves_epi {C : Category} (p : C) :
  @Projective C p
    ↔ (∀ (b c : C) (g : b ~> c), Epic g → @Epic Sets _ _ (fmap[[Hom p ,─]] g)) :=
  (fun P b c g He => @projective_hom_epic C p P b c g He,
   @hom_epic_projective C p).

(* The dual, at C^op: [Hom ─,q] over C IS [Hom q,─] over C^op, definitionally. / 在 C^op 上的对偶：在 C 上的 [Hom ─,q] 定义上是 C^op 上的 [Hom q,─]。 *)
Example cohom_is_op_hom {C : Category} (q : C) :
  @Curried_CoHom C q = @Curried_Hom (C^op) q := eq_refl.

Definition injective_cohom_epic {C : Category} {q : C} (Q : @Injective C q)
  {a b : C} (m : a ~> b) (Hm : Monic m) :
  @Epic Sets _ _ (fmap[[Hom ─, q]] m) :=
  @projective_hom_epic (C^op) q Q b a m (op_Epic_of_Monic m Hm).

Definition cohom_epic_injective {C : Category} (q : C)
  (H : ∀ (a b : C) (m : a ~> b), Monic m → @Epic Sets _ _ (fmap[[Hom ─, q]] m)) :
  @Injective C q :=
  @hom_epic_projective (C^op) q
    (fun b a m Hm => H a b m (@Monic_of_op_Epic C a b m Hm)).

Definition injective_iff_cohom_preserves_mono {C : Category} (q : C) :
  @Injective C q
    ↔ (∀ (a b : C) (m : a ~> b), Monic m →
         @Epic Sets _ _ (fmap[[Hom ─, q]] m)) :=
  (fun Q a b m Hm => @injective_cohom_epic C q Q a b m Hm,
   @cohom_epic_injective C q).

(* * ** Orthogonality: the unique-filler strengthening / * ** 正交性：独特填充物的增强 *)

Definition ortho_lift_exists {C : Category} {a b x y : C}
  (e : a ~> b) (m : x ~> y) (O : Orthogonal e m)
  {u : a ~> x} {v : b ~> y} (comm : m ∘ u ≈ v ∘ e) :
  ∃ d : b ~> x, (d ∘ e ≈ u) ∧ (m ∘ d ≈ v) :=
  (unique_obj (ortho_lift comm); unique_property (ortho_lift comm)).

Definition ortho_zero_Projective {C : Category} `{I : @Initial C} (p : C)
  (H : ∀ (b c : C) (g : b ~> c), Epic g → Orthogonal (zero (x:=p)) g) :
  @Projective C p.
Proof.
  construct.
  destruct (ortho_lift_exists _ _ (H b c g He) (u:=zero) (v:=f)
              (ltac:(apply zero_unique))) as [d [_ Hd]].
  exists d; exact Hd.
Defined.

Definition Projective_ortho_weak {C : Category} `{I : @Initial C} {p : C}
  (P : @Projective C p) {b c : C} (g : b ~> c) (He : Epic g)
  (u : @initial_obj C I ~> b) (v : p ~> c) (comm : g ∘ u ≈ v ∘ zero) :
  ∃ d : p ~> b, (d ∘ zero ≈ u) ∧ (g ∘ d ≈ v).
Proof.
  destruct (@projective_lift C p P b c g He v) as [d Hd].
  exists d; split; [ apply zero_unique | exact Hd ].
Defined.

(** ** Closure facts / ** 关闭事实 *)

Definition Retraction_Projective {C : Category} {p q : C} (r : p ~> q)
  (R : Retraction r) (P : @Projective C p) : @Projective C q.
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ r)) as [h Hh].
  exists (h ∘ retract).
  rewrite comp_assoc, Hh, <- comp_assoc, retract_comp; cat.
Defined.

Definition Section_Projective {C : Category} {p q : C} (s : q ~> p)
  (S : Section s) (P : @Projective C p) : @Projective C q.
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ section)) as [h Hh].
  exists (h ∘ s).
  rewrite comp_assoc, Hh, <- comp_assoc, section_comp; cat.
Defined.

Definition Coprod_Projective {C : Category} `{O : @Cocartesian C} {p q : C}
  (P : @Projective C p) (Q : @Projective C q) :
  @Projective C (@Coprod C O p q).
Proof.
  construct.
  destruct (@projective_lift C p P b c g He (f ∘ inl)) as [h1 H1].
  destruct (@projective_lift C q Q b c g He (f ∘ inr)) as [h2 H2].
  exists (h1 ▽ h2).
  rewrite <- merge_comp, H1, H2, merge_comp, merge_inl_inr; cat.
Defined.

Definition IndexedCoprod_Projective {C : Category} {A : Type} (fam : A → C)
  (s : C) (inj : ∀ a : A, fam a ~> s) (H : IsIndexedCoproduct fam s inj)
  (P : ∀ a : A, @Projective C (fam a)) : @Projective C s.
Proof.
  construct.
  pose (lifts := fun a : A =>
          @projective_lift C (fam a) (P a) b c g He (f ∘ inj a)).
  pose (D := @icoprod_desc C A fam s inj H b (fun a => `1 (lifts a))).
  pose (E := @icoprod_desc C A fam s inj H c (fun a => f ∘ inj a)).
  exists (unique_obj D).
  transitivity (unique_obj E).
  - symmetry; apply (uniqueness E).
    intro a.
    rewrite <- comp_assoc, (unique_property D a).
    exact (`2 (lifts a)).
  - apply (uniqueness E).
    intro a; reflexivity.
Defined.

(* * ** The injective duals, by instantiation at C^op / * ** 注射对偶，通过在 C^op 的实例化 *)

Example op_op_Cartesian {C : Category} : @Cartesian C = @Cocartesian (C^op) :=
  eq_refl.

Example op_Coprod_is_product {C : Category} `{O : @Cartesian C} (p q : C) :
  @Coprod (C^op) O p q = @product_obj C O p q := eq_refl.

Definition Prod_Injective {C : Category} `{O : @Cartesian C} {p q : C}
  (P : @Injective C p) (Q : @Injective C q) :
  @Injective C (@product_obj C O p q) :=
  @Coprod_Projective (C^op) O p q P Q.

Definition Section_Injective {C : Category} {p q : C} (s : q ~> p)
  (S : Section s) (P : @Injective C p) : @Injective C q :=
  @Retraction_Projective (C^op) p q s (op_Retraction_of_Section s S) P.

(*
 The hypothesis is stated in C's own vocabulary: [IsIndexedCoproduct] over
 [C^op] IS [IsIndexedProduct] over C (Structure/Limit/Coproduct.v). 

 --------
 假设是用 C 自己的词汇陈述的：[IsIndexedCoproduct] 在 [C^op] 上等于 [IsIndexedProduct] 在 C（Structure/Limit/Coproduct.v）。
*)
Definition IndexedProd_Injective {C : Category} {A : Type} (fam : A → C)
  (s : C) (proj : ∀ a : A, s ~> fam a)
  (H : @IsIndexedProduct C A fam s proj)
  (P : ∀ a : A, @Injective C (fam a)) : @Injective C s :=
  @IndexedCoprod_Projective (C^op) A fam s proj H P.

(** ** Witnesses / ** 证人 *)

Definition Retraction_lifts {C : Category} {p b c : C} (g : b ~> c)
  (R : Retraction g) (f : p ~> c) : ∃ h : p ~> b, g ∘ h ≈ f.
Proof.
  exists (retract ∘ f).
  rewrite comp_assoc, retract_comp; cat.
Defined.

Definition every_epi_splits_Projective {C : Category}
  (S : ∀ (b c : C) (g : b ~> c), Epic g → Retraction g) (p : C) :
  @Projective C p.
Proof.
  construct.
  exact (Retraction_lifts g (S b c g He) f).
Defined.

Definition initial_obj_Projective {C : Category} `{I : @Initial C} :
  @Projective C (@initial_obj C I).
Proof.
  construct.
  exists zero.
  apply zero_unique.
Defined.

Definition terminal_obj_Injective {C : Category} `{T : @Terminal C} :
  @Injective C (@terminal_obj C T) :=
  @initial_obj_Projective (C^op) T.

Program Definition LeibnizSetoid@{o p} (T : Type@{o}) : SetoidObject@{o p} :=
  {| carrier := T; is_setoid := {| equiv := @eq T |} |}.

Definition Sets_Leibniz_Projective@{h p} (T : Type@{p}) :
  @Projective Sets@{p h} (LeibnizSetoid@{p p} T).
Proof.
  construct.
  unshelve eexists.
  - refine {| morphism :=
                fun t => `1 (epic_implies_surjective@{h p} g He (f t)) |}.
    now intros t t' Ht; rewrite Ht.
  - intro t; simpl.
    exact (`2 (epic_implies_surjective@{h p} g He (f t))).
Defined.

Lemma TwoY_not_Projective : @Projective _2 TwoY → False.
Proof.
  intro P.
  exact (TwoHom_Y_X_absurd
           (`1 (@projective_lift _2 TwoY P TwoX TwoY TwoXY TwoXY_epic id))).
Qed.

Program Definition two_X_initial : @Initial _2 := {| terminal_obj := TwoX |}.
Next Obligation. destruct x; [ exact TwoIdX | exact TwoXY ]. Defined.
Next Obligation. apply Two_thin. Qed.

Definition TwoX_Projective : @Projective _2 TwoX :=
  @initial_obj_Projective _2 two_X_initial.

(*
 Projectivity is not a vacuous property of _2: it holds at TwoX and not
 at TwoY. 

 --------
 投射性并不是 _2 的空洞属性：它在 TwoX 上成立，而在 TwoY 上不成立。
*)
Definition two_projective_not_all :
  @Projective _2 TwoX * (@Projective _2 TwoY → False) :=
  (TwoX_Projective, TwoY_not_Projective).

(* * ** The price of "every object is projective" / * ** “每个对象的价格是投影的” *)

(*
 In any category, projectivity of the codomain of an epi splits it: take
 the identity as the map to lift. 

 --------
 在任何范畴中，满射的上同域的射影性使其可分裂：取恒等映射作为要提升的映射。
*)
Definition Projective_codomain_splits {C : Category} {b c : C} (g : b ~> c)
  (P : @Projective C c) (He : Epic g) : Retraction g :=
  {| retract      := `1 (@projective_lift C c P b c g He id)
   ; retract_comp := `2 (@projective_lift C c P b c g He id) |}.

Definition all_projective_iff_every_epi_splits {C : Category} :
  (∀ p : C, @Projective C p)
    ↔ (∀ (b c : C) (g : b ~> c), Epic g → Retraction g) :=
  (fun HP b c g He => Projective_codomain_splits g (HP c) He,
   fun HS => fun p => @every_epi_splits_Projective C HS p).

(*
 Over [Sets] that principle is not merely unavailable: it DECIDES EVERY
 PROPOSITION.  Instance/Sets/Regular.v proves [BlanketSplitting → LEM]
 axiom-free by a Diaconescu-shaped countermodel; "every setoid is
 projective" implies [BlanketSplitting] in one line. 

 --------
 在 [Sets] 上，这一原理不仅仅是不可用的：它决定了每一个命题。Instance/Sets/Regular.v 通过一个 Diaconescu 形的反例模型证明了 [BlanketSplitting → LEM] 无公理；“每个集合化对象都是投射的”在一行中就暗示了 [BlanketSplitting]。
*)
Definition sets_all_projective_entails_splitting :
  (∀ p : @obj Sets, @Projective Sets p) → BlanketSplitting :=
  fun HP A B a0 f E => Projective_codomain_splits f (HP B) E.

Definition sets_all_projective_entails_LEM :
  (∀ p : @obj Sets, @Projective Sets p) → ∀ P : Prop, (P + (P → False))%type :=
  fun HP => blanket_splitting_entails_LEM
              (sets_all_projective_entails_splitting HP).

