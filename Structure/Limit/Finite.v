Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

Open Scope category_scope.

(* * * Finite index categories and finite limits / * * 有限指数范畴与有限极限 *)

(*
 Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.2
 Definition 1 and Corollary 1 (book p. 113); Awodey, Category Theory,
 §5.4 Definition 5.18 and the running definition of “all finite limits”
 (printed pp. 109/111), §5.6 (printed p. 116); Fong and Spivak, Seven
 Sketches in Compositionality, §6.2.4 (printed pp. 191-192, Definition
 6.30); Riehl, Category Theory in Context, 2nd ed., §3.5 (printed p. 115,
 Theorem 3.5.17).

 A FINITE limit is a limit over a finite index category, and the theorem
 is Mac Lane's Corollary 1: a terminal object, binary products and
 equalizers give every finite limit.  This file supplies the finiteness
 predicate the tree never had, states finite (co)completeness over it,
 proves the corollary by CONSUMING the enumeration through
 Structure/Limit/FromProducts.v's engine, and proves the converse with
 the surrogate packages Structure/Topos.v and Structure/Regular.v carry.

 WHAT “FINITE” IS HERE.  Riehl's and Seven Sketches' reading — finitely
 many MORPHISMS — as DATA: [FiniteCategory J] carries a size [fc_size], an
 enumeration [fc_arr : Fin.t fc_size → ArrowIx J] into FromProducts.v's
 arrow index (a pair of objects with an arrow between them), and a
 coverage [fc_cover] returning, for every arrow [f], an index whose entry
 HITS [f]: [ArrowHit a f] is two Leibniz endpoint equations and the
 transported arrow [≈ f] (Construction/Quotient.v's [hom_cast]).  Three
 consequences of that shape are the point.  (i) The hit witness is
 TYPE-valued because FromProducts.v's [Gen] is an [Inductive … : Type] and
 [Generates] quantifies over it: [fc_Generates] destructs the witness and
 feeds [gen_equiv]/[gen_idx], which a [Prop]-valued coverage could not do
 (large elimination) — which is exactly why the unregistered
 Structure/Limit/Preservation/Shapes.v's [FiniteShape] is NOT consumed here
 and is disclosed instead: its object coverage [fs_objs_all] is a
 [Prop]-valued [List.In], and its arrow coverage [fs_homs_all] is a [sigT]
 (Type-valued, so it does eliminate into [Type]) whose membership
 component is again a [Prop]-valued [List.In], from which no [Fin.t] index
 is recoverable — an earlier draft called the whole coverage “[List.In] in
 [Prop]”, which a fess audit refuted for the arrow half.
 (ii) “Finitely many” is UP TO [≈], the only reading a setoid supports,
 and the enumeration is a RETRACTION, not a bijection: one arrow may be
 hit by several indices, so [fc_size] is an upper bound on the number of
 arrows and no cardinality is claimed.  (iii) Objects are not enumerated
 separately: an object is recovered from the index hitting its identity
 arrow, [fc_obj_idx x := `1 (fc_cover (id[x]))] with retraction
 [fc_obj_rt], which is Seven Sketches' footnote that finitely many
 morphisms force finitely many objects —
 [finite_morphisms_implies_finite_objects : FiniteCategory J →
 FiniteObjects J], a lemma rather than a second field.  Finiteness is
 self-dual ([FiniteCategory_op], the same index with endpoints swapped),
 and no choice principle appears anywhere: every [∃] is a [sigT].

 THE ENGINE IS A PRODUCT OVER A RETRACT.  The corollary needs the product
 of [F] over the OBJECTS of [J], but the enumeration indexes ARROWS.  So
 Section RetractProduct proves, over an arbitrary category, that a product
 over an index [A] together with ONE equalizer — of the identity against
 the canonical idempotent [rp_r := ⟨ cast ∘ proj (idx (down a)) ⟩_a] — is a
 product over any retract [B] of [A] (maps [down : A → B], [idx : B → A],
 [rt : down (idx b) = b]); nothing in it is about finiteness, and the
 chosen-structure form [retract_product]/[retract_product_ump] under
 [HasEqualizers] is what the corollary applies at [A := Fin.t fc_size],
 [B := obj J], [down := fc_dom], [idx := fc_obj_idx].

 THE COROLLARY CONSUMES THE ENUMERATION.  In Section FiniteLimit, under
 [HasFiniteProducts C] (Structure/Limit/Product/Finite.v, #335's fold of
 binary products) and [HasEqualizers C]: [fl_P0] is #335's product of
 [F ∘ fc_dom] over [Fin.t fc_size]; [fl_P] is the retract product of [F]
 over the objects; [fl_Q] is the product of [F ∘ fc_cod] over the arrow
 index; [fl_s]/[fl_t] are the two tuplings (the projection at the domain,
 and [fmap[F] (fc_arrow i)] after it); [fl_eq] their equalizer; and
 [fl_cone]/[fl_limiting] are #416's [pe_cone]/[pe_limiting] at the
 generating family [fc_arrow] with [fc_Generates] discharging the
 coverage.  So [finite_limit : Limit F] is built from THREE finite
 products and TWO equalizers — [fl_P0] and [fl_Q] indexed by
 [Fin.t (fc_size HJ)], the retract product [fl_P] indexed by [obj J] and
 itself built from a [Fin.t]-indexed product plus the retract equalizer,
 then [fl_eq] — the reviewer's check that the predicate is consumed
 rather than placeholdered — with [finite_limit_apex] and
 [finite_limit_leg] reading the apex and
 the legs back at [eq_refl].  [finitely_complete_from_generators
 (T : Terminal C) (CP : Cartesian C) (HEq : HasEqualizers C)] (the pinned
 name) is that at [Cartesian_Terminal_HasFiniteProducts], and
 [finitely_complete_from_finite_products] the [HasFiniteProducts] form.
 The dual [finitely_cocomplete_from_generators] is the primal at [C^op]
 through [HasEqualizers_op_of_HasCoequalizers], [FiniteCategory_op] and
 [Opposite_Functor], a [:=] with no tactic.

 RIEHL 3.5.17 AND THE CONVERSE.  [finitely_complete_of_pullbacks_terminal
 : HasPullbacks C → Terminal C → FinitelyComplete C] and its dual are the
 corollary composed with Structure/Pullback/Reduction.v's two reductions.
 The converse is proved shape by shape: the terminal object is the limit
 of the empty diagram over [EmptyShape := DiscreteCat False]
 ([FinitelyComplete_Terminal]); pullbacks are limits over [Roof^op] read
 through Structure/Pullback/Limit.v's [Pullback_to_Universal]
 ([FinitelyComplete_HasPullbacks]); products and equalizers follow by
 Reduction.v; and [FinitelyComplete_iff_pullbacks_terminal] packages the
 biconditional, its dual [FinitelyCocomplete_iff_pushouts_initial]
 obtained by reading the primal at [C^op] ([FinitelyCocomplete_Initial],
 [FinitelyCocomplete_HasPushouts]).  The surrogate packages are thereby
 THEOREMS: Structure/Regular.v's terminal-plus-pullbacks clause and
 Structure/Topos.v's [ElementaryTopos] fields yield [FinitelyComplete]
 (the topos instantiation is Test/ProbeFinite417.v's
 [topos_FinitelyComplete]), and both headers now say so.

 UNIVERSES, measured off BOTH binder and block (Set Printing Universes on
 every constant).  [FiniteCategory@{u u0 u1} : Category@{u u0 u0} →
 Type@{u1}] identifies the shape's hom and proof universes in its BINDER;
 that is INHERITED from FromProducts.v's [ArrowIx], which is refused alone
 at a shape whose hom is declared strictly below its proof universe with
 [x ~> y] and [id[x]] accepted there (pinned), and [FiniteCategory] is
 refused at the same argument with the same message, so whether it adds an
 identification of its own is not measured.  [FinitelyComplete@{u u0 u1 u2
 u3} : Category@{u3 u2 u2} → Type@{u}] keeps the ambient OBJECT universe
 free and puts the shape's hom at the ambient's hom (the [Limit]
 vocabulary's identification, #416's measurement), the shape's object
 universe strictly below the sort; of the twenty-four [fl_*]/
 [finite_limit] constants exactly FIVE — [finite_limit],
 [finite_limit_apex], [finite_limit_leg], [fl_cone] and [fl_limiting] —
 carry the one block equation [u2 = u5] saying the same, the other
 nineteen ([fl_P0], [fl_P], [fl_Q], [fl_s], [fl_t], [fl_eq], …) carrying
 no equation at all (a first draft said “the whole family”; a fess audit
 counted).  TWO
 measurements decide the converse's route.  First, the small shapes
 SPLIT: [Roof@{u u0} : Category@{u u0 u0}] and [Parallel] are FREE, while
 Instance/Two.v's [_2], [Two_Discrete] and Instance/Zero.v's [_0] are
 [Category@{u Set Set}] — so at an ambient whose homs sit strictly above
 [Set] a limit over [_2] is refused and [FinitelyComplete C] cannot be
 instantiated at [_2] though the diagram is accepted (pinned), which is
 why pullbacks are read at [Roof^op] and the terminal object at the
 polymorphic [DiscreteCat False] rather than at [_0]; [Two_FiniteCategory
 : FiniteCategory@{u Set u} _2] inherits [_2]'s pin and is the ONLY
 constant of the 94 carrying a word-bounded [Set].  Second, the empty
 shape's route WAS pinned when first written: with a bare [(C : Category)]
 binder, [EmptyDiagram] minimized to [∀ C : Category@{u0 Set Set}, …] and
 dragged [empty_cone], [FinitelyComplete_Terminal] and the biconditional
 down to a [Set]-homed ambient; the explicit binders on those four are
 what lifts it, and the bare clone is pinned against them
 (Test/ProbeFinite417.v N7).  Every headline is now over
 [Category@{co ch ch}] with [co] free.

 THE CONE-CATEGORY READINGS (Instance/Cones/Limit.v).  Awodey's defining
 formulation, “a limit is a terminal object in the category of cones”,
 had only the direction [Limit_Cones : Terminal (Cones F) → Limit F];
 [Cones_Limit] is the other, and the round trips return the cone, every
 mediator, the terminal cone and the APEX MAP of every unique arrow at
 [eq_refl] — the whole unique arrow is re-paired, stdlib [sigT] having no
 eta, so only its first projection converts (the probe's [p417_round_one]
 checks exactly that; a first draft of this sentence said “every unique
 arrow”), whole records refuted, pinned.  The colimit half needed a
 CORRECTION rather
 than a dual: with [Cocones F := Cones (F^op)] (Instance/Cones.v) a cocone
 morphism is an arrow of [C^op], so the colimit is the TERMINAL object of
 [Cocones F], and the comment there saying “initial” was wrong.  Delivered
 as [Colimit_Cocones : Terminal (Cocones F) → Colimit F] and
 [Cocones_Colimit], with the covariant spelling [Initial ((Cocones F)^op)]
 proved THE SAME TYPE at [eq_refl] ([initial_op_is_terminal]) — while the
 issue's literal [Initial (Cocones F)] is a DIFFERENT type, refuted as
 types and refused as the hypothesis of the passage (pinned).

 THE METACATEGORY DONOR IS NOT TAKEN.  The issue names
 Theory/Metacategory.v's finite composition tables as a possible donor;
 that file's own header records that its guard-free [identity] is
 unsatisfiable over a finite table, so [FromArrows] yields the EMPTY
 category, and its inline note beside the field still asserted the
 encoding “is sound for the finite … metacategories built here” — that
 sentence is corrected in this commit (line-neutrally), and nothing here
 consumes that module.

 COUNTS.  94 constants: 77 [Definition], 11 [Qed]-closed lemmas ([Print
 Module] renders them [Parameter]), the 3 records and their 3 [Build_*],
 all in the [make print-assumptions] gate FULLY QUALIFIED together with
 Instance/Cones/Limit.v's 7; closure 66 modules excluding self, of which
 Structure/Limit/Product/Finite costs 22 by drop-one (its own [Coq]
 witness section is what it drags in), Pullback/Limit, FromProducts,
 Instance/Two and Construction/Quotient 1 each and every other [Require]
 0; nine [Defined] tokens, of which exactly ONE is load-bearing by
 flipping each ALONE to [Qed] — [empty_cone], whose [Qed] form stops
 [FinitelyComplete_Terminal] in this very file — the other eight
 ([FiniteCategory_op], [EmptyDiagram], [FinitelyComplete_Terminal], the
 two biconditionals and the three [Defined] shape witnesses
 [Roof_FiniteCategory], [Two_FiniteCategory], [Parallel_FiniteCategory];
 [EmptyShape_FiniteCategory] and [Cospan_FiniteCategory] are [:=] terms)
 flipping with the file and the probe intact, kept [Defined] by the data
 convention only; [make todo] grows by 18, ALL in the probe (13
 refutation commands and 5 header lines naming the token), this file and
 the six prose-edited files contributing ZERO — a sentence that is true
 only because it does not itself spell the token: a first draft did, was
 the one library hit (19, not 18), and a fess audit caught it.

 NOT DELIVERED.  No class bundling finite completeness (a plain
 [Definition], nothing registered as an [Instance], a chosen limit not
 being allowed to resolve globally); no closure of [FiniteCategory] under
 products or coproducts of shapes, under quotients, or under [Sub]; no
 bijective enumeration, no cardinality and no decidable equality of
 arrows — [fc_size] is a bound; no creation or preservation vocabulary at
 finite shapes (Structure/Limit/Creation.v's scope note is repointed, not
 discharged; no [PreservesFiniteLimits], no left-exact functors); no
 comparison of [finite_limit] with a [Complete] category's chosen limit
 at any strength; a computing witness only since #415: by the pullback
 route at [FinSet] the terminal object from the empty finite limit is
 NOT [1] by conversion (its equalizer's carrier counts a predicate that
 tests the opaque [FinSet_Pullbacks_obligation_2]; probe N10 — an
 earlier revision said N9 and “no computing witness”), while
 Instance/FinSet/Limit.v's native route converts it to [1]; no bridge
 to Shapes.v's [FiniteShape]; no filtered categories (Riehl 3.8.7); no
 equivalence-invariance of [FinitelyComplete]; and the [Set] pin on
 [Two_FiniteCategory] is [_2]'s, not repaired here and not claimed
 unavoidable. 

 --------
 Mac Lane，《为工作中的数学家而作的范畴论》，第2版，§V.2 定义1和推论1（书第113页）；Awodey，《范畴论》，§5.4 定义5.18及“所有有限极限”的运行定义（印刷第109/111页），§5.6（印刷第116页）；Fong和Spivak，《组合性中的七个示意》，§6.2.4（印刷第191-192页，定义6.30）；Riehl，《语境中的范畴论》，第2版，§3.5（印刷第115页，定理3.5.17）。有限极限是有限指标范畴上的极限，而定理是 Mac Lane 的推论 1：一个终对象、二元积和等化子给出每一个有限极限。此文件提供了树从未拥有的有限性谓词，根据它声明有限（余）完备性，通过 Structure/Limit/FromProducts.v 的引擎消耗枚举来证明该推论，并利用 Structure/Topos.v 和 Structure/Regular.v 提供的替代包证明其逆命题。这里的“有限”是什么意思。Riehl 和 Seven Sketches 的理解——有限数量的态射——作为数据：[FiniteCategory J] 携带一个大小 [fc_size]，一个枚举 [fc_arr : Fin.t fc_size → ArrowIx J] 进入 FromProducts.v 的箭头索引（两个对象及其间的箭头的对），以及一个覆盖 [fc_cover]，为每个箭头 [f] 返回一个条目的索引，该条目命中 [f]：[ArrowHit a f] 是两个 Leibniz 端点方程和传输的箭头 [≈ f]（Construction/Quotient.v 的 [hom_cast]）。这种形状的三个结果即是这一点。(i) 命中的证明是 TYPE 值的，因为 FromProducts.v 的 [Gen] 是一个 [Inductive … : Type]，并且 [Generates] 对其进行量化：[fc_Generates] 解构了证明并提供给 [gen_equiv] / [gen_idx]，而 [Prop] 值的覆盖无法做到（大消元）——这正是为什么未注册的 Structure/Limit/Preservation/Shapes.v 的 [FiniteShape] 在此未被消耗而是被披露：它的对象覆盖 [fs_objs_all] 是一个 [Prop] 值的 [List.In]，它的箭头覆盖 [fs_homs_all] 是一个 [sigT]（Type 值，因此可消元至 [Type]），其成员组件再次是一个 [Prop] 值的 [List.In]，从中无法恢复任何 [Fin.t] 索引——早期草稿称整个覆盖为“[List.In] in [Prop]”，但一次 fess 审核驳回了箭头部分的说法。(ii) “有限个”是 UP TO [≈]，这是集合等价类支持的唯一读法，并且枚举是一个 RETRACTION，而不是双射：一条箭头可能被几个索引命中，所以 [fc_size] 是箭头数量的上界，并没有声称基数。 (iii) 对象不单独枚举：一个对象是通过命中其恒等箭头的索引 [fc_obj_idx x := `1 (fc_cover (id[x] )）] 并利用收缩 [fc_obj_rt] 恢复的，这是《七个素描》的脚注指出有限多个态射强制有限多个对象——[finite_morphisms_implies_finite_objects : FiniteCategory J → FiniteObjects J]，是一个引理而不是第二个字段。有限性是自对偶的（[FiniteCategory_op]，将端点交换后的相同索引），并且任何地方都没有出现选择原理：每个 [∃] 都是一个 [sigT]。引擎是一个关于抽取（retract）的积。推论需要在[J]的对象上对[F]做积，但枚举索引是ARROWS。因此，Section RetractProduct在任意范畴上证明，一个在索引[A]上的积，加上一个等化器——针对恒等映射与规范幂等[rp_r := ⟨ cast ∘ proj (idx (down a)) ⟩_a]的等化器——是[A]的任意抽取[B]（映射[down : A → B]，[idx : B → A]，[rt : down (idx b) = b]）的积；其中没有涉及有限性，并且在[HasEqualizers]下的选择结构形式[retract_product] / [retract_product_ump]即是推论在[A := Fin.t fc_size]，[B := obj J]，[down := fc_dom]，[idx := fc_obj_idx]中应用的内容。推论消耗枚举。在有限极限一节中，在 [HasFiniteProducts C] （Structure/Limit/Product/Finite.v，第 #335 的二元积折叠）和 [HasEqualizers C]：[fl_P0] 是 #335 对 [F ∘ fc_dom] 在 [Fin.t fc_size] 上的积；[fl_P] 是 [F] 在对象上的重traction积；[fl_Q] 是 [F ∘ fc_cod] 在箭头索引上的积；[fl_s] / [fl_t] 是两个元组（在域上的投影，以及其后的 [fmap[F] (fc_arrow i)）；[fl_eq] 是它们的等化器；而 [fl_cone] / [fl_limiting] 是 #416 的 [pe_cone] / [pe_limiting] 在生成族 [fc_arrow] 上，[fc_Generates] 解除覆盖。所以 [finite_limit : Limit F] 是由三个有限积和两个等化器构建的——[fl_P0] 和 [fl_Q] 由 [Fin.t (fc_size HJ)] 索引，重traction积 [fl_P] 由 [obj J] 索引，并且本身由一个 [Fin.t] 索引的积加上重traction等化器构建，然后是 [fl_eq]——审稿人检查谓词是被消耗而不是占位的——带有 [finite_limit_apex] 和 [finite_limit_leg] 在 [eq_refl] 读取顶点和边。[finitely_complete_from_generators (T : Terminal C) (CP : Cartesian C) (HEq : HasEqualizers C)]（固定名称）在 [Cartesian_Terminal_HasFiniteProducts]，这是 [finitely_complete_from_finite_products] 的 [HasFiniteProducts] 形式。对偶 [finitely_cocomplete_from_generators] 通过 [C^op]、[HasEqualizers_op_of_HasCoequalizers]、[FiniteCategory_op] 和 [Opposite_Functor] 是原始的 [:=]，没有策略。RIEHL 3.5.17 及其逆命题。[finitely_complete_of_pullbacks_terminal : HasPullbacks C → Terminal C → FinitelyComplete C] 及其对偶是由 Structure/Pullback/Reduction.v 的两个归约组成的推论。逆命题是按形式逐步证明的：终对象是 [EmptyShape := DiscreteCat False] ([FinitelyComplete_Terminal]) 上空图的极限；拉回是 [Roof^op] 上的极限，通过 Structure/Pullback/Limit.v 的 [Pullback_to_Universal] ([FinitelyComplete_HasPullbacks]) 来读取；乘积和等化子通过 Reduction.v 得出；而 [FinitelyComplete_iff_pullbacks_terminal] 打包了双条件命题，其对偶 [FinitelyCocomplete_iff_pushouts_initial] 通过在 [C^op] ([FinitelyCocomplete_Initial], [FinitelyCocomplete_HasPushouts]) 读取原命题得到。因此，代理包是
 定理：Structure/Regular.v 的 terminal-plus-pullbacks 条款和
 Structure/Topos.v 的 [ElementaryTopos] 字段生成 [FinitelyComplete]
 （拓扑实例化是 Test/ProbeFinite417.v 的 [topos_FinitelyComplete]），并且两个头现在都说明了这一点。宇宙，同时测量绑定器和区块（为每个常量设置打印宇宙）。[FiniteCategory@{u u0 u1} : Category@{u u0 u0} → Type@{u1}] 在其绑定器中标识形状的 hom 和证明宇宙；也就是说，它是从 FromProducts.v 的 [ArrowIx] 继承的，该形状其 hom 被声明严格低于其证明宇宙时，单独拒绝 [x ~> y] 和 [id[x]（在那里被接受并固定），而 [FiniteCategory] 在相同参数下以相同信息被拒绝，因此它是否添加自己的标识未被测量。[FinitelyComplete@{u u0 u1 u2 u3} : Category@{u3 u2 u2} → Type@{u}] 保持环境对象宇宙自由，并将形状的 Hom 设置在环境的 Hom 上（[Limit] 词汇的标识，#416 的测量），形状的对象宇宙严格低于类别；在二十四个 [fl_*] / [finite_limit] 常数中，正好有五个——[finite_limit]、[finite_limit_apex]、[finite_limit_leg]、[fl_cone] 和 [fl_limiting]——承载着单一的块方程 [u2 = u5] 表示相同内容，其余的十九个（[fl_P0]、[fl_P]、[fl_Q]、[fl_s]、[fl_t]、[fl_eq]、…）则完全没有方程（初稿写着“整个家族”；一次仔细审核统计过）。两个测量决定了逆向的路径。首先，小形状
 SPLIT：[Roof@{u u0} : Category@{u u0 u0}] 和 [Parallel] 是自由的，而
 Instance/Two.v 的 [_2]、[Two_Discrete] 和 Instance/Zero.v 的 [_0] 是
 [Category@{u Set Set}] ——所以在同态严格高于 [Set] 的环境下，对 [_2] 的极限被拒绝，并且 [FinitelyComplete C] 无法在 [_2] 上实例化，尽管图被接受（固定），这就是为什么拉回在 [Roof^op] 读取，而终对象在
 多态的 [DiscreteCat False] 而不是在 [_0]；[Two_FiniteCategory : FiniteCategory@{u Set u} _2] 继承了 [_2] 的固定，并且是 94 个携带字界 [Set] 的唯一常量。其次，当第一次写入时，空形状的路径已经被固定：使用一个空的 [(C : Category)] 绑定器，[EmptyDiagram] 被最小化到 [∀ C : Category@{u0 Set Set}, …]，并且拖动 [empty_cone]、[FinitelyComplete_Terminal] 和双条件到一个 [Set] 定位的环境中；这四个上的显式绑定器就是使其提升的原因，而空克隆则针对它们被固定（Test/ProbeFinite417.v N7）。每一个标题现在都位于 [Category@{co ch ch}] 上，[co] 是自由的。锥类别读物（实例/锥/极限.v）。Awodey 的定义性表述，“极限是在锥类别中的终对象”，只是方向 [Limit_Cones : Terminal (Cones F) → Limit F]；[Cones_Limit] 是另一方向，往返返回锥、每个中介者、终锥以及 [eq_refl] 上每条唯一箭头的顶点映射——整条唯一箭头被重新配对，stdlib [sigT] 没有 eta，因此只有它的第一个投影转换（探针的 [p417_round_one] 正好检查这个；这句话的初稿说的是“每条唯一箭头”），整体记录被驳斥，已固定。余极半部分需要的是修正而不是对偶：对于 [Cocones F := Cones (F^op)]（Instance/Cones.v），余锥态射是 [C^op] 的箭头，所以余极是 [Cocones F] 的终对象，而那里评论中说的“初始”是错误的。以 [Colimit_Cocones : Terminal (Cocones F) → Colimit F] 和 [Cocones_Colimit] 的形式交付，用协变拼写 [Initial ((Cocones F)^op)] 在 [eq_refl]（[initial_op_is_terminal]）证明了相同类型——而问题中的字面 [Initial (Cocones F)] 是不同类型，被作为类型驳回，并被拒作为该段落的假设（已固定）。元类别捐赠者未被采用。该问题在 Theory/Metacategory.v 的有限组合表中将其作为可能的捐赠者；该文件自己的头部记录了它的无保护 [identity] 在有限表上是不可满足的，因此 [FromArrows] 产生了空类别，并且其字段旁的内联注释仍然断言编码“对于这里构建的有限……元类别是有效的”——该句在此提交中已被修正（行号保持不变），并且此处没有使用该模块。计数。94 个常量：77 个 [Definition]，11 个 [Qed] - 闭合引理（[Print Module] 将它们呈现为 [Parameter]），3 个记录及其 3 个 [Build_*]，全部在 [make print-assumptions] 门中完全限定，同时包括 Instance/Cones/Limit.v 的 7 个；闭包 66 个模块，不包括自身，其中 Structure/Limit/Product/Finite 通过 drop-one 消耗 22（其自身的 [Coq] 见证部分是它所带入的），Pullback/Limit、FromProducts、Instance/Two 和 Construction/Quotient 各 1，其他所有 [Require] 为 0；九个 [Defined] 令牌，其中恰好有一个通过将各自单独翻转为 [Qed] 来承重 — [empty_cone]，其 [Qed] 形式阻止了 [FinitelyComplete_Terminal] 在这个文件中 —— 其他八个（[FiniteCategory_op]、[EmptyDiagram]、[FinitelyComplete_Terminal]、两个双条件以及三个 [Defined] 形状见证 [Roof_FiniteCategory]、[Two_FiniteCategory]、[Parallel_FiniteCategory]；[EmptyShape_FiniteCategory] 和 [Cospan_FiniteCategory] 是 [:=] 术语）
 保持文件和探针完整地翻转，仅通过数据约定保持 [Defined]；[make todo] 增长 18，全在探针中（13 个驳回命令和 5 行命名前缀的标题行），此文件及贡献为零的六个散文编辑文件——一句话仅因为其本身未拼写该标记而为真：初稿拼写过，是唯一的库命中（19，不是 18），而一次 Fess 审计捕获了它。

 未送达。没有类捆绑有限完备性（一个普通的 [Definition]，没有注册为 [Instance]，选择的极限不允许全局求解）；在形状的乘积或余积下、在商下或在 [Sub] 下没有闭合；没有双射枚举，没有箭头的基数，也没有可判定的相等性——[fc_size] 是一个界限；在有限形状下没有创建或保持词汇（Structure/Limit/Creation.v 的范围注释被重新指向，而不是消除；没有 [PreservesFiniteLimits]，没有左正合函子）；没有将 [finite_limit] 与 [Complete] 类别的选定极限进行任何强度上的比较；自 #415 起仅作为计算证明者：通过 [FinSet] 的拉回路径，从空有限极限得到的终对象通过转换不是 [1]（其等化器的承载数计数一个谓词该测试不透明的 [FinSet_Pullbacks_obligation_2]；探针 N10 — 先前的版本写的是 N9 和 “无计算见证”), 而 Instance/FinSet/Limit.v 的原生路径将其转换为 [1]；没有到 Shapes.v 的 [FiniteShape] 的桥接；没有筛选类别（Riehl 3.8.7）；没有 [FinitelyComplete] 的等价不变性；并且 [Two_FiniteCategory] 上的 [Set] 引脚是 [_2] 的，这里未修复，也未声称不可避免。
*)

(** ** Finite index categories / ** 有限指标范畴 *)

Section FiniteCategory.

Context {J : Category}.

(*
 An indexed arrow [a] HITS the arrow [f : x ~> y] when its endpoints are
 [x] and [y] on the nose and, transported along those two equalities, it
 is [f] up to [≈]. The endpoint equalities are Leibniz — objects of a
 category are compared strictly in this library — and the arrow clause is
 the hom-setoid's, which is the only reading the setoid setting supports. 

 --------
 当一个有索引的箭头 [a] 的端点正好是 [x] 和 [y] 时，它会命中箭头 [f : x ~> y]，并且沿着这两个等式传递时，它在 [f] 下最多是 [≈]。端点等式是 Leibniz 的——在这个库中，范畴的对象是严格比较的——而箭头条款属于同态集等价的，这是集合等价设定唯一支持的解释。
*)

Record ArrowHit (a : @ArrowIx J) {x y : J} (f : x ~{J}~> y) : Type := {
  hit_dom : aix_dom a = x;
  hit_cod : aix_cod a = y;
  hit_arr : hom_cast hit_dom hit_cod (aix_arr a) ≈ f
}.

(*
 A category is FINITE when finitely many arrows, listed by a [Fin.t]-indexed
 family, hit every arrow (Riehl §3.5, Fong–Spivak §6.2.4: “finitely many
 morphisms”). The witness of the hit is DATA, not a mere existence claim,
 so no choice principle is needed to read an index off an arrow — and so
 the enumeration can feed the [Type]-valued [Gen] of
 Structure/Limit/FromProducts.v, which is what the corollary consumes. 

 --------
 当一个范畴在有限多箭头上被 [Fin.t] 索引族列出的箭头完全命中时，它就是有限的（Riehl §3.5，Fong–Spivak §6.2.4：“有限多个态射”）。命中的见证是数据，而不仅仅是存在性声明，因此不需要选择原理来从箭头中读取索引——因此这个枚举可以供给 Structure/Limit/FromProducts.v 中 [Gen] 的 [Type] 值，这正是推论所使用的内容。
*)

Record FiniteCategory : Type := {
  fc_size  : nat;
  fc_arr   : Fin.t fc_size → @ArrowIx J;
  fc_cover : ∀ (x y : J) (f : x ~{J}~> y),
    { i : Fin.t fc_size & ArrowHit (fc_arr i) f }
}.

(* The family the enumeration presents, in the form [Generates] takes. / 枚举所呈现的家庭以 [Generates] 的形式出现。 *)

Definition fc_dom (F : FiniteCategory) (i : Fin.t (fc_size F)) : J :=
  aix_dom (fc_arr F i).

Definition fc_cod (F : FiniteCategory) (i : Fin.t (fc_size F)) : J :=
  aix_cod (fc_arr F i).

Definition fc_arrow (F : FiniteCategory) (i : Fin.t (fc_size F)) :
  fc_dom F i ~{J}~> fc_cod F i :=
  aix_arr (fc_arr F i).

(*
 The enumerated family generates [J]: every arrow is [≈] to an indexed
 one, so it is generated by [gen_idx] and [gen_equiv] alone — identities
 and composites are never needed, the enumeration listing every arrow. 

 --------
 列举的范畴生成了 [J]：每一个箭头都是 [≈] 到一个索引的箭头，因此它仅由 [gen_idx] 和 [gen_equiv] 生成——恒等和复合箭头从不需要，列举中列出了每一个箭头。
*)

Theorem fc_Generates (F : FiniteCategory) : Generates (fc_arrow F).
Proof.
  intros x y f.
  destruct (fc_cover F x y f) as [i [ed ec ea]].
  destruct ed, ec.
  exact (gen_equiv _ f ea (gen_idx i)).
Qed.

(** *** Finitely many objects / *** 有限多个对象 *)

(*
 Objects inject into identity arrows, so an enumeration of the arrows
 yields one of the objects: the object [x] is recovered as the DOMAIN of
 the arrow that hits [id[x]]. 

 --------
 对象注入到恒等箭头，因此箭头的枚举会产生其中一个对象：对象 [x] 被恢复为击中 [id[x] 的箭头的定义域。
*)

Definition fc_obj_idx (F : FiniteCategory) (x : J) : Fin.t (fc_size F) :=
  `1 (fc_cover F x x id).

Definition fc_obj_rt (F : FiniteCategory) (x : J) :
  fc_dom F (fc_obj_idx F x) = x :=
  hit_dom _ _ (`2 (fc_cover F x x id)).

(* Finitely many objects, as a retraction of a [Fin.t] onto them. / 有限多个对象，作为 [Fin.t] 到它们的一个收缩。 *)

Record FiniteObjects : Type := {
  fo_size : nat;
  fo_obj  : Fin.t fo_size → J;
  fo_idx  : J → Fin.t fo_size;
  fo_rt   : ∀ x : J, fo_obj (fo_idx x) = x
}.

(*
 Fong–Spivak §6.2.4's footnote: a category with finitely many morphisms
 has finitely many objects. 

 --------
 Fong–Spivak §6.2.4的脚注：一个具有有限多态射的范畴具有有限多个对象。
*)

Definition finite_morphisms_implies_finite_objects (F : FiniteCategory) :
  FiniteObjects := {|
  fo_size := fc_size F;
  fo_obj  := fc_dom F;
  fo_idx  := fc_obj_idx F;
  fo_rt   := fc_obj_rt F
|}.

End FiniteCategory.

Arguments ArrowHit {J} a {x y} f.
Arguments hit_dom {J a x y f} _.
Arguments hit_cod {J a x y f} _.
Arguments hit_arr {J a x y f} _.
Arguments FiniteCategory J : clear implicits.
Arguments FiniteObjects J : clear implicits.
Arguments fc_size {J} _.
Arguments fc_arr {J} _ _.
Arguments fc_cover {J} _ {x y} f.
Arguments fc_dom {J} _ _.
Arguments fc_cod {J} _ _.
Arguments fc_arrow {J} _ _.
Arguments fc_obj_idx {J} _ _.
Arguments fc_obj_rt {J} _ _.
Arguments fo_size {J} _.
Arguments fo_obj {J} _ _.
Arguments fo_idx {J} _ _.
Arguments fo_rt {J} _ _.

(** *** Finiteness is self-dual / *** 有穷性是自对偶的 *)

(* An arrow of [J^op] is an arrow of [J] with its endpoints exchanged, so the same list enumerates both. / [J^op] 的一个箭头是 [J] 的一个箭头，其端点被交换，所以同一个列表列出了两者。 *)

Definition FiniteCategory_op {J : Category} (F : FiniteCategory J) :
  FiniteCategory (J^op).
Proof.
  unshelve refine {|
    fc_size := fc_size F;
    fc_arr := fun i =>
      @mk_arrow (J^op) (aix_cod (fc_arr F i)) (aix_dom (fc_arr F i))
        (aix_arr (fc_arr F i))
  |}.
  intros x y f.
  destruct (fc_cover F (x := y) (y := x) f) as [i [ed ec ea]].
  exists i.
  unshelve econstructor.
  - exact ec.
  - exact ed.
  - cbn; destruct ec, ed; exact ea.
Defined.

(* * ** Products over a retract of an index / * ** 指数的收缩上的产品 *)

(*
 The objects of a finite category are a RETRACT of a [Fin.t] — not a
 [Fin.t] itself, since the enumeration of arrows may name an object
 several times over. Products over a retract are recovered from products
 over the index by ONE equalizer: the tuples whose repeated factors
 agree. This is general, and is stated over bare [IsIndexedProduct] and
 [IsEqualizer] data. 

 --------
 有限范畴的对象是一个 [Fin.t] 的重traction——而不是 [Fin.t] 本身，因为箭的枚举可能会多次命名同一个对象。通过一个重traction的积可以通过指标上的积恢复：那些重复因子相同的元组。这是一般性的，并且是在裸 [IsIndexedProduct] 和 [IsEqualizer] 数据上陈述的。
*)

Section RetractProduct.

#[local] Set Default Proof Using "All".

Context {C : Category}.
Context {A B : Type} (down : A → B) (idx : B → A)
  (rt : ∀ b : B, down (idx b) = b).
Context (fam : B → C).
Context {P : C} (proj : ∀ a : A, P ~> fam (down a))
  (HP : IsIndexedProduct (fun a : A => fam (down a)) P proj).

(* The transport along the retraction, as a cast. / 沿着收缩的运输，如同浇铸。 *)

Definition rp_cast (b : B) : fam (down (idx b)) ~> fam b :=
  id_cast (f_equal fam (rt b)).

Lemma rp_cast_family {c : C} (h : ∀ b : B, c ~> fam b) (b : B) :
  rp_cast b ∘ h (down (idx b)) ≈ h b.
Proof.
  unfold rp_cast.
  generalize (rt b).
  generalize (down (idx b)).
  intros b' e.
  destruct e.
  cat.
Qed.

(* The comparison [r : P ~> P] that reads every factor off its canonical representative. / 比较 [r : P ~> P]，它读取其每个规范代表的所有因子。 *)

Definition rp_r : P ~> P :=
  unique_obj (iprod_desc HP (fun a => rp_cast (down a) ∘ proj (idx (down a)))).

Lemma rp_r_proj (a : A) :
  proj a ∘ rp_r ≈ rp_cast (down a) ∘ proj (idx (down a)).
Proof. exact (unique_property (iprod_desc HP _) a). Qed.

(* An equalizer of [id] and [r]. / [id] 和 [r] 的均衡器。 *)

Context {E : C} (e : E ~> P) (HE : IsEqualizer id rp_r E e).

Definition rp_proj (b : B) : E ~> fam b :=
  rp_cast b ∘ proj (idx b) ∘ e.

Lemma rp_r_e : rp_r ∘ e ≈ e.
Proof.
  pose proof (fork_eq HE) as H.
  rewrite id_left in H.
  now symmetry.
Qed.

Definition rp_tuple {c : C} (h : ∀ b : B, c ~> fam b) : c ~> P :=
  unique_obj (iprod_desc HP (fun a => h (down a))).

Lemma rp_tuple_proj {c : C} (h : ∀ b : B, c ~> fam b) (a : A) :
  proj a ∘ rp_tuple h ≈ h (down a).
Proof. exact (unique_property (iprod_desc HP _) a). Qed.

Lemma rp_tuple_equalizes {c : C} (h : ∀ b : B, c ~> fam b) :
  id ∘ rp_tuple h ≈ rp_r ∘ rp_tuple h.
Proof.
  apply (pe_iprod_ext HP); intro a.
  rewrite id_left, rp_tuple_proj.
  rewrite comp_assoc, rp_r_proj, <- comp_assoc, rp_tuple_proj.
  symmetry; apply (rp_cast_family h).
Qed.

Definition rp_med {c : C} (h : ∀ b : B, c ~> fam b) : c ~> E :=
  unique_obj (eq_desc HE (rp_tuple h) (rp_tuple_equalizes h)).

Lemma rp_med_incl {c : C} (h : ∀ b : B, c ~> fam b) :
  e ∘ rp_med h ≈ rp_tuple h.
Proof. exact (unique_property (eq_desc HE _ _)). Qed.

Lemma rp_med_proj {c : C} (h : ∀ b : B, c ~> fam b) (b : B) :
  rp_proj b ∘ rp_med h ≈ h b.
Proof.
  unfold rp_proj.
  rewrite <- comp_assoc, rp_med_incl.
  rewrite <- comp_assoc, rp_tuple_proj.
  apply (rp_cast_family h).
Qed.

Lemma rp_med_unique {c : C} (h : ∀ b : B, c ~> fam b) (v : c ~> E)
  (Hv : ∀ b : B, rp_proj b ∘ v ≈ h b) :
  rp_med h ≈ v.
Proof.
  apply (monic (Monic := equalizer_monic id rp_r HE)).
  rewrite rp_med_incl.
  apply (pe_iprod_ext HP); intro a.
  rewrite rp_tuple_proj.
  rewrite <- (Hv (down a)).
  unfold rp_proj.
  transitivity (proj a ∘ ((rp_r ∘ e) ∘ v)).
  - rewrite comp_assoc, comp_assoc, rp_r_proj.
    reflexivity.
  - rewrite rp_r_e.
    reflexivity.
Qed.

Definition rp_IsIndexedProduct : IsIndexedProduct fam E rp_proj := {|
  iprod_desc := fun c h => {|
    unique_obj      := rp_med h;
    unique_property := rp_med_proj h;
    uniqueness      := rp_med_unique h |}
|}.

End RetractProduct.

(* With a supply of equalizers, the product over the retract is CHOSEN. / 有了均衡器的供应，收回上的产品被选择。 *)

Section RetractProductChosen.

Context {C : Category} (HEq : HasEqualizers C).
Context {A B : Type} (down : A → B) (idx : B → A)
  (rt : ∀ b : B, down (idx b) = b).
Context (fam : B → C).
Context {P : C} (proj : ∀ a : A, P ~> fam (down a))
  (HP : IsIndexedProduct (fun a : A => fam (down a)) P proj).

Definition retract_equalizer :=
  @equalizer C HEq P P id (rp_r down idx rt fam proj HP).

Definition retract_product : C := `1 retract_equalizer.

Definition retract_incl : retract_product ~> P := `1 (`2 retract_equalizer).

Definition retract_product_proj (b : B) : retract_product ~> fam b :=
  rp_proj down idx rt fam proj retract_incl b.

Definition retract_product_ump :
  IsIndexedProduct fam retract_product retract_product_proj :=
  rp_IsIndexedProduct down idx rt fam proj HP retract_incl
    (`2 (`2 retract_equalizer)).

End RetractProductChosen.

(* * ** The corollary: finite products and equalizers give every finite limit / * ** 推论：有限积和等化器给出每一个有限极限 *)

Section FiniteLimit.

#[local] Set Default Proof Using "All".

Context {C : Category} (HFP : HasFiniteProducts C) (HEq : HasEqualizers C).
Context {J : Category} (HJ : FiniteCategory J) (F : J ⟶ C).

(*
 The product over the enumeration's DOMAINS, then over the objects of [J]
 as their retract. 

 --------
 在枚举的域上进行乘积，然后在 [J] 的对象上作为它们的收缩进行乘积。
*)

Definition fl_ofam (i : Fin.t (fc_size HJ)) : C := F (fc_dom HJ i).

Definition fl_P0 : C := finite_product fl_ofam.
Definition fl_P0_proj (i : Fin.t (fc_size HJ)) : fl_P0 ~> fl_ofam i :=
  finite_product_proj fl_ofam i.
Definition fl_P0_ump : IsIndexedProduct fl_ofam fl_P0 fl_P0_proj :=
  finite_product_ump fl_ofam.

Definition fl_P : C :=
  retract_product HEq (fc_dom HJ) (fc_obj_idx HJ) (fc_obj_rt HJ)
    (fun x : J => F x) fl_P0_proj fl_P0_ump.

Definition fl_P_proj (x : J) : fl_P ~> F x :=
  retract_product_proj HEq (fc_dom HJ) (fc_obj_idx HJ) (fc_obj_rt HJ)
    (fun x : J => F x) fl_P0_proj fl_P0_ump x.

Definition fl_P_ump : IsIndexedProduct (fun x : J => F x) fl_P fl_P_proj :=
  retract_product_ump HEq (fc_dom HJ) (fc_obj_idx HJ) (fc_obj_rt HJ)
    (fun x : J => F x) fl_P0_proj fl_P0_ump.

(* The product over the enumerated ARROWS, at their codomains. / 在它们的余域上，对枚举的箭头求积。 *)

Definition fl_afam (i : Fin.t (fc_size HJ)) : C := F (fc_cod HJ i).

Definition fl_Q : C := finite_product fl_afam.
Definition fl_Q_proj (i : Fin.t (fc_size HJ)) : fl_Q ~> fl_afam i :=
  finite_product_proj fl_afam i.
Definition fl_Q_ump : IsIndexedProduct fl_afam fl_Q fl_Q_proj :=
  finite_product_ump fl_afam.

(* The two canonical maps, by their components. / 两个典型映射，按其分量。 *)

Definition fl_s : fl_P ~> fl_Q :=
  unique_obj (iprod_desc fl_Q_ump (fun i => fl_P_proj (fc_cod HJ i))).

Definition fl_t : fl_P ~> fl_Q :=
  unique_obj (iprod_desc fl_Q_ump
    (fun i => fmap[F] (fc_arrow HJ i) ∘ fl_P_proj (fc_dom HJ i))).

Lemma fl_s_proj (i : Fin.t (fc_size HJ)) :
  fl_Q_proj i ∘ fl_s ≈ fl_P_proj (fc_cod HJ i).
Proof. exact (unique_property (iprod_desc fl_Q_ump _) i). Qed.

Lemma fl_t_proj (i : Fin.t (fc_size HJ)) :
  fl_Q_proj i ∘ fl_t ≈ fmap[F] (fc_arrow HJ i) ∘ fl_P_proj (fc_dom HJ i).
Proof. exact (unique_property (iprod_desc fl_Q_ump _) i). Qed.

(* Their equalizer, and the limit. / 他们的均衡者，也是极限。 *)

Definition fl_eq := @equalizer C HEq _ _ fl_s fl_t.
Definition fl_apex : C := `1 fl_eq.
Definition fl_incl : fl_apex ~> fl_P := `1 (`2 fl_eq).
Definition fl_incl_IsEqualizer : IsEqualizer fl_s fl_t fl_apex fl_incl :=
  `2 (`2 fl_eq).

Definition fl_cone : Cone F :=
  pe_cone F fl_P_proj fl_P_ump (fc_Generates HJ) fl_Q_proj fl_Q_ump
    fl_s fl_t fl_s_proj fl_t_proj fl_incl fl_incl_IsEqualizer.

Definition fl_limiting : IsLimitCone fl_cone :=
  pe_limiting F fl_P_proj fl_P_ump (fc_Generates HJ) fl_Q_proj fl_Q_ump
    fl_s fl_t fl_s_proj fl_t_proj fl_incl fl_incl_IsEqualizer.

Definition finite_limit : Limit F := limitcone_limit fl_cone fl_limiting.

Example finite_limit_apex :
  vertex_obj[@limit_cone _ _ _ finite_limit] = fl_apex := eq_refl.

Example finite_limit_leg (x : J) :
  @vertex_map _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ finite_limit)) x
    = fl_P_proj x ∘ fl_incl := eq_refl.

End FiniteLimit.

(** ** Finite completeness / ** 有限完备性 *)

Definition FinitelyComplete {C : Category} : Type :=
  ∀ (J : Category) (HJ : FiniteCategory J) (F : J ⟶ C), Limit F.

Definition FinitelyCocomplete {C : Category} : Type :=
  ∀ (J : Category) (HJ : FiniteCategory J) (F : J ⟶ C), Colimit F.

Definition Complete_FinitelyComplete {C : Category} (HC : @Complete C) :
  @FinitelyComplete C :=
  fun J _ F => HC J F.

Definition Cocomplete_FinitelyCocomplete {C : Category} (HC : @Cocomplete C) :
  @FinitelyCocomplete C :=
  fun J _ F => HC J F.

Definition finitely_complete_from_finite_products {C : Category}
  (HFP : HasFiniteProducts C) (HEq : HasEqualizers C) : @FinitelyComplete C :=
  fun J HJ F => finite_limit HFP HEq HJ F.

(*
 Mac Lane §V.2 Corollary 1, the pinned name: a terminal object, binary
 products and equalizers give every finite limit. 

 --------
 Mac Lane §V.2 推论 1，固定的名称：终对象、二元积和等化器给出每一个有限极限。
*)

Definition finitely_complete_from_generators {C : Category}
  (T : @Terminal C) (CP : @Cartesian C) (HEq : HasEqualizers C) :
  @FinitelyComplete C :=
  finitely_complete_from_finite_products
    (Cartesian_Terminal_HasFiniteProducts CP T) HEq.

(* The dual, at [C^op]. / 在 [C^op] 的双重。 *)

Definition finitely_cocomplete_from_generators {C : Category}
  (I : @Initial C) (CO : @Cocartesian C) (HCo : HasCoequalizers C) :
  @FinitelyCocomplete C :=
  fun J HJ F =>
    @finitely_complete_from_generators (C^op) I CO
      (HasEqualizers_op_of_HasCoequalizers HCo)
      (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

(*
 Riehl §3.5 Theorem 3.5.17: pullbacks and a terminal object give every
 finite limit; dually, pushouts and an initial object give every finite
 colimit. 

 --------
 Riehl §3.5 定理 3.5.17：拉回和一个终对象可以给出每一个有限极限；对偶地，推前和一个初对象可以给出每一个有限余极限。
*)

Definition finitely_complete_of_pullbacks_terminal {C : Category}
  (HPB : HasPullbacks C) (T : @Terminal C) : @FinitelyComplete C :=
  finitely_complete_from_generators T
    (@Cartesian_of_HasPullbacks_Terminal C T HPB)
    (@HasEqualizers_of_HasPullbacks_Terminal C T HPB).

Definition finitely_cocomplete_of_pushouts_initial {C : Category}
  (HPO : HasPushouts C) (I : @Initial C) : @FinitelyCocomplete C :=
  fun J HJ F =>
    @finitely_complete_of_pullbacks_terminal (C^op)
      (HasPullbacks_op_of_HasPushouts HPO) I
      (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

(* * ** The converse: a finitely complete category has the generators / * ** 反之：一个有限完备的范畴有生成元 *)

(* * *** The empty shape and the terminal object / * *** 空形和终对象 *)

(*
 The explicit universe binders below are LOAD-BEARING.  Written bare,
 [EmptyDiagram] minimizes its ambient category to [Category@{u Set Set}]
 and drags [empty_cone], [FinitelyComplete_Terminal] and the biconditional
 [FinitelyComplete_iff_pullbacks_terminal] down to a [Set]-homed ambient
 (measured; the pin was found by [About] and lifted by the binders). 

 --------
 下面的显式宇宙绑定器是承重的。裸写时，[EmptyDiagram] 将其环境类别最小化为 [Category@{u Set Set}]，并将 [empty_cone]、[FinitelyComplete_Terminal] 以及双条件 [FinitelyComplete_iff_pullbacks_terminal] 拉到 [Set] 所归属的环境中（已测量；销钉由 [About] 找到，绑定器提起）。
*)

Definition EmptyShape@{o h} : Category@{o h h} := DiscreteCat@{o h h} False.

Definition EmptyShape_FiniteCategory@{o h u +} :
  FiniteCategory@{o h u} EmptyShape@{o h} := {|
  fc_size  := 0;
  fc_arr   := fin0_rect (fun _ => @ArrowIx EmptyShape@{o h});
  fc_cover := fun x => False_rect _ x
|}.

Definition EmptyDiagram@{o h co ch +} (C : Category@{co ch ch}) :
  EmptyShape@{o h} ⟶ C.
Proof.
  unshelve refine (@Build_Functor EmptyShape@{o h} C
    (fun x => False_rect _ x) (fun x y _ => False_rect _ x) _ _ _);
    intros; contradiction.
Defined.

Definition empty_cone@{o h co ch +} {C : Category@{co ch ch}} (c : C) :
  Cone (EmptyDiagram@{o h co ch} C).
Proof.
  unshelve refine (@Build_Cone EmptyShape@{o h} C (EmptyDiagram@{o h co ch} C) c
    (@Build_ACone EmptyShape@{o h} C c (EmptyDiagram@{o h co ch} C)
       (fun x => False_rect _ x) _));
    intros; contradiction.
Defined.

Definition FinitelyComplete_Terminal@{co ch +} {C : Category@{co ch ch}}
  (FC : @FinitelyComplete C) : @Terminal C.
Proof.
  pose (L := FC EmptyShape EmptyShape_FiniteCategory (EmptyDiagram C)).
  unshelve refine {|
    terminal_obj := vertex_obj[@limit_cone _ _ _ L];
    one := fun c => unique_obj (@ump_limits _ _ _ L (empty_cone c))
  |}.
  intros c f g.
  transitivity (unique_obj (@ump_limits _ _ _ L (empty_cone c))).
  - symmetry.
    exact (uniqueness (@ump_limits _ _ _ L (empty_cone c)) f
             (fun x => False_rect _ x)).
  - exact (uniqueness (@ump_limits _ _ _ L (empty_cone c)) g
             (fun x => False_rect _ x)).
Defined.

(* * *** The walking cospan and pullbacks / * *** 行走余圆和拉回 *)

Definition Roof_FiniteCategory : FiniteCategory Roof.
Proof.
  unshelve refine {|
    fc_size := 5;
    fc_arr := Vector.nth (Vector.of_list
      (@mk_arrow Roof RNeg RNeg IdNeg
       :: @mk_arrow Roof RZero RNeg ZeroNeg
       :: @mk_arrow Roof RZero RZero IdZero
       :: @mk_arrow Roof RZero RPos ZeroPos
       :: @mk_arrow Roof RPos RPos IdPos :: nil)%list)
  |}.
  intros x y f.
  destruct f.
  - exists Fin.F1.
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS Fin.F1).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS Fin.F1)).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
Defined.

Definition Cospan_FiniteCategory : FiniteCategory (Roof^op) :=
  FiniteCategory_op Roof_FiniteCategory.

Definition FinitelyComplete_HasPullbacks {C : Category}
  (FC : @FinitelyComplete C) : HasPullbacks C := {|
  pullback := fun (x y z : C) (f : x ~> z) (g : y ~> z) =>
    Pullback_to_Universal
      (Opposite_Functor (@ASpan (C^op) z x y f g))
      (FC (Roof^op) Cospan_FiniteCategory
         (Opposite_Functor (@ASpan (C^op) z x y f g)))
|}.

(* The other two generators follow through #326's reductions. / 另外两个生成器遵循#326的简化。 *)

Definition FinitelyComplete_Cartesian {C : Category}
  (FC : @FinitelyComplete C) : @Cartesian C :=
  @Cartesian_of_HasPullbacks_Terminal C
    (FinitelyComplete_Terminal FC) (FinitelyComplete_HasPullbacks FC).

Definition FinitelyComplete_HasEqualizers {C : Category}
  (FC : @FinitelyComplete C) : HasEqualizers C :=
  @HasEqualizers_of_HasPullbacks_Terminal C
    (FinitelyComplete_Terminal FC) (FinitelyComplete_HasPullbacks FC).

Theorem FinitelyComplete_iff_pullbacks_terminal (C : Category) :
  @FinitelyComplete C ↔ (HasPullbacks C * @Terminal C)%type.
Proof.
  split.
  - intro FC.
    exact (FinitelyComplete_HasPullbacks FC, FinitelyComplete_Terminal FC).
  - intros [HPB T].
    exact (finitely_complete_of_pullbacks_terminal HPB T).
Defined.

(* * *** The dual, by reading the primal at [C^op] / * *** 双重的，通过在 [C^op] 阅读原始的 *)

Definition FinitelyCocomplete_FinitelyComplete_op {C : Category}
  (FCC : @FinitelyCocomplete C) : @FinitelyComplete (C^op) :=
  fun J HJ F => FCC (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

Definition FinitelyComplete_op_FinitelyCocomplete {C : Category}
  (FC : @FinitelyComplete (C^op)) : @FinitelyCocomplete C :=
  fun J HJ F => FC (J^op) (FiniteCategory_op HJ) (Opposite_Functor F).

Definition FinitelyCocomplete_Initial {C : Category}
  (FCC : @FinitelyCocomplete C) : @Initial C :=
  FinitelyComplete_Terminal (FinitelyCocomplete_FinitelyComplete_op FCC).

Definition FinitelyCocomplete_HasPushouts {C : Category}
  (FCC : @FinitelyCocomplete C) : HasPushouts C :=
  HasPushouts_of_HasPullbacks_op
    (FinitelyComplete_HasPullbacks
       (FinitelyCocomplete_FinitelyComplete_op FCC)).

Theorem FinitelyCocomplete_iff_pushouts_initial (C : Category) :
  @FinitelyCocomplete C ↔ (HasPushouts C * @Initial C)%type.
Proof.
  split.
  - intro FCC.
    exact (FinitelyCocomplete_HasPushouts FCC, FinitelyCocomplete_Initial FCC).
  - intros [HPO I].
    exact (finitely_cocomplete_of_pushouts_initial HPO I).
Defined.

(* * ** Sanity witnesses: the small shapes are finite / * ** 理智见证：小形状是有限的 *)

Definition Two_FiniteCategory : FiniteCategory _2.
Proof.
  unshelve refine {|
    fc_size := 3;
    fc_arr := Vector.nth (Vector.of_list
      (@mk_arrow _2 TwoX TwoX TwoIdX
       :: @mk_arrow _2 TwoY TwoY TwoIdY
       :: @mk_arrow _2 TwoX TwoY TwoXY :: nil)%list)
  |}.
  intros x y f.
  destruct f.
  - exists Fin.F1.
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS Fin.F1).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS Fin.F1)).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
Defined.

Definition Parallel_FiniteCategory : FiniteCategory Parallel.
Proof.
  unshelve refine {|
    fc_size := 4;
    fc_arr := Vector.nth (Vector.of_list
      (@mk_arrow Parallel ParX ParX (true; ParIdX) ::
       @mk_arrow Parallel ParY ParY (true; ParIdY) ::
       @mk_arrow Parallel ParX ParY (true; ParOne) ::
       @mk_arrow Parallel ParX ParY (false; ParTwo) :: nil)%list)
  |}.
  intros x y [b f].
  destruct f.
  - exists Fin.F1.
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS Fin.F1).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS Fin.F1)).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
  - exists (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
    unshelve econstructor;
      [ exact eq_refl | exact eq_refl | cbn; first [ reflexivity | exact I ] ].
Defined.
