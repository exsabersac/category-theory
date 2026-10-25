Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Product.Fixed.
Require Import Category.Adjunction.Continuity.Finite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

(* * * Non-existence of adjoints in Sets and Sets^op / * * 在集合及集合的对偶范畴中伴随函子不存在 *)

(*
 Mac Lane §V.5 Exercises 1 and 4 (book p. 120; maclane:V.5:ex1,
 maclane:V.5:ex4); Awodey §9.6's remark that limit preservation is a
 test for the non-existence of adjoints (awodey:9.6:remark-adjoint-
 existence-tests).
 nLab: https://ncatlab.org/nlab/show/continuous+functor
 https://ncatlab.org/nlab/show/complete+category

 BACKGROUND.  Right adjoints preserve limits, so a functor that does not
 preserve some limit has no left adjoint; the two exercises are the two
 classical instances in Sets.  Exercise 1: [X × − : Sets ⟶ Sets] has a
 left adjoint only when [X] is a point, since a right adjoint preserves
 the terminal object and [X × 1 ≅ X].  Exercise 4: [Sets^op] is not
 cartesian closed, since in a cartesian closed category with an initial
 object [x × 0 ≅ 0], and read in Sets that says [x + 1 ≅ 1].

 STALE PREMISES, RE-MEASURED.
 - "The library records only positive adjunction constructions … no
 impossibility result … no idiom for stating that a given functor
 lacks an adjoint": FALSE.  Twelve no-adjoint theorems in four
 shapes predate this file (the twelve declarations whose names match
 [(no|not)_…adjoint], plus Adjunction/Choice.v's
 [two_left_adjoint_proper : HasRightAdjoint … → False]; an earlier
 revision counted seven): quantified over the candidate —
 Instance/Top/Image.v [nat_inf_no_left_adjoint],
 Instance/Monoid/Translation.v [nat_translation_no_right_adjoint]
 and [nat_no_right_adjoints], Adjunction/Choice.v
 [two_const_Y_no_right_adjoint], Instance/Proset/Galois.v
 [succ_not_self_adjoint]; [(∃ L, L ⊣ G) → False] —
 Instance/Powerset/Quantifier.v [exists_not_right_adjoint] and
 [forall_not_left_adjoint], and, AT SETS,
 Construction/Slice/Adjunction.v [sets_slice_proj_no_left_adjoint]
 and [sets_coslice_proj_no_right_adjoint]; at a named pair —
 Adjunction/Diagonal/Connected.v [eval_not_left_adjoint];
 hypothesis-shaped — Instance/Top/Forgetful.v
 [indiscrete_no_right_adjoint].  Construction/Slice/Adjunction.v's
 [slice_proj_left_adjoint_iff_terminal : (∃ L, L ⊣ Slice_Proj a) ↔
 IsTerminalObj a] is moreover an "a left adjoint exists iff the
 object is terminal" biconditional of exactly this file's shape, so
 neither "the first no-adjoint result at Sets" nor "the first stated
 as an iff" is claimed (an earlier revision claimed both).  The
 issue's own grep is off too: 'no left adjoint|no right adjoint' has
 12 hits in the [.v] files, not one (15 over every tracked file
 outside doc/plan), and [⊣] 786 hits in 177 [.v] files, not 261.
 - "'not cartesian closed' finds only prose": FALSE.  Instance/Fun/
 Closed.v [fun_not_cartesian_closed (CC : @Cartesian ([Omega,
 FinSet])) : @Closed _ CC → False] is a theorem, in the strong form
 quantified over every cartesian structure (with a pointwise
 corollary beside it); Exercise 4 below is a second non-cartesian-
 closedness result and the first for [Sets^op], at that strength.
 (Instance/Coq/Par.v and ParE.v are prose,
 as the issue says.)
 - "The general tool (Adjunction/Continuity.v) is never used
 in the negative direction": TRUE of the two constants it means,
 [right_adjoint_PreservesLimitCone] and
 [left_adjoint_preserves_colimit] -- the places the issue points
 at are comment lines, not those declarations.  RAPL/LAPC
 have twelve term-level consumers in seven files, every one positive
 (an earlier revision said eleven); this file is the FIRST negative
 use of them — the one novelty claimed.  (The Awodey clause's "no
 category of posets" is stale too: Instance/Pos.v.)
 - Structure/BiCCC.v's [prod_zero_r] needs [Cartesian], [Closed]
 and [Initial] only — not the
 [Cocartesian] its section also opens — so no dual cocartesian
 structure of [Sets^op] is needed.

 WHAT IS DELIVERED (15 named constants plus the 4 [Program] obligations
 of [fp_adj_iso], every one closed under the global context; the four
 reusable corollaries live in Adjunction/Continuity/Finite.v).
 (1) EXERCISE 1, IN ANY CARTESIAN CATEGORY WITH A TERMINAL OBJECT.
 Forward: [fixed_product_left_adjoint_terminal (X) (L) (A : L ⊣
 fixed_product_functor X) : X ≅ 1] — Adjunction/Continuity/Finite.v's
 [right_adjoint_preserves_terminal] gives [fobj_one_iso : 1 ≅ X ×
 1], and Structure/Cartesian.v's [prod_one_r] closes; a
 GENUINE consequence of limit preservation, as the reviewer asks.
 Converse: [Id_adj_fixed_product (X) (HX : X ≅ 1) : Id ⊣ fixed_
 product_functor X], built directly from the hom-set bijection
 [fp_adj_iso] (pair with the unique arrow [to_X] to [X]; project
 back) through [Build_Adjunction']; [to_X_unique] is its one
 lemma.  No adjunction is transported along [X × − ≈ Id]: the
 converse is a construction (probe N1 refuses [fixed_product_
 functor 1 = Id] at [eq_refl]).  Packaged as the exact
 characterisation [fixed_product_left_adjoint_iff_terminal] and,
 at Sets, the issue's [times_X_has_left_adjoint_iff_terminal] — both
 directions, [∃] being [sigT]; the iff is [Qed], so its projection
 does not compute and the adjoint is exported separately as
 [Id_adj_fixed_product].  The functor is Functor/Product/Fixed.v's
 [fixed_product_functor X] ([X × −], [second] on arrows);
 Structure/Cartesian/Closed/Adjunction.v's [Prod_Functor] is
 the same functor on the other side ([− × S], with its right
 adjoint [Curry_Adjunction]), and its consolidation with
 Fixed.v's [fixed_product_functor_right] is surfaced, not done.
 (2) EXERCISE 4, IN THE STRONG FORM.  [Sets_op_not_cartesian_closed
 (CC : @Cartesian (Sets^op)) (CL : @Closed (Sets^op) CC) : False] —
 quantified over EVERY cartesian structure on [Sets^op], the
 strength of Instance/Fun/Closed.v.  The scaffolding is
 [Sets_op_Initial := Sets_Terminal] and Structure/Cocartesian.v's
 notation ([Sets_op_Cartesian_is_coproducts : @Cartesian
 (Sets^op) = @Cocartesian Sets] at [eq_refl] holds by notation
 expansion alone — both sides parse to the same term — and checks
 nothing beyond that); the argument: [prod_zero_r] at the point gives
 [1 ×[CC]
 0 ≅ 0] in [Sets^op], so the apex is subterminal in Sets and the
 two projections [exl], [exr] agree as morphisms; copairing the
 two injections [pt_inl], [pt_inr] of [OnePlusOne := 1 + 1] through
 it forces [pt_inl ≈ pt_inr], and across summands the coproduct's
 [≈] IS [False] ([pt_inl_inr_apart], [eq_refl];
 Instance/Sets/Cocartesian.v).  The two-point set is [1 + 1] and
 not the [bool]-carried [bool_setoid_object]: a morphism into the
 latter pins the CARRIER level of [Sets@{o so}] to [Set] ([∀ CC :
 @Cocartesian Sets@{Set u}, ¬ Closed@{u Set u}] on a discarded
 draft) and would state the theorem for small carriers only.
 (3) THE REUSABLE OBSTRUCTION LEMMAS (Awodey's checkbox), in
 Adjunction/Continuity/Finite.v: [right_adjoint_preserves_terminal],
 [right_adjoint_preserves_binary_products],
 [left_adjoint_preserves_initial],
 [left_adjoint_preserves_binary_coproducts] — two-line compositions
 of Adjunction/Continuity.v's RAPL with Structure/Limit/
 Comparison.v's bridges, the last two through
 [Opposite_Adjunction].  They live in a satellite of Continuity.v
 because Comparison.v already requires Continuity.v (placing them
 in Continuity.v would cycle) and because their statements are
 generic, not about Sets.

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 15
 constants and the four corollaries).  No constant of this file carries
 a universe equation, none names [Set]:
 [Sets_op_not_cartesian_closed@{u u0} : ∀ CC : Cartesian@{u u0},
 Closed@{u u0 u} → False] with [u0 < u] only, and
 [times_X_has_left_adjoint_iff_terminal@{u u0 u1 u2}] over [Sets@{u2 u1}]
 with [u2 < u1] only.  The four corollaries carry [u0 = u2], the hom
 levels of the two categories identified — [Adjunction]'s own block
 ([Build_Adjunction'] has [h1 = h2]; [right_adjoint_PreservesLimitCone]
 carries the same equation), not this development's; probe N4 pins the
 underlying constraint (a functor may not go down the hom levels,
 Theory/Functor.v's [h1 <= h2]).  Stdlib caps, each attributed by
 [About] on the donor: [DiscreteCat_Functor'] (Comparison.v) carries
 [EqdepFacts], [JMeq], [eq_ind], [eq_ind_r], [eq_rect_r] and
 [Logic_lemmas.equality], and hands them to the four corollaries and so
 to [fixed_product_left_adjoint_terminal] and both iffs;
 [Build_Adjunction'] carries [Logic_lemmas.equality] and [prod_rect],
 inherited by [Id_adj_fixed_product]; [Sets_Terminal] carries
 [Logic_lemmas.equality], [eq_ind], [eq_ind_r], inherited by [OnePt],
 [OnePlusOne], [pt_inl], [pt_inr], [Sets_op_Initial] and
 [pt_inl_inr_apart] and [Sets_op_not_cartesian_closed]; [prod_zero_r]
 carries [prod_rect] and [Sets_Cocartesian] carries [False_rect] and
 [sum_rect], all three inherited by [Sets_op_not_cartesian_closed];
 [Sets_Cartesian] carries [prod_rect].  [fixed_product_functor],
 [prod_one_r], [fobj_one_iso] and [nullary_fam] carry none (an earlier
 revision listed the two Sets structures among them).  The lists name
 the stdlib caps; every block also carries the tree's own [Basics.
 compose], [projections] and [ID] levels, not repeated here.

 COUNTS AND CONVENTIONS.
 - 15 [.glob] declaration heads here (11 [def], 4 [prf]) plus the 4
 [Program] obligations of [fp_adj_iso] (two discharged by
 [cat_simpl], two by hand), and 4 heads in Finite.v — all "Closed
 under the global context", zero [Axioms:] lines; the gate carries
 the 19 heads, fully qualified, the issue's
 [times_X_has_left_adjoint_iff_terminal] and
 [Sets_op_not_cartesian_closed] among them.
 - One [Defined], [Id_adj_fixed_product], LOAD-BEARING: flipped to
 [Qed] in a copy of the file, the probe's readback of its transpose
 ([to (adj …) f = to_X x △ f] at [eq_refl]) stops.  Six [Qed] (two
 theorems, [to_X_unique], the two hand-written obligations, the
 iff).  Finite.v has neither: its four constants are [:=] terms.
 - Closure 68 files excluding self: Functor/Product/Fixed.v costs 23 at
 the margin (it requires Instance/Grp.v — the price of reusing the
 tree's [X × −] rather than redefining it), Adjunction/Continuity/
 Finite.v 17, Structure/BiCCC.v 2, Instance/Sets/Cocartesian.v 1,
 the other fourteen [Require]s 0; Finite.v's own closure is 39
 (Structure/Limit/Comparison.v 12 at the margin).  Name collisions:
 none — each of the 19 names has 0 word occurrences elsewhere in the
 tree ([TwoPt] was renamed to [OnePlusOne] away from
 Instance/Top/Wedge.v's).
 - Test/ProbeNoAdjoint432.v mirrors the [Require] list and carries 5
 refutation commands (1 instrument + N1 CONVERSION + N2-N3 TYPING +
 N4 UNIVERSE), each stripped one at a time in a copy of the whole
 file beside its accepted controls (N4's message: "Cannot enforce ch
 = _ because ch < dh <= _"; the two TYPING negatives are told apart
 from N1 by WHAT is refused — a type ascription against an [eq_refl]
 — not by the error text, N3's also saying "cannot unify"); four
 [eq_refl] readbacks; guard coverage 20 identifier tokens inside the
 refutations / 17 also named outside, comments stripped, with three
 exhaustive exceptions (the keyword, the refuted declaration's name,
 the absent name); rename-simulated over the nine library names the
 refutations use ([fixed_product_functor], [Id_adj_fixed_product],
 [Sets_op_not_cartesian_closed], [Closed], [Cartesian], [Sets], [Id],
 [eq_refl], [False]; section binders and the controls' [Category] and
 [iso_id] excluded — an earlier revision listed those two), every
 first break on a positive line.  [make todo] grows by those 5
 lines only (2261 → 2266 over 39aa0ea5, master 1be50678 with #431),
 so the issue's "adds no new hits" box is not met as written;
 disclosed.

 NOT DELIVERED.
 - Awodey's concrete instances (the forgetful functor from posets, the
 free monoid): not built here.
 - A right-hand adjunction transport ([G ≈ G' → F ⊣ G → F ⊣ G']): not
 needed, the converse being a construction.
 - Any positive closedness statement about [Sets^op]; the
 [bool]-carried form of Exercise 4 (pinned at [Set], discarded).
 - The consolidation of [Prod_Functor] with [fixed_product_functor_
 right] (surfaced above).
 - No edit to Adjunction/Continuity.v, Structure/Limit/Comparison.v,
 Functor/Product/Fixed.v, Structure/BiCCC.v or Instance/Sets/*.v. 

 --------
 Mac Lane §V.5 练习题 1 和 4（书页 120；maclane:V.5:ex1, maclane:V.5:ex4）；Awodey §9.6 的备注：极限保持性是检验伴随不存在的一个标准（awodey:9.6:remark-adjoint-existence-tests）。
 nLab:  https://ncatlab.org/nlab/show/continuous+functor 
 https://ncatlab.org/nlab/show/complete+category 

 背景。右伴随保持极限，因此一个不保持某些极限的函子没有左伴随；这两个练习是 Sets 中的两个经典实例。练习 1：[X × − : Sets ⟶ Sets] 仅在 [X] 是一个点时才有左伴随，因为右伴随保持终对象以及 [X × 1 ≅ X]。练习 4：[Sets^op] 不是笛卡尔闭的，因为在一个具有初对象的笛卡尔闭范畴中 [x × 0 ≅ 0]，并且在 Sets 中表示为 [x + 1 ≅ 1]。陈旧的前提，重新测量。- “图书馆仅记录正向伴随构造……没有不可能性结果……没有用于说明某个函子缺乏伴随的成语”：错误。十二个非伴随定理以四种形式在此文件之前就已存在（十二个声明，其名称与 [(no|not)_…adjoint] 匹配，加上 Adjunction/Choice.v 的 [two_left_adjoint_proper : HasRightAdjoint … → False]；早期修订计数为七）：针对候选量化——Instance/Top/Image.v [nat_inf_no_left_adjoint]，Instance/Monoid/Translation.v [nat_translation_no_right_adjoint] 和 [nat_no_right_adjoints]，Adjunction/Choice.v [two_const_Y_no_right_adjoint]，Instance/Proset/Galois.v [succ_not_self_adjoint]；[(∃ L, L ⊣ G) → False]——Instance/Powerset/Quantifier.v [exists_not_right_adjoint] 和 [forall_not_left_adjoint]，以及，在集合上，Construction/Slice/Adjunction.v [sets_slice_proj_no_left_adjoint] 和 [sets_coslice_proj_no_right_adjoint]；在命名对上——Adjunction/Diagonal/Connected.v [eval_not_left_adjoint]；假设型——Instance/Top/Forgetful.v [indiscrete_no_right_adjoint]。Construction/Slice/Adjunction.v 的
 [slice_proj_left_adjoint_iff_terminal : (∃ L, L ⊣ Slice_Proj a) ↔
 IsTerminalObj a] 进一步是一个“当且仅当对象是终对象时存在左伴随”的双条件，与本文件的结构完全一致，因此并没有声称“Sets 中的第一个无伴随结果”或“第一个以 iff 形式陈述”，（早期版本声称了两者）。该问题自身的 grep 也有误：'no left adjoint|no right adjoint' 在 [.v] 文件中有 12 个匹配，而不是一个（在 doc/plan 之外的每个被跟踪文件中为 15 个），在 [⊣] 中有 786 个匹配，分布在 177 个 [.v] 文件中，而不是 261。- “‘not cartesian closed’ 只找到文本描述”：错误。实例/Fun/
 Closed.v [fun_not_cartesian_closed (CC : @Cartesian ([Omega,
 FinSet])) : @Closed _ CC → False] 是一个定理，以强形式量化于每一个笛卡尔结构（旁边有一个逐点推论）；下面的练习4是第二个非笛卡尔封闭性结果，也是 [Sets^op] 在该强度下的第一个结果。（Instance/Coq/Par.v 和 ParE.v 是散文，如问题所述。）
 - “一般工具 (Adjunction/Continuity.v) 从未在负方向上使用过”：对于它指的两个常量，[right_adjoint_PreservesLimitCone] 和
 [left_adjoint_preserves_colimit] 是正确的 — 问题指出的地方是注释行，而不是那些声明。RAPL/LAPC 在七个文件中有十二个项级使用者，每一个都是正例（早先的修订版本说是十一）；这个文件是它们的第一个负面使用——所声称的新颖之处。（Awodey 条款中的“没有 posets 的范畴”也已陈旧：Instance/Pos.v。）
 - Structure/BiCCC.v 的 [prod_zero_r] 只需要 [Cartesian]、[Closed] 和 [Initial]——不需要它所在部分也打开的 [Cocartesian]——因此不需要 [Sets^op] 的对偶余笛卡尔结构。交付内容是什么（15个命名常量加上[fp_adj_iso]的4个[Program]义务，每一个都在全局上下文中封闭；四个可重用的推论位于Adjunction/Continuity/Finite.v中）。

 (1) 练习1，在任何具有终对象的笛卡尔范畴中。前向：[fixed_product_left_adjoint_terminal (X) (L) (A : L ⊣ fixed_product_functor X) : X ≅ 1] — Adjunction/Continuity/Finite.v的[right_adjoint_preserves_terminal]提供[fobj_one_iso : 1 ≅ X × 1]，并且Structure/Cartesian.v的[prod_one_r]封闭；这是极限保持的真正结果，正如审稿人所要求的。逆命题：[Id_adj_fixed_product (X) (HX : X ≅ 1) : Id ⊣ fixed_product_functor X]，直接由同态集双射 [fp_adj_iso] 构建（与到 [X] 的唯一箭头 [to_X] 配对；投影回去）通过 [Build_Adjunction']；[to_X_unique] 是它的一个引理。没有沿 [X × − ≈ Id] 传送的伴随：逆命题是一个构造（探针 N1 在 [eq_refl] 处拒绝 [fixed_product_functor 1 = Id]）。封装为精确的表征 [fixed_product_left_adjoint_iff_terminal]，并且，在集合上，问题是 [times_X_has_left_adjoint_iff_terminal] —— 两个方向，[∃] 为 [sigT]；iff 是 [Qed]，因此它的投影无法计算，伴随被单独导出为 [Id_adj_fixed_product]。函子是 Functor/Product/Fixed.v 的 [fixed_product_functor X]（[X × −]，[second] 在箭头上）；Structure/Cartesian/Closed/Adjunction.v 的 [Prod_Functor] 是另一侧相同的函子（[− × S]，及其右伴随 [Curry_Adjunction]），并且它与 Fixed.v 的 [fixed_product_functor_right] 的合并是初步呈现的，还未完成。(2) 练习 4，强形式。[Sets_op_not_cartesian_closed (CC : @Cartesian (Sets^op)) (CL : @Closed (Sets^op) CC) : False] — 对 [Sets^op] 上的每一个笛卡尔结构量化，Instance/Fun/Closed.v 的强度。脚手架是 [Sets_op_Initial := Sets_Terminal]，Structure/Cocartesian.v 的符号（[Sets_op_Cartesian_is_coproducts : @Cartesian (Sets^op) = @Cocartesian Sets] 在 [eq_refl] 仅通过符号展开成立——双方解析为相同的项——并且不检查其他内容）；论证：[prod_zero_r] 在该点给出 [1 ×[CC] 0 ≅ 0] 在 [Sets^op] 中，因此顶点在 Sets 中是次终端的，两个投射 [exl]，[exr] 作为态射是相同的；将两个注入 [pt_inl]，[pt_inr] 通过 [OnePlusOne := 1 + 1] 的共对强制 [pt_inl ≈ pt_inr]，并且在各个直和分量上，共积的 [≈] 是 [False]（[pt_inl_inr_apart]，[eq_refl]；Instance/Sets/Cocartesian.v）。该两点集合是 [1 + 1]，而不是 [bool]-承载的 [bool_setoid_object]：一个到后者的态射将 [Sets@{o so}] 的 CARRIER 水平固定到 [Set]（[∀ CC：@Cocartesian Sets@{Set u}，¬ Closed@{u Set u}] 在一个被丢弃的草稿上），并且只会对小型承载者陈述定理。(3) 可重用阻挠引理（Awodey 的复选框），在 Adjunction/Continuity/Finite.v 中： [right_adjoint_preserves_terminal]，[right_adjoint_preserves_binary_products]，[left_adjoint_preserves_initial]，[left_adjoint_preserves_binary_coproducts] — Adjunction/Continuity.v 的 RAPL 与 Structure/Limit/Comparison.v 的桥的两行组合，后两个通过 [Opposite_Adjunction]。它们生活在 Continuity.v 的卫星中，因为 Comparison.v 已经依赖于 Continuity.v（将它们放入 Continuity.v 会形成循环），并且因为它们的陈述是通用的，而不是关于集合的。UNIVERSES（由[About]在所有15个常数和四个推论下的[Set Printing Universes]测量）。这个文件没有任何常数携带宇宙方程，没有任何常数命名为[Set]：[Sets_op_not_cartesian_closed@{u u0} : ∀ CC : Cartesian@{u u0}, Closed@{u u0 u} → False]仅带[u0 < u]，并且[times_X_has_left_adjoint_iff_terminal@{u u0 u1 u2}]在[Sets@{u2 u1}]上仅带[u2 < u1]。四个推论携带[u0 = u2]，被识别的两个范畴的同态层级——[Adjunction]自身的块（[Build_Adjunction']有[h1 = h2]；[right_adjoint_PreservesLimitCone]携带相同的方程），而不是本开发的；探针N4固定了基础约束（函子可能不会下降到同态层级，Theory/Functor.v的[h1 <= h2]）。标准库大写，每个由 [About] 归属给捐赠者：[DiscreteCat_Functor'] (Comparison.v) 携带 [EqdepFacts]、[JMeq]、[eq_ind]、[eq_ind_r]、[eq_rect_r] 和 [Logic_lemmas.equality]，并将它们传递给四个推论，从而传递给 [fixed_product_left_adjoint_terminal] 以及两个 iffs；[Build_Adjunction'] 携带 [Logic_lemmas.equality] 和 [prod_rect]，由 [Id_adj_fixed_product] 继承；[Sets_Terminal] 携带 [Logic_lemmas.equality]、[eq_ind]、[eq_ind_r]，由 [OnePt] 继承，[OnePlusOne]、[pt_inl]、[pt_inr]、[Sets_op_Initial] 以及 [pt_inl_inr_apart] 和 [Sets_op_not_cartesian_closed]；[prod_zero_r] 携带 [prod_rect]，[Sets_Cocartesian] 携带 [False_rect] 和 [sum_rect]，这三者都由 [Sets_op_not_cartesian_closed] 继承；[Sets_Cartesian] 携带 [prod_rect]。[fixed_product_functor]、[prod_one_r]、[fobj_one_iso] 和 [nullary_fam] 没有携带任何（早期修订版在它们中列出了两个集合结构）。列表列出了标准库大写字母；每个块还包含树自身的 [Basics. compose]、[projections] 和 [ID] 级别，这里不重复。计数和惯例。- 15  [.glob] 在此处声明头（11  [def]，4  [prf]）加上 4 个 [Program] 义务由 [fp_adj_iso]（两个由 [cat_simpl] 解除，两个手动解除）以及 Finite.v 中的 4 个头 — 全部“在全局上下文下关闭”，零 [Axioms:] 行；门携带 19 个头，完全合格，其中包含该问题的 [times_X_has_left_adjoint_iff_terminal] 和 [Sets_op_not_cartesian_closed]。- 一个 [Defined]，[Id_adj_fixed_product]，可承重：在文件副本中翻转至 [Qed]，探针对其转置（[to (adj …) f = to_X x △ f] 在 [eq_refl]）的回读停止。六个 [Qed]（两个定理，[to_X_unique]，两个手写义务，iff）。Finite.v 没有：它的四个常数是 [:=] 项。- 闭包 68 个文件（不包括自身）：Functor/Product/Fixed.v 边际成本为 23（它需要 Instance/Grp.v —— 重新使用树的 [X × −] 而不是重新定义它的成本），Adjunction/Continuity/Finite.v 为 17，Structure/BiCCC.v 为 2，Instance/Sets/Cocartesian.v 为 1，其余十四个 [Require] 为 0；Finite.v 自身的闭包为 39（Structure/Limit/Comparison.v 边际成本为 12）。名称冲突：无 —— 19 个名称在树的其他地方的词出现次数均为 0（[TwoPt] 已从 Instance/Top/Wedge.v 重命名为 [OnePlusOne]）。- Test/ProbeNoAdjoint432.v 对应 [Require] 列表，并包含 5 个反驳命令（1 个工具 + N1 转换 + N2-N3 类型 + N4 宇宙），每次在整个文件的副本中旁边逐一去掉，同时保留其已接受的控制（N4 的消息：“无法强制 ch = _ 因为 ch < dh <= _”；两个 TYPING 否定命令通过拒绝的内容什么来区分 N1 —— 针对 [eq_refl] 的类型指定 —— 而不是通过错误文本，N3 也说“无法统一”）；四个 [eq_refl] 回读；反驳中的守卫覆盖 20 个标识符标记 / 外部也命名 17 个，注释已去掉，有三个彻底例外（关键字、被反驳的声明名称、缺失的名称）；在反驳使用的九个库名称上进行重命名模拟（[fixed_product_functor]，[Id_adj_fixed_product]，[Sets_op_not_cartesian_closed]，[Closed]，[Cartesian]，[Sets]，[Id]，[eq_refl]，[False]；部分活页夹和控制的 [Category] 与 [iso_id] 被排除——早期版本列出了这两个，每个正线的第一次断点。[make todo]  仅通过这 5 行增长（在 39aa0ea5, master 1be50678 以及 #431 上从 2261 → 2266），所以按原文写的“未增加新命中”的问题框未不满足；已披露。

 未交付。
 - Awodey 的具体实例（从偏序集的遗忘函子，自由幺半群）：这里未构建。
 - 右侧伴随传输（[G ≈ G' → F ⊣ G → F ⊣ G']）：不需要，其逆为一个构造。
 - 关于 [Sets^op] 的任何正闭性声明；[bool] 承载的练习 4 形式（固定在 [Set]，已丢弃）。
 - [Prod_Functor] 与 [fixed_product_functor_right] 的整合（如上所示）。
 - 未编辑 Adjunction/Continuity.v, Structure/Limit/Comparison.v, Functor/Product/Fixed.v, Structure/BiCCC.v 或 Instance/Sets/*.v。
*)

(*
   * ** Mac Lane V.5 Exercise 1, in any cartesian category with a terminal
   object 

   --------
   * ** Mac Lane 第五版 练习 1，在任何带有终对象的笛卡尔范畴中
*)

Section FixedProductAdjoint.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

(*
 Forward: a left adjoint to [X × −] makes [X × −] a right adjoint, so it
 preserves the terminal object, [1 ≅ X × 1]; with [X × 1 ≅ X] this is
 [X ≅ 1]. 

 --------
 前向：[X × −] 的左伴随使得 [X × −] 成为右伴随，因此它保持终对象 [1 ≅ X × 1]；对于 [X × 1 ≅ X]，这就是 [X ≅ 1]。
*)
Theorem fixed_product_left_adjoint_terminal
  (X : C) (L : C ⟶ C) (A : L ⊣ fixed_product_functor X) : X ≅ 1.
Proof.
  pose proof (@right_adjoint_preserves_terminal C C L
                (fixed_product_functor X) A T T) as HT.
  pose proof (@fobj_one_iso C C (fixed_product_functor X) T T HT) as Hi.
  simpl in Hi.
  transitivity (X × 1); [ symmetry; exact (@prod_one_r C CC T X) |].
  symmetry; exact Hi.
Qed.

Section Converse.

Context (X : C).
Context (HX : X ≅ 1).

(* Every object has exactly one arrow into an [X ≅ 1]. / 每个对象正好有一条箭头指向一个 [X ≅ 1]。 *)
Definition to_X (x : C) : x ~> X := from HX ∘ one.

Lemma to_X_unique {x : C} (f : x ~> X) : f ≈ to_X x.
Proof.
  unfold to_X.
  rewrite <- (id_left f), <- (iso_from_to HX), <- comp_assoc.
  apply compose_respects; [reflexivity |]; apply one_unique.
Qed.

(* The hom-set bijection [C(x, y) ≅ C(x, X × y)]: pair with the unique arrow to [X], and project back. / 同态集双射 [C(x, y) ≅ C(x, X × y)]：与到 [X] 的唯一箭头配对，然后投射回去。 *)
Program Definition fp_adj_iso (x y : C) :
  @Isomorphism Sets
    {| carrier := @hom C (Id x) y; is_setoid := @homset C (Id x) y |}
    {| carrier := @hom C x (fixed_product_functor X y)
     ; is_setoid := @homset C x (fixed_product_functor X y) |} := {|
  to   := {| morphism := fun f => to_X x △ f |};
  from := {| morphism := fun g => exr ∘ g |}
|}.
Next Obligation. proper; now apply fork_respects. Qed.
Next Obligation.
  symmetry; apply (snd (ump_products _ _ _)); split;
    [ apply to_X_unique | reflexivity ].
Qed.

(*
 Converse: when [X ≅ 1], the identity is a left adjoint of [X × −].  Built
 directly (no adjunction is transported along [X × − ≈ Id]). 

 --------
 反之：当 [X ≅ 1] 时，恒等函子是 [X × −] 的左伴随。直接构造（没有沿 [X × − ≈ Id] 传递伴随）。
*)
Definition Id_adj_fixed_product : Id ⊣ fixed_product_functor X.
Proof using C CC HX T X.
  unshelve eapply (@Build_Adjunction' C C Id (fixed_product_functor X)
                     fp_adj_iso).
  - intros x y z f g; simpl.
    rewrite <- fork_comp.
    apply fork_respects; [| reflexivity].
    symmetry; apply to_X_unique.
  - intros x y z f g; simpl.
    symmetry; apply second_fork.
Defined.

End Converse.

(*
 The exact characterisation: [X × −] has a left adjoint iff [X] is
 terminal ([∃] is [sigT], so the converse hands over the adjoint). 

 --------
 精确的表述：[X × −] 有一个左伴随当且仅当 [X] 是终对象（[∃] 是 [sigT]，所以反过来提供了伴随）。
*)
Theorem fixed_product_left_adjoint_iff_terminal (X : C) :
  (∀ L : C ⟶ C, L ⊣ fixed_product_functor X → X ≅ 1)
  ∧ (X ≅ 1 → ∃ L : C ⟶ C, L ⊣ fixed_product_functor X).
Proof.
  split.
  - intros L A; exact (fixed_product_left_adjoint_terminal X L A).
  - intro HX; exists Id; exact (Id_adj_fixed_product X HX).
Qed.

End FixedProductAdjoint.

(** The exercise as stated, at Sets. / 练习如所述，按组进行。 *)
Definition times_X_has_left_adjoint_iff_terminal (X : Sets) :
  (∀ L : Sets ⟶ Sets, L ⊣ fixed_product_functor X → X ≅ 1)
  ∧ (X ≅ 1 → ∃ L : Sets ⟶ Sets, L ⊣ fixed_product_functor X) :=
  fixed_product_left_adjoint_iff_terminal X.

(* * ** Mac Lane V.5 Exercise 4: [Sets^op] is not cartesian closed / * ** Mac Lane V.5 练习 4：[Sets^op] 不是笛卡尔闭合的 *)

(*
 The duality scaffolding is conversion: [@Cocartesian Sets] IS
 [@Cartesian (Sets^op)] (Structure/Cocartesian.v), and the
 terminal object of Sets is the initial object of [Sets^op]. 

 --------
 二元性支架是转换：[@Cocartesian Sets] 是 [@Cartesian (Sets^op)]（结构/余笛卡尔.v），而集合的终对象是 [Sets^op] 的初对象。
*)
Definition Sets_op_Initial : @Initial (Sets^op) := Sets_Terminal.

Example Sets_op_Cartesian_is_coproducts :
  @Cartesian (Sets^op) = @Cocartesian Sets := eq_refl.

(*
 The point, and the two-point set [1 + 1] with its injections — kept
 polymorphic (a [bool]-carried two-point set would pin the object level
 to [Set]). 

 --------
 这一点，以及具有其注入的两点集 [1 + 1] — 保持多态（一个由 [bool] 携带的两点集会将对象层固定到 [Set]）。
*)
Definition OnePt : Sets := @terminal_obj Sets Sets_Terminal.

Definition OnePlusOne : Sets :=
  @product_obj (Sets^op) Sets_Cocartesian OnePt OnePt.

Definition pt_inl : OnePt ~{Sets}~> OnePlusOne :=
  @exl (Sets^op) Sets_Cocartesian OnePt OnePt.

Definition pt_inr : OnePt ~{Sets}~> OnePlusOne :=
  @exr (Sets^op) Sets_Cocartesian OnePt OnePt.

(* The two injections differ: across summands the coproduct's [≈] IS [False] (Instance/Sets/Cocartesian.v). / 这两个注入不同：在求和算子的各个加数中，余积的 [≈] 是 [False]（Instance/Sets/Cocartesian.v）。 *)
Example pt_inl_inr_apart :
  (pt_inl ttt ≈ pt_inr ttt) = False := eq_refl.

(*
 If [Sets^op] were cartesian closed for ANY cartesian structure [CC],
 [prod_zero_r] would give [1 ×[CC] 0 ≅ 0] in [Sets^op] — in [Sets], a
 subterminal apex under both injections of [1 + 1] — forcing the two
 injections to agree. 

 --------
 如果  [Sets^op]  对于任何笛卡尔结构  [CC]  都是笛卡尔封闭的，[prod_zero_r]  将在 [Sets^op] 中给出 [1 ×[CC]  0 ≅ 0] —— 在 [Sets] 中，一个在 [1 + 1] 双重注入下的子终端顶点 —— 迫使两个注入相一致。
*)
Theorem Sets_op_not_cartesian_closed
  (CC : @Cartesian (Sets^op)) (CL : @Closed (Sets^op) CC) : False.
Proof.
  pose (Z := @initial_obj (Sets^op) Sets_op_Initial).
  pose proof (@prod_zero_r (Sets^op) CC CL Sets_op_Initial OnePt) as Hi.
  assert (Hsub : ∀ p q : carrier (@product_obj (Sets^op) CC OnePt Z), p ≈ q).
  { intros p q.
    pose proof (iso_from_to Hi p) as Hp.
    pose proof (iso_from_to Hi q) as Hq.
    assert (Hu : ∀ u v : carrier OnePt, to Hi u ≈ to Hi v)
      by (intros [] []; reflexivity).
    exact (transitivity (symmetry Hp) (transitivity (Hu _ _) Hq)). }
  assert (Hi12 : @exl (Sets^op) CC OnePt Z ≈ @exr (Sets^op) CC OnePt Z)
    by (intro u; apply Hsub).
  assert (Hbad : pt_inl ≈ pt_inr).
  { rewrite <- (@exl_fork (Sets^op) CC OnePlusOne OnePt Z pt_inl pt_inr) at 1.
    rewrite <- (@exr_fork (Sets^op) CC OnePlusOne OnePt Z pt_inl pt_inr) at 2.
    now rewrite Hi12. }
  exact (Hbad ttt).
Qed.
