Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* * * The evaluation functor on a functor category / * * 在函子范畴上的评价函子 *)

(*
 Mac Lane §V.3, the opening construction (book p. 115;
 maclane:V.3:construction1); Awodey §8.1's ev_C : Sets^(C^op) ⟶ Sets
 (awodey:8.1:construction-evaluation-functor).
 nLab: https://ncatlab.org/nlab/show/functor+category

 BACKGROUND.  Each object p of the index category P gives the evaluation
 functor E_p : [P, X] ⟶ X, H ↦ H p on objects and σ ↦ σ_p on
 transformations.  It is the partial application at p of the two-variable
 evaluation [P, X] ∏ P ⟶ X — the counit of Cat's exponential — whose
 transpose [J ∏ P, X] ≅ [J, [P, X]] is what turns a diagram of functors
 into a diagram with a parameter.  Its USE, that evaluation preserves and
 creates limits so that limits in [P, X] are computed pointwise, is
 Theorems 1 and 2 of the section and belongs to #425 and #426, not here.

 STALE PREMISES, RE-MEASURED.  The issue's “the fixed-object evaluation
 functor [P, X] ⟶ X is nowhere materialised” is FALSE, and its hit list
 is wrong in two of four entries.
 - Adjunction/Diagonal/Connected.v [EvalAt@{jo jh co ch +} (j : J) :
 [J, C] ⟶ C] IS this functor, general in shape and target, closed
 under the global context, and docs/INDEX.md records it as NEW
 there with a by-type sweep.  [Eval] below has the same two data
 fields at [eq_refl] under [EvalAt]'s own annotation (probe); the
 RECORDS do not convert (probe N1: both are [Program Definition]s with
 opaque law fields).  Also present: Functor/Hom/Yoneda/Natural.v
 [YoEvalAt : [C, Sets] ⟶ Sets] and [YoEval : [C, Sets] ∏ C ⟶ Sets]
 (the two-variable one, at Sets, in the OTHER arrow order, bridged by
 [yo_eval_map_alt]), and Theory/Shapes.v [One_Eval : [_1, C]
 ⟶ C].  Both [YoEvalAt] and [One_Eval] agree with [Eval] at [eq_refl]
 (probe).
 - The hit list: the Theory/Kan/Extension.v entry lands on a comment
 rather than on [Induced] itself;
 Instance/CMon.v is [CMon_Forget : CMon ⟶ Sets], not out of
 a functor category; Construction/Day.v is the Day tensor; only
 Theory/Lawvere/Sets.v [ev1] is as described.
 - “record [J ∏ P, X] ≅ [J, [P, X]] from [Cat_Closed]”: it exists as an
 isomorphism in [Cat], Instance/Cat/Exponential.v [Cat_exp_prod_l]
 — cited by Instance/Fun/Eval/Cat.v's [eval_transpose], not rebuilt.
 - “[Functor/Bifunctor.v] supplies [bimap] but no partial-application
 constructor”: Functor/Bifunctor/Partial.v's [Partial_l] and
 [Partial_r] exist (its INDEX bullet warns about the [Cat_Closed]
 currying route's universe pinning, measured again below).
 - Correct as cited: Structure/Cartesian/Closed.v [eval],
 Instance/Cat/Cartesian/Closed.v [Cat_Closed], Theory/Lawvere/
 Model.v's [Models] as a FULL subcategory of [[law_cat T, C]].

 WHAT IS DELIVERED (11 named constants here plus 17 [Program]
 obligations, 6 in Instance/Fun/Eval/Cat.v, every one closed under the
 global context).
 (1) [Eval (p : P) : [P, X] ⟶ X], annotated [@{jo jh co ch}] through the
 section's [Universe] declaration exactly as [EvalAt] is, in the
 light home the issue asks for (closure 19 files).
 (2) THE TWO-VARIABLE EVALUATION.  [EvalBi : [P, X] ∏ P ⟶ X] with arrow
 action [fmap[K] f ∘ transform[σ] p] — [Cat_Closed]'s order, so
 Instance/Fun/Eval/Cat.v's [CatEval_obj]/[CatEval_map] identify it
 with [Cat]'s own [eval] at [eq_refl] in both fields.  It is built
 directly rather than as [@eval Cat Cat_Cartesian Cat_Closed P X]
 because that route is reachable only at [Cat]'s universes: measured
 in the satellite, the [Cat] route identifies P's and X's object and
 hom levels into ONE universe ([u0 = u1], [u0 = u5], [u0 = u6]),
 while [EvalBi] keeps only [jh = ch].
 (3) PARTIAL APPLICATION AGREES.  [eval_partial_obj] at [eq_refl];
 [eval_partial_map] at [≈] ONLY — [Partial_l]'s action is [bimap s
 id], which carries the [fmap id] the functor law removes (probe N2;
 the same reason [yo_eval_at_map] is stated at [≈]); packaged as
 [eval_partial_iso : Eval p ≅ Partial_l EvalBi p] in [[[P, X], X]]
 with identity components, every obligation auto-discharged; the
 other partial is the functor itself ([eval_partial_r_obj] at
 [eq_refl], [eval_partial_r_map] at [≈]).
 (4) NATURALITY IN THE OBJECT.  [Eval_nat (f : p ~> q) : Eval p ⟹ Eval q]
 with component [fmap[H] f] (both naturality fields are the
 naturality of the evaluated transformation), assembled into
 [EvalFunctor : P ⟶ [[P, X], X]] with [EvalFunctor_obj]/
 [EvalFunctor_map] at [eq_refl].  The GENERAL form is new; the
 construction itself appears at one object of one category as
 Functor/Representable/Functorial.v's [wit_ev_tau n : YoEvalAt
 ttt ⟹ YoEvalAt ttt] over [BNat] and [Sets], whose component
 converts with [Eval_nat]'s at [eq_refl] (probe).  [EvalFunctor]
 has no precedent: a tree-wide sweep for a functor into a double
 functor category [[_, _], _] returns only this file.  (An earlier
 revision said “genuinely absent before”; the audit found the
 one-object instance.)
 (5) IN THE PROBE (Test/ProbeFunEval424.v): the identifications with
 [EvalAt], [YoEvalAt] and [One_Eval], each in BOTH data fields at
 [eq_refl] (an earlier revision recorded [One_Eval] on objects
 only, implying a boundary that is not there), and Awodey's
 increment [p424_ev1_via_Eval : Models T Sets ⟶ Sets := Eval
 (law_of_nat 1) ◯ Incl] agreeing with Theory/Lawvere/Sets.v's
 [ev1] in both data fields at [eq_refl].  They live in Test/
 because the identified constants sit in heavier layers
 (Adjunction/, Functor/Hom/Yoneda/, Theory/Lawvere/) that no
 Instance/Fun/ file requires.  The Awodey checkbox asks that [ev1]
 be re-expressed “rather than left as a parallel hand-written
 definition”: it is NOT met — [ev1] is untouched — the twin shows
 the re-expression is exact, and the edit to the landed file is
 surfaced for John (an earlier revision called the box met).
 The issue's pinned verification name [Eval_partial_application]
 is not declared; the partial-application agreement is delivered
 as [eval_partial_obj]/[eval_partial_map]/[eval_partial_iso].
 (6) THE [EvalAt] DECISION, SURFACED.  Two constants now carry the same
 functor.  Aliasing [EvalAt := Eval] would edit
 Adjunction/Diagonal/Connected.v (with its exact annotation, and a
 re-check of [EvalAt_retracts], [colimit_is_EvalAt] and
 Test/ProbeConnected378.v); deleting it is a removal of working
 code.  Neither is done here: docs/INDEX.md's “NEW” is corrected
 in place and both remain.

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 17
 constants).
 - Every constant of this file carries exactly one equation, [jh = ch]:
 Instance/Fun.v's [Fun] identifies the hom universes of source and
 target, so every functor into or out of [[P, X]] inherits it.
 [Eval@{jo jh co ch u u0}] carries [jh < u], [jo <= jh], [jh <= u0],
 [co <= u0], [jh = ch] — [EvalAt]'s constraint set exactly.  No
 word-bounded [Set], no [JMeq]/[EqdepFacts]/[eq_rect_r] bound.  Exactly
 four constants carry [prod_rect.*] bounds — [eval_partial_iso],
 [EvalFunctor], [EvalFunctor_obj], [EvalFunctor_map] — and the carrier
 is NOT the passage through [[[P, X], X]]: that category and its
 identity functor carry no such bound (measured); the donor is not
 isolated here.  (An earlier revision attributed the bound to the
 passage.)  The 17 [Program] obligations carry [jh = ch] and no
 stdlib bound.
 - The satellite's [Cat]-routed constants collapse to one universe
 (item (2)) and carry [Basics.compose], [eq_rect] and [prod_rect]
 bounds; see its header.

 COUNTS AND CONVENTIONS.
 - 34 constants closed under the global context: 17 [.glob] declaration
 heads (here 9 [def] + 2 [prf]; the satellite 5 [def] + 1 [prf]) plus
 this file's 17 [Program] obligations, which the [.glob] cannot see
 ([Eval] 3, [EvalBi] 3, [eval_partial_iso] 6, [Eval_nat] 2,
 [EvalFunctor] 3; the satellite has none); zero [Axioms:] lines; the
 gate carries the 17 heads, fully qualified.  (An earlier revision
 said “17/17 constants”, counting heads only.)  No [Defined]; eight
 [Qed] tokens here (two lemmas, six obligation proofs written out; all
 obligations opaque by Lib.v's flag) and one in the satellite.
 - Closure 19 files excluding self: Instance/Fun.v costs 5 at the
 margin, Functor/Bifunctor/Partial.v 1, the other seven [Require]s 0.
 No collision: each new name has 0 declaration hits elsewhere in the
 tree.  THE NAME [Eval] AND THE VERNACULAR: [Eval compute in …] and
 [ltac:(eval …)] still work after this file, and [Check Eval] resolves
 to the constant — but at the HEAD of a definition body, [Definition
 f p := Eval p.] is a PARSE error (“'in' expected after [red_expr]”),
 because Coq reads [Eval <red_expr> in <term>]; [(Eval p)],
 [@Eval P X p] and tactic-mode [exact (Eval p)] all work.  Consumers
 (#425, #426) must parenthesise.  Renaming the constant is surfaced
 for John, not done.  (An earlier revision measured only the harmless
 direction.)
 - Test/ProbeFunEval424.v carries 4 refutation commands (1 instrument +
 N1, N2, N3, all CONVERSION — N3 is the [Partial_r] twin of N2, added
 after the audit so the right-hand [≈]-only boundary is guarded too),
 each stripped one at a time in a copy of the whole file; guard
 coverage 23 identifier tokens inside the refutations / 17 also named
 outside, comments stripped, with six exhaustive exceptions (the
 keyword, the three refuted declarations' names, the binder [s], the
 absent name); rename-simulated 7/7 ([Eval], [EvalBi], [EvalAt],
 [Partial_l], [Partial_r], [YoEvalAt], [CatEval], each renamed
 throughout a copy with module paths excluded) with every first break
 on a positive line.  [make todo] grows by those 4 lines only
 (2218 → 2222 against the rebased base 39e583d2), so the issue's
 “adds no new hits” box is not met as written; disclosed.

 NOT DELIVERED.
 - Any preservation or creation of limits by evaluation (#425, #426).
 - An alias or removal of [EvalAt], [YoEvalAt] or [One_Eval] (item (6);
 surfaced).  [YoEval]'s arrow order is not changed; its bridge to this
 order is the existing [yo_eval_map_alt].
 - Replacing [ev1]'s body in Theory/Lawvere/Sets.v (surfaced); the
 re-expression lives in the probe.
 - A general two-variable evaluation at [Cat]'s universes with the
 collapse removed: the collapse is [Cat]'s, measured and disclosed.
 - No edit to Adjunction/Diagonal/Connected.v, Functor/Hom/Yoneda/
 Natural.v, Theory/Shapes.v, Theory/Lawvere/Sets.v or
 Functor/Bifunctor/Partial.v. 

 --------
 Mac Lane §V.3，开篇构造（书页 115；maclane:V.3:construction1）；Awodey §8.1 的 ev_C : Sets^(C^op) ⟶ Sets (awodey:8.1:construction-evaluation-functor)。
 nLab: https://ncatlab.org/nlab/show/functor+category 

 背景。指数范畴 P 的每个对象 p 给出评估函子 E_p : [P, X] ⟶ X，H ↦ H p（在对象上）以及 σ ↦ σ_p（在变换上）。它是二变量评估 [P, X] ∏ P ⟶ X 在 p 的部分应用——Cat 指数的余单位——其转置 [J ∏ P, X] ≅ [J, [P, X] 将函子图变成带参数的图。它的用途是，评估保持并产生极限，因此 [P, X] 中的极限可以按点计算，这就是本节定理 1 和定理 2，并属于 #425 和 #426，而不在这里。过时的前提，重新测量。问题“固定对象评估函子 [P, X] ⟶ X 从未具体化”是错误的，并且其命中列表在四个条目中有两个是错误的。- Adjunction/Diagonal/Connected.v [EvalAt@{jo jh co ch +} (j : J) : [J, C] ⟶ C] 是否这个函子，在形状和目标上是一般的，在全局上下文下封闭，并且 docs/INDEX.md 将其记录为新的，通过类型扫描。下面的 [Eval] 在 [EvalAt] 自身注解（探针）下的 [eq_refl] 具有相同的两个数据字段；RECORDS 不进行转换（探针 N1：两者都是具有不透明定律字段的 [Program Definition]）。同样存在的文件有：Functor/Hom/Yoneda/Natural.v  [YoEvalAt : [C, Sets] ⟶ Sets] 和 [YoEval : [C, Sets] ∏ C ⟶ Sets]（那个二变量的，在 Sets 中，箭头顺序不同，由 [yo_eval_map_alt] 连接），以及 Theory/Shapes.v  [One_Eval : [_1, C] ⟶ C]。[YoEvalAt] 和 [One_Eval] 在 [eq_refl]（探针）处都与 [Eval] 一致。- 重点清单：Theory/Kan/Extension.v 条目指向的是注释，而不是 [Induced] 本身；Instance/CMon.v 是 [CMon_Forget : CMon ⟶ Sets]，而不是来自函子范畴的；Construction/Day.v 是 Day 张量；只有 Theory/Lawvere/Sets.v  [ev1] 如描述所示。- “record [J ∏ P, X] ≅ [J, [P, X] ] 来自 [Cat_Closed]”：它作为一个同构存在于 [Cat] 中，Instance/Cat/Exponential.v  [Cat_exp_prod_l] — 被 Instance/Fun/Eval/Cat.v 的 [eval_transpose] 引用，而未被重建。- “[Functor/Bifunctor.v] 提供 [bimap]，但没有部分应用构造函数”：Functor/Bifunctor/Partial.v 的 [Partial_l] 和 [Partial_r] 存在（其 INDEX 项警告了 [Cat_Closed] 柯里化路径的宇宙固定，如下再次测量）。- 引用正确：Structure/Cartesian/Closed.v 的 [eval]，Instance/Cat/Cartesian/Closed.v 的 [Cat_Closed]，Theory/Lawvere/Model.v 的 [Models] 作为 [[law_cat T, C] 的 FULL 子范畴。交付的内容是什么（这里有11个命名常量，加上17个[Program]义务，其中6个在Instance/Fun/Eval/Cat.v中，每一个都在全局上下文中封闭）。(1) [Eval (p : P) : [P, X] ⟶ X]，通过本节的[Universe]声明注释为[@{jo jh co ch}]，完全像[EvalAt]一样，根据问题要求的光亮位置（封闭19个文件）。(2) 双变量评估。[EvalBi : [P, X] ∏ P ⟶ X]，箭头操作[fmap[K] f ∘ transform [σ] p] — [Cat_Closed]的顺序，因此Instance/Fun/Eval/Cat.v的[CatEval_obj] / [CatEval_map]在两个字段中将其与[Cat]自己的[eval]在[eq_refl]处识别。它是直接构建的，而不是作为 [@eval Cat Cat_Cartesian Cat_Closed P X]，因为那条路径只能在 [Cat] 的宇宙中到达：在卫星中测量，[Cat] 路径将 P 和 X 的对象及同伦级别识别到一个宇宙中（[u0 = u1]、[u0 = u5]、[u0 = u6]），而 [EvalBi] 只保留 [jh = ch]。（3）部分应用一致。[eval_partial_obj] 在 [eq_refl]；[eval_partial_map] 仅在 [≈] — [Partial_l] 的作用是 [bimap s id]，它携带 [fmap id]，函子定律移除（探测 N2；同样的原因 [yo_eval_at_map] 在 [≈] 陈述）；作为 [eval_partial_iso : Eval p ≅ Partial_l EvalBi p] 打包在 [[[P, X] 中，X]]具有恒等分量，每项义务自动解除；另一个部分是函子自身（[eval_partial_r_obj] 在 [eq_refl]，[eval_partial_r_map] 在 [≈]）。(4) 对象的自然性。[Eval_nat (f : p ~> q) : Eval p ⟹ Eval q]  
 与组件  [fmap[H]  f]（两个自然性域都是已评估变换的自然性），组装成  
 [EvalFunctor : P ⟶ [[P, X] , X]] 与  [EvalFunctor_obj] /  
 [EvalFunctor_map] 在  [eq_refl]。其通用形式是新的；该构造本身出现在一个范畴的一个对象上，作为 Functor/Representable/Functorial.v 中的 [wit_ev_tau n : YoEvalAt  
 ttt ⟹ YoEvalAt ttt] 在  [BNat] 和  [Sets] 上，其组件在  [eq_refl]（探针）处与  [Eval_nat] 转换。[EvalFunctor] 没有先例：对双函子范畴 [[_, _] 的函子进行树级遍历，_] 只返回该文件。（早期修订稿写的是“之前确实缺失”；审核发现了那个单对象实例。）
 （5）在探查中（Test/ProbeFunEval424.v）：与 [EvalAt]、[YoEvalAt] 和 [One_Eval] 的标识，每个都在 [eq_refl] 的两个数据字段中（早期修订稿仅在对象上记录了 [One_Eval]，暗示了不存在的边界），以及 Awodey 的增量 [p424_ev1_via_Eval : Models T Sets ⟶ Sets := Eval (law_of_nat 1) ◯ Incl] 在 [eq_refl] 的两个数据字段中与 Theory/Lawvere/Sets.v 的 [ev1] 一致。它们位于 Test/ 中，因为被识别的常量位于更高层（Adjunction/、Functor/Hom/Yoneda/、Theory/Lawvere/），而没有 Instance/Fun/ 文件需要它们。Awodey 复选框要求 [ev1] 被重新表达“而不是作为平行手写定义保留”：这一要求未满足——[ev1] 未被修改——复本显示重新表达是精确的，并且对已生成文件的编辑已显示给 John（早期版本称该框已满足）。该问题的固定验证名称 [Eval_partial_application] 未被声明；部分应用协议以 [eval_partial_obj] / [eval_partial_map] / [eval_partial_iso] 形式交付。（6）[EvalAt] 决策，已显示。现在有两个常量使用相同的函子。对 [EvalAt := Eval] 进行别名操作会编辑 Adjunction/Diagonal/Connected.v（带有其精确注解，并重新检查 [EvalAt_retracts]、[colimit_is_EvalAt] 和 Test/ProbeConnected378.v）；删除它则是移除工作代码。这里两个都没有完成：docs/INDEX.md 中的“NEW”已原地纠正，并且两者都保留。宇宙（通过 [About] 在 [Set Printing Universes] 下对所有 17 个常量测量）。- 本文件的每个常量恰好包含一个方程，[jh = ch]：Instance/Fun.v 的 [Fun] 标识源和目标的同态宇宙，因此每个进入或来自 [[P, X] 的函子继承它。[Eval@{jo jh co ch u u0}] 包含 [jh < u]、[jo <= jh]、[jh <= u0]、[co <= u0]、[jh = ch] — [EvalAt] 的约束集完全一致。没有字界限 [Set]，没有 [JMeq] / [EqdepFacts] / [eq_rect_r] 界限。恰好四个常量带有 [prod_rect.*] 界限 — [eval_partial_iso]、[EvalFunctor]、[EvalFunctor_obj]、[EvalFunctor_map] — 且承载者不是通过 [[[P, X], X]] 的通道：该类别及其恒等函子不带有此类界限（已测量）；捐赠者在此未被孤立。(早期版本将界限归因于该段落。) 17 [Program] 义务带有 [jh = ch] 并且没有 stdlib 界限。- 卫星的 [Cat] 路由常量折叠到一个宇宙（条目 (2)）并带有 [Basics.compose]、[eq_rect] 和 [prod_rect] 界限；见其标题。计数与约定。- 在全局上下文下封闭的34个常量：17个[.glob]声明头（这里9个[def] + 2个[prf]；卫星5个[def] + 1个[prf]）加上该文件的17个[Program]义务，[.glob]无法看到（[Eval] 3，[EvalBi] 3，[eval_partial_iso] 6，[Eval_nat] 2，[EvalFunctor] 3；卫星没有）；零个[Axioms:]行；门包含了17个头，完全限定。（早期版本说“17/17常量”，只计算头。）无[Defined]；这里有八个[Qed]标记（两个引理，六个义务证明已写出；所有义务因Lib.v的标志而不透明）以及卫星中的一个。- 关闭除自身外的19个文件：Instance/Fun.v 在边际成本为5，Functor/Bifunctor/Partial.v 为1，其余七个 [Require] 为0。没有冲突：每个新名称在树的其他地方声明命中为0。名称 [Eval] 和 VERNACULAR: [Eval compute in …] 以及 [ltac:(eval …)] 在此文件之后仍然有效，[Check Eval] 解析为常量——但在定义体的开头，[Definition f p := Eval p.] 是 PARSE 错误（“在 [red_expr] 之后期望 'in'”），因为 Coq 读取 [Eval <red_expr> in <term>]；[(Eval p)]，[@Eval P X p] 和战术模式 [exact (Eval p)] 都可以使用。使用者（#425, #426）必须加括号。重命名常量已向 John 显示，但未执行。（早期的修订版本仅测量了无害方向。）
 - Test/ProbeFunEval424.v 载有 4 个反驳命令（1 个工具 + N1、N2、N3，都为 CONVERSION — N3 是 N2 的 [Partial_r] 双胞胎，在审计后添加，因此右侧 [≈] 专用边界也被保护），每次在整个文件的副本中剥离一个；反驳中的守护覆盖了 23 个标识符标记 / 外部同样命名的 17 个，注释被剥除，具有六个详尽的例外（关键字、三个被反驳声明的名称、绑定器 [s]、缺失的名称）；重命名模拟 7/7（[Eval]、[EvalBi]、[EvalAt]、[Partial_l]、[Partial_r]、[YoEvalAt]、[CatEval]，每个在整个复制文件中重命名，模块路径除外），每次在 posit 上首次中断五线[make todo] 仅通过那 4 行增长
 （2218 → 2222，相对于重定位后的基准 39e583d2），因此该问题的
 “没有新增命中”选项框按书面说明未满足；已披露。未交付。
 - 通过求值保留或创建极限（#425, #426）。
 - 对 [EvalAt]、[YoEvalAt] 或 [One_Eval] 进行别名或移除（第（6）项；已呈现）。[YoEval] 的箭头顺序未更改；其与该顺序的桥接是现有的 [yo_eval_map_alt]。
 - 替换 Theory/Lawvere/Sets.v 中 [ev1] 的主体（已呈现）；重新表达存在于探针中。
 - 在 [Cat] 的宇宙中进行的一般双变量求值，并去除了塌缩：塌缩属于 [Cat]，已测量并披露。
 - 未修改 Adjunction/Diagonal/Connected.v、Functor/Hom/Yoneda/Natural.v、Theory/Shapes.v、Theory/Lawvere/Sets.v 或 Functor/Bifunctor/Partial.v。
*)

Section Evaluation.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(* * ** The evaluation functor at a fixed object / * ** 在固定对象处的评价函子 *)

(*
 Mac Lane §V.3's E_c : [P, X] ⟶ X — objects to their value at p,
 transformations to their component at p.  The same data as
 Adjunction/Diagonal/Connected.v's [EvalAt] (measured, see the header);
 declared here in the light home the issue asks for. 

 --------
 Mac Lane §V.3 的 E_c :  [P, X]  ⟶ X — 对象在 p 点的值，变换到它们在 p 点的分量。与 Adjunction/Diagonal/Connected.v 的 [EvalAt] 相同的数据（已测量，见标题）；在此根据问题所需的情况声明。
*)
Program Definition Eval (p : P) : [P, X] ⟶ X := {|
  fobj := fun H => H p;
  fmap := fun _ _ s => transform[s] p
|}.

(** ** The two-variable evaluation / ** 双变量评估 *)

(*
 The bifunctor [P, X] ∏ P ⟶ X whose partial application at p is [Eval p].
 The arrow action is in [Cat_Closed]'s order, [fmap[K] f ∘ transform[s] p]
 (Instance/Fun/Eval/Cat.v shows the two agree at [eq_refl]); the other
 order, [transform[s] q ∘ fmap[H] f], is the same arrow by naturality and
 is the one Functor/Hom/Yoneda/Natural.v's [YoEval] uses. 

 --------
 双函子 [P, X] ∏ P ⟶ X，其在 p 处的部分应用为 [Eval p]。
 箭头作用在 [Cat_Closed] 的顺序中，[fmap[K] f ∘ transform [s] p]（Instance/Fun/Eval/Cat.v 显示两者在 [eq_refl] 处一致）；另一顺序，[transform[s] q ∘ fmap [H] f]，通过自然性是相同的箭头，并且是 Functor/Hom/Yoneda/Natural.v 的 [YoEval] 所使用的。
*)
Program Definition EvalBi : ([P, X] ∏ P) ⟶ X := {|
  fobj := fun Hp => fst Hp (snd Hp);
  fmap := fun Hp Kq sf =>
            fmap[fst Kq] (snd sf) ∘ transform[fst sf] (snd Hp)
|}.
Next Obligation.
  proper; simpl in *.
  rewrite H, X0; reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite comp_assoc, (naturality[t0] o1 o0 h), <- comp_assoc.
  reflexivity.
Qed.

(* * ** Partial application agrees with the fixed-object evaluation / * ** 部分应用与固定对象求值一致 *)

(* On objects: on the nose. / 关于物体：在鼻子上。 *)
Definition eval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(*
 On arrows: up to ≈ only — [Partial_l]'s action is [bimap s id], which
 still carries the [fmap id] the functor law removes (probe). 

 --------
 关于箭头：向上至 ≈ 仅 — [Partial_l] 的操作是 [bimap s id]，这仍然携带 [fmap id]，函子定律会去除（探测）。
*)
Lemma eval_partial_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[Eval p] s ≈ fmap[Partial_l EvalBi p] s.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(*
 Packaged as an isomorphism of functors in [[P, X], X], with identity
 components. 

 --------
 以 [[P, X] , X] 中函子同构的形式打包，具有恒等分量。
*)
Program Definition eval_partial_iso (p : P) :
  @Isomorphism ([[P, X], X]) (Eval p) (Partial_l EvalBi p) := {|
  to   := {| transform := fun H => id |};
  from := {| transform := fun H => id |}
|}.

(* The other partial application is the functor itself. / 另一个部分应用是函子本身。 *)
Definition eval_partial_r_obj (H : [P, X]) (p : P) :
  fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.

Lemma eval_partial_r_map (H : [P, X]) (p q : P) (f : p ~> q) :
  fmap[Partial_r EvalBi H] f ≈ fmap[H] f.
Proof. simpl; unfold bimap; simpl; cat. Qed.

(* * ** Naturality in the evaluated object / * ** 被评估对象的自然性 *)

(*
 Each arrow of P gives a transformation between evaluation functors,
 with component [fmap[H] f] at H; both naturality fields are the
 naturality of the transformation being evaluated. 

 --------
 P 的每个箭头都提供了评估函子之间的变换，其在 H 处的分量为 [fmap[H] f；两个自然性域都是正在被评估的变换的自然性。
*)
Program Definition Eval_nat {p q : P} (f : p ~> q) : Eval p ⟹ Eval q := {|
  transform := fun H => fmap[H] f
|}.
Next Obligation. symmetry; apply naturality. Qed.
Next Obligation. apply naturality. Qed.

(* Assembled: evaluation is a functor P ⟶ [[P, X], X]. / 组装：评估是一个函子 P ⟶ [[P, X] , X]. *)
Program Definition EvalFunctor : P ⟶ [[P, X], X] := {|
  fobj := Eval;
  fmap := fun _ _ f => Eval_nat f
|}.
Next Obligation. proper; rewrite X0; reflexivity. Qed.
Next Obligation. apply fmap_comp. Qed.

(* Its actions read back on the nose. / 它的行为显而易见。 *)
Definition EvalFunctor_obj (p : P) : fobj[EvalFunctor] p = Eval p := eq_refl.

Definition EvalFunctor_map {p q : P} (f : p ~> q) (H : [P, X]) :
  transform[fmap[EvalFunctor] f] H = fmap[H] f := eq_refl.

End Evaluation.

Arguments Eval {P X} p.
Arguments EvalBi {P X}.
Arguments EvalFunctor {P X}.
