Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Limit.

Generalizable All Variables.

(* * * Pointwise limits as creation along the discrete inclusion / * * 在离散包含下作为创生的逐点极限 *)

(*
 Mac Lane §V.3 Theorem 2 (book p. 116; maclane:V.3:thm2): precomposition
 with the inclusion of the discrete category |P| on the objects of P,
 [P, X] ⟶ [|P|, X], creates limits.  Riehl §3.4 Proposition 3.4.9
 (riehl:3.4:prop9): the evaluation functors jointly create limits — the
 analogue for [P, X] of her Exercise 3.4.v, which is about the projections
 of a PRODUCT of categories and is Construction/Product/Limit.v's
 [PiCat_JointlyCreateLimit]; for the “strictly” of her statement see NOT
 DELIVERED.
 nLab: https://ncatlab.org/nlab/show/created+limit
 https://ncatlab.org/nlab/show/discrete+category

 BACKGROUND.  Theorem 1 (Instance/Fun/Limit.v, #425) computes the limit of
 a diagram D : J ⟶ [P, X] pointwise, from limits of the evaluated diagrams
 Eval p ◯ D.  Theorem 2 restates this as a creation property: restricting
 a functor P ⟶ X to the discrete category |P| on its objects forgets the
 arrow part and keeps the object-indexed family, and a diagram of functors
 has a limit exactly when its diagram of families does — the pointwise
 limits assemble into the unique lift, and a cone upstairs whose image is
 limiting is limiting.  Riehl reads the same content off the family of
 evaluation functors: they jointly create limits.  Both statements are
 TRANSPORTS of Theorem 1, not parallel proofs (Work item 3): the
 reflection clause is [limitcone_transport] of #425's
 [PointwiseIsLimitCone] along an isomorphism of cones with identity
 components, and every lift IS #425's pointwise cone.

 STALE PREMISES, RE-MEASURED.
 - “The creation vocabulary is itself absent”: false since #406.
 Structure/Limit/Creation.v has [CreatesLimit] (with its fields
 [creates_lift], [creates_lift_over] and [creates_reflect], and with
 Mac Lane's limiting clause [creates_limiting] and uniqueness
 [creates_lift_unique] derived), [creates_limit_lift],
 [CreatesAllLimits],
 [creates_limits_Complete], [creates_limits_continuous],
 Riehl's [StrictLift] / [StrictlyCreatesLimit] with
 [self_lift], and [JointlyCreateLimit] (her Exercise 3.4.v).
 Structure/Limit.v's INDEX bullet records seven of them, not
 [creates_limit_lift], [CreatesAllLimits], [self_lift] or
 [JointlyCreateLimit] — the last is recorded in Construction/Product/
 Limit.v's bullet instead.
 - “No discrete subcategory on the objects of a category and no
 inclusion functor”: TRUE as stated ('discrete subcategory' has 0 hits
 in the tree's [.v] files; 'discrete inclusion' 2, both forward
 references in Instance/Fun/Limit.v), but the ingredient is richer than the issue
 says: Structure/Limit/Comparison.v has the ANNOTATED
 discrete-diagram functor [DiscreteCat_Functor'@{o h p uo uh up +}],
 and Instance/Fun/Discrete.v has [Fun_Discrete_PiCat : [DiscreteCat
 A, B] ≅[Cat] PiCat (fun _ => B)], the “C^{ob A} ≅ ∏_{ob A} C” of the
 Riehl note.  RECORDED CORRECTION: an earlier revision continued
 “That bridge is Set-PINNED in the target (it uses
 Instance/Discrete.v's unannotated [DiscreteCat_Functor]; at a
 general X the application is refused with ”Cannot enforce
 Set = …“), so Riehl's route through Construction/Product/
 Limit.v's [PiCat_JointlyCreateLimit] is NOT usable here”.
 The donor was annotated in place at Instance/Discrete.v in the
 PR “algebraic carriers are sets” (2026-09-17), so that [Set] pin
 no longer exists and the quoted refusal no longer occurs.
 Whether Riehl's route thereby becomes usable has NOT been
 re-measured; the reflection is proved directly here either way,
 and that direct proof is unaffected.
 - “Theory/Kan/Extension.v ([Induced])”: the line cited is a comment,
 the definition being a few lines below it; that no limit property
 of it existed is true
 (Functor/Construction/Postcompose.v says so in terms).
 - The Riehl note's “no evaluation functor out of a functor category at
 all” and “ls Instance/Fun/ contains exactly one file” are false:
 #424's [Eval] (Instance/Fun/Eval.v) and Adjunction/Diagonal/
 Connected.v's [EvalAt] exist; fourteen files besides this one.

 WHAT IS DELIVERED (34 named constants plus 9 [Program] obligations, every
 one closed under the global context).
 (1) THE INCLUSION AND THE RESTRICTION.  [ObjCat : Category@{jo jh jh} :=
 DiscreteCat (obj[P])] at P's own object and hom levels; [DiscInc :
 ObjCat ⟶ P] through [DiscreteCat_Functor']
 (RECORDED CORRECTION: an earlier revision explained that choice
 by “Instance/Discrete.v's unannotated [DiscreteCat_Functor]
 instantiates [DiscreteCat@{u Set Set}] and would pin P's hom and
 proof levels to [Set] — Structure/Limit/Comparison.v's note above
 its own annotated copy says so — and is left as it is”; since
 the PR “algebraic
 carriers are sets” (2026-09-17) [DiscreteCat_Functor] is itself
 annotated and [DiscreteCat_Functor'] is a transparent ALIAS of
 it, so the two are interchangeable here and the primed name is
 retained only to avoid a rename); [Res : [P, X] ⟶ [ObjCat, X] :=
 Induced DiscInc], the theorem's X^i.  Readbacks at [eq_refl]:
 [res_obj], [res_obj_at], [res_map], and [eval_res_obj]/
 [eval_res_map] — evaluating after restricting IS evaluating, in
 both functor fields.
 (2) REFLECTION (the new content; #425 has only the converse,
 [Eval_PreservesLimitCone], which takes [L]).  For [M : Cone D] with
 every [FCone (Eval p) M] limiting: [ptw_of_cone] (the pointwise
 limits M's evaluations provide), [ptw_apex_readback] and
 [ptw_leg_readback] (the assembled pointwise cone has M's apex and
 M's legs objectwise on the nose), [ptw_map_is_fmap] (the mediator
 between adjacent pointwise limits is M's own arrow action, by
 [plim_map_unique]), [ptw_apex_iso] (an isomorphism in [P, X] whose
 components are identities), [ptw_cone_iso : ConeIso M
 (PointwiseLimitCone D _)], and [Fun_pointwise_reflect : IsLimitCone
 M] := [limitcone_transport] of [PointwiseIsLimitCone] along it.
 (3) JOINT CREATION BY THE EVALUATIONS (the analogue of Riehl Exercise
 3.4.v).
 [ev_family p := Eval p], [ev_lift] (#425's pointwise cone assembled
 from the given family of limiting cones), [ev_lift_apex] and
 [ev_lift_leg] at [eq_refl], [ev_lift_over] (a [ConeIso] with
 [iso_id]), and [Fun_Eval_JointlyCreateLimit : JointlyCreateLimit D
 ev_family].  The image of the lift under [Eval p] is the given cone
 in apex and legs on the nose; the cone RECORDS do not convert, the
 coherence field being a rebuilt proof (probe N1).
 (4) CREATION ALONG THE RESTRICTION (Theorem 2), UNDER THE HYPOTHESIS
 [L : ∀ p, Limit (Eval p ◯ D)].  [res_comp_cone] (a cone over
 [Res ◯ D] evaluated at p), [res_ump_nat] (the mediator into a cone
 downstairs, componentwise the pointwise mediator; naturality over
 the discrete shape is discharged by the obligation tactic),
 [Res_preserves : IsLimitCone (FCone Res M)] for M with limiting
 evaluations, [res_coneiso_at] (an isomorphism of cones downstairs
 restricts to one at each object), [Res_CreatesLimit L : CreatesLimit
 D Res] — [creates_lift] the pointwise cone, [creates_lift_over] by
 [limitcone_iso], [creates_reflect] by [Fun_pointwise_reflect] after
 transporting along [res_coneiso_at] — its alias under the issue's
 name [discrete_inclusion_creates_limits] (ANNOTATED; see
 UNIVERSES), [res_limit L : Limit (Res ◯ D)], and [creation_apex]/
 [creation_leg] at [eq_refl]: the limit [creates_limit_lift] derives
 IS #425's [Functor_Category_pointwise_limit] in apex and legs.
 WHY THE HYPOTHESIS STAYS.  [creates_lift] must turn ONE limiting
 cone downstairs into a cone upstairs, i.e. read the components of a
 limiting cone in [|P|, X] as limiting cones in X.  Mac Lane does so
 silently (limits in a product of categories are computed in each
 factor); the constructive proof patches the apex family at one
 index — [fun q => if q = p then c else N q] — and so needs decidable
 equality on [obj P].  The tree made the same call before:
 Construction/Product/Limit.v ships [Fst_PreservesLimitCone]/
 [Snd_PreservesLimitCone] for the BINARY product (index
 [bool]) and, for [PiCat] at a general index type, only [pi_reflect]
 and [PiCat_JointlyCreateLimit] — no single-projection preservation
 — and #425's [Eval_PreservesLimitCone] takes [L] for the same
 reason.  A hypothesis-free [CreatesLimit D Res] over Construction/
 Quotient.v's [ObjDecEq P] is a follow-on, not written here.
 (5) COROLLARIES.  [Res_CreatesAllLimits (HX : Complete X)],
 [Res_Complete : Complete [P, X]] — completeness of [P, X] once more,
 now as an instance of Structure/Limit/Creation.v's general
 [creates_limits_Complete] (creation plus completeness of [|P|, X],
 the latter #425's [Functor_Category_Complete] at the discrete
 shape) — and [Res_continuous : PreservesLimitCone D Res] through
 [creates_limits_continuous] (Mac Lane §V.4 Theorem 2's SECOND half,
 Structure/Limit/Creation.v's own heading; an earlier revision
 said “first”).
 (6) STRICTNESS.  [strict_self : StrictLift D Res (FCone Res M) :=
 self_lift M]: every cone upstairs TAUTOLOGICALLY strictly lifts its
 own image (the donor's own word; it holds for every functor and
 says nothing specific to [Res]).
 Riehl's “strictly creates” (Definition 3.4.7; [StrictlyCreatesLimit],
 whose [slift_eq] is an [eq] of apexes) would need the canonical
 lift's image EQUAL to an arbitrary given cone's apex, an [eq]
 between functor records [DiscreteCat (obj P) ⟶ X] (probe N3 pins
 the refusal; N2 pins that a restricted functor is not even the
 discrete functor on its own object map — the arrow fields differ).

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 34
 constants).
 - [Res@{jo jh co ch u u0 u1}] carries exactly one equation, [jh = ch]
 ([Fun]'s), and leaves P's OBJECT level free: at a shape whose objects
 sit strictly ABOVE its homs ([Constraint smallh < bigo] in the probe's
 section Wide) [ObjCat Pw], [Res Pw Xw] and the type [[Pw, Xw] ⟶ [Pw,
 Xw]] are all accepted.  Seven constants share this freedom: [ObjCat],
 [DiscInc], [Res], [res_obj], [res_obj_at], [res_map], [strict_self].
 - The other 27 constants — every one that reaches [Eval] through its
 definition; 21 of them name it in their statements — inherit [jo <= jh] (P's objects ≤ P's homs; [u1 <= u2] or [u <= u0]
 in their blocks).  The FIRST CARRIER is the type [[P, X] ⟶ X] itself,
 not anything in this file or in #424's: [Fun]'s hom universe (a
 natural transformation quantifies over P's objects) sits above jo,
 and [Functor] identifies source and target hom universes, so a
 functor [P, X] ⟶ X forces jo ≤ ch = jh.  Probe N5 refuses the bare
 type [[Pw, Xw] ⟶ Xw] with “Cannot enforce smallh = … because smallh <
 bigo”; N6 refuses [@Eval Pw Xw]; N4 refuses #425's
 [Functor_Category_Complete Pw Xw].  [Res] is more universe-general
 than the theorem it serves.
 - The 20 section constants with J in context (PointwiseReflect,
 JointCreation, ResCreation) carry #425's four equations [u0 = u2],
 [u0 = u4], [u0 = u6], [u2 = u4] over [J : Category@{u u0 u0}], [P :
 Category@{u1 u2 u2}], [X : Category@{u3 u4 u4}]: J's hom = P's hom =
 X's hom = [P, X]'s hom.  The nine constants over [{P X}] alone
 ([eval_res_obj], [eval_res_map], [res_obj], [res_obj_at], [res_map],
 [Res_CreatesAllLimits], [Res_Complete], [Res_continuous],
 [strict_self]) carry [u0 = u2] only; [ev_family] [u2 = u4] only;
 [ObjCat] and [DiscInc] none.  The three corollaries, section constants
 over [{P X : Category}] with no annotation, keep P's object level
 distinct from its hom level ([u <= u0], never [u = u0]); [strict_self]
 relates the two not at all.
 - [discrete_inclusion_creates_limits] is ANNOTATED AT THE DEFINITION
 ([@{io jo co h +}], one hom level for J, P and X, which the four
 equations identify anyway): written bare over [{J P X : Category}],
 the alias minimized P's object universe onto its hom universe AND J's
 hom onto it ([{J : Category@{u2 u3 u3}} {P : Category@{u3 u3 u3}}],
 measured) — Instance/Fun/Limit.v's trap, now on a [:=] alias.
 Annotated it carries [jo <= h] and no equation.
 - STDLIB BOUNDS, absent from Instance/Fun/Limit.v, enter here through
 [DiscreteCat]: the 21 constants outside PointwiseReflect and
 JointCreation — a different set of 21 from the [Eval]-naming one
 above; these reach [ObjCat] or [Res] through their definitions —
 carry [jo <= eq.u0], [jo <= Logic_lemmas.equality.u0], [jh <=
 eq_ind.u0], [jh <= Logic_lemmas.equality.u0] and [jh <= eq_ind_r.u0]
 (first carrier [ObjCat], from [DiscreteCat]'s equality homs) and, all
 but [ObjCat], also [jh <= eq_rect_r.u1], [jh <=
 EqdepFacts.eq_sigT_sig_eq.u2] and [JMeq.u0 <= JMeq.u1] (first carrier
 [DiscInc], from [DiscreteCat_Functor']'s [match] on an equality).  The
 13 constants of PointwiseReflect and JointCreation carry none.  Ten
 constants ([creation_apex], [creation_leg],
 [discrete_inclusion_creates_limits], [Fun_Eval_JointlyCreateLimit],
 [Fun_pointwise_reflect], [res_coneiso_at], [Res_Complete],
 [Res_continuous], [Res_CreatesAllLimits], [Res_CreatesLimit]) also
 carry bounds into a non-local [Projections] module, inherited from
 Structure/Limit/Creation.v's [creates_limit_lift] and
 [creates_limits_Complete], not introduced here.  No word-bounded [Set]
 in any block.

 COUNTS AND CONVENTIONS.
 - 34 [.glob] declaration heads (33 [def], 1 [prf]) plus 9 [Program]
 obligations the [.glob] cannot see ([ptw_apex_iso] 6, [res_comp_cone]
 1, [res_ump_nat] 2), all “Closed under the global context”, zero
 [Axioms:] lines; the gate carries the 34 heads, fully qualified.
 - Six [Defined] ([ptw_cone_iso], [ev_lift_over],
 [Fun_Eval_JointlyCreateLimit], [Res_preserves], [res_coneiso_at],
 [Res_CreatesLimit]), each flipped to [Qed] alone in a copy of the
 file: only [Res_CreatesLimit] is LOAD-BEARING (the [creation_apex]
 readback is refused); the other five compile with the probe unchanged
 and stay transparent because their conclusions are data (isomorphisms
 of cones, a lift, a mediator).  Seven [Qed] tokens outside this
 header (one lemma, six obligations; the other three obligations are
 discharged by the obligation tactic).
 - Closure 52 files excluding self: Structure/Limit/Comparison.v costs
 11 at the margin (it is required for [DiscreteCat_Functor'] alone),
 Instance/Fun/Limit.v 9, Structure/Limit/Creation.v 1, Theory/Kan/
 Extension.v 1, the other twelve [Require]s 0.  Moving
 [DiscreteCat_Functor'] into Instance/Discrete.v would remove those 11
 and give its two consumers (Comparison.v and this file) one source;
 surfaced for the maintainer, not done.  Zero name collisions: each of
 the 34 names has 0 declaration hits elsewhere in the tree.
 - Test/ProbeFunCreation426.v mirrors the [Require] list and carries 7
 refutation commands (1 instrument + N1, N2, N3 CONVERSION + N4, N5, N6
 UNIVERSE), each stripped one at a time in a copy of the whole file,
 each beside its accepted controls; guard coverage 32 identifier tokens
 inside the refutations / 26 also named outside, comments stripped,
 with six exhaustive exceptions (the keyword, a binder, the three
 refuted declarations' names, the absent name); rename-simulated 13/13
 ([Res], [ObjCat], [ev_lift], [PointwiseLimit],
 [Functor_Category_Complete], [Res_CreatesLimit], [FCone],
 [DiscreteCat_Functor'], [Eval], [strict_self], [self_lift],
 [plim_obj], [Complete]; module paths excluded), every first break on
 a positive line.  [make todo] grows by those 7 lines only (2226 →
 2233), so the issue's “adds no new hits” box is not met as written;
 disclosed.
 - [(Eval p)] is parenthesised or applied inside a larger term
 throughout (Instance/Fun/Eval.v's header: bare at a definition-body
 head it parses as the [Eval … in] vernacular).
 - Two forward references in Instance/Fun/Limit.v now name
 this file; line-neutral (an earlier revision named a different
 pair of lines, corrected after measuring).

 NOT DELIVERED.
 - The COLIMIT half (Riehl: [ev] creates colimits too — the Riehl box of
 the issue): not one colimit line is written, and no issue carries it
 (#715 is pointwise colimits and cocompleteness of presheaves, not
 creation).
 - Riehl's STRICT creation ([StrictlyCreatesLimit]): see (6) and probes
 N2/N3.
 - A hypothesis-free [CreatesLimit D Res] (decidable object equality on
 P would give it; see (4)).
 - Riehl's route through [Fun_Discrete_PiCat] and
 [PiCat_JointlyCreateLimit] (not attempted; the [Set]-pin reason
 given for that is withdrawn — see STALE PREMISES).
 - No edit to Instance/Discrete.v, Structure/Limit/Comparison.v,
 Structure/Limit/Creation.v, Theory/Kan/Extension.v or Instance/Fun/
 Discrete.v. 

 --------
 Mac Lane §V.3 定理 2（书第 116 页；maclane:V.3:thm2）：与离散范畴 |P| 在 P 对象上的包含的预复合，[P, X] ⟶ [|P|, X]，会产生极限。Riehl §3.4 命题 3.4.9（riehl:3.4:prop9）：评价函子联合地产生极限——这是 [P, X] 对应她练习 3.4.v 的类比，该练习关于范畴乘积的投影，并且是 Construction/Product/Limit.v 的 [PiCat_JointlyCreateLimit]；关于她表述的“严格”性，请参见 NOT DELIVERED。nLab: https://ncatlab.org/nlab/show/created+limit https://ncatlab.org/nlab/show/discrete+category背景。定理 1（Instance/Fun/Limit.v，#425）计算了一个图 D : J ⟶ [P, X] 的逐点极限，其基于已求值图 Eval p ◯ D 的极限。定理 2 将其重新表述为创建性质：将函子 P ⟶ X 限制在其对象组成的离散范畴 |P| 上，会忽略箭头部分并保留对象索引的族，当且仅当函子图的族图存在极限时，函子图也存在极限——逐点极限会组装成唯一的提升，并且一个在上层的圆锥，其像为极限，则该圆锥也是极限。Riehl 从评价函子族读出相同的内容：它们联合地创建极限。这两个陈述都是定理1的变换，而不是平行证明（工作项3）：反射子句是#425的[PointwiseIsLimitCone]沿着具有恒等分量的锥同构的[limitcone_transport]，并且每个提升都是#425的逐点锥。陈旧的前提，重新测量。- “创造的词汇本身缺失”：自 #406 起为假。Structure/Limit/Creation.v 包含 [CreatesLimit]（及其字段 [creates_lift]、[creates_lift_over] 和 [creates_reflect]，以及 Mac Lane 的限制条款 [creates_limiting] 和派生的唯一性 [creates_lift_unique]），[creates_limit_lift]，[CreatesAllLimits]，[creates_limits_Complete]，[creates_limits_continuous]，Riehl 的 [StrictLift] / [StrictlyCreatesLimit] 及 [self_lift] 和 [JointlyCreateLimit]（她的练习 3.4.v）。Structure/Limit.v 的 INDEX 项目记录了其中七项，而不是 [creates_limit_lift]、[CreatesAllLimits]、[self_lift] 或 [JointlyCreateLimit]——最后一项记录在 Construction/Product/Limit.v 的项目中。- “一个范畴的对象上没有离散子范畴，也没有包含函子”：如所述为真（‘discrete subcategory’ 在树的 [.v] 文件中有 0 个命中；‘discrete inclusion’ 有 2 个，都是 Instance/Fun/Limit.v 中的前向引用），但组成部分比问题所述的要丰富：Structure/Limit/Comparison.v 中有标注的离散图函子 [DiscreteCat_Functor'@{o h p uo uh up +}]，Instance/Fun/Discrete.v 中有 [Fun_Discrete_PiCat : [DiscreteCat A, B] ≅ [Cat] PiCat (fun _ => B)]，即 Riehl 笔记中的 “C^{ob A} ≅ ∏_{ob A} C”.记录的更正：早期修订继续：“那座桥在目标中已固定（它使用 Instance/Discrete.v 中未标注的 [DiscreteCat_Functor]；在一般 X 上应用会被拒绝，提示‘无法执行 Set = …’），因此 Riehl 通过 Construction/Product/Limit.v 的 [PiCat_JointlyCreateLimit] 的路径在这里不可用。”在 PR “代数承载是集合”（2026-09-17）中，捐赠者已在 Instance/Discrete.v 中替换为带标注版本，因此该 [Set] 引脚不再存在，也不再发生引述的拒绝。不论 Riehl 的路径是否因此变得可用，都尚未重新测量；在这里反射定理无论如何都是直接证明的，并且该直接证明不受影响。- “Theory/Kan/Extension.v ([Induced])”：引用的这一行是注释，定义在它的下面几行；说它不存在限制性质是正确的（Functor/Construction/Postcompose.v 术语中是这么说的）。- Riehl 笔记中“没有从函子范畴到外部的评估函子”和“ls Instance/Fun/ 正好包含一个文件”是错误的：#424 的 [Eval]（Instance/Fun/Eval.v）和 Adjunction/Diagonal/Connected.v 的 [EvalAt] 存在；除了这个之外还有十四个文件。交付的内容是什么（34 个命名常量加上 9 个 [Program] 义务，每一个都在全局上下文中闭合）。(1) 包含和限制。[ObjCat : Category@{jo jh jh} :=
 DiscreteCat (obj [P] )] 在 P 自身的对象和同态层面；[DiscInc :
 ObjCat ⟶ P] 通过 [DiscreteCat_Functor'] 
 （已记录更正：早期版本解释了该选择是因为 “Instance/Discrete.v 未注释的 [DiscreteCat_Functor] 
 实例化了 [DiscreteCat@{u Set Set}]，并会将 P 的同态和证明层级固定到 [Set] — Structure/Limit/Comparison.v 上方的已注释副本也说明了这一点 — 并保持不变”；自从 PR “代数承载是集合”（2026-09-17） 以来 [DiscreteCat_Functor] 本身被注释，[DiscreteCat_Functor'] 是它的透明别名，因此这里两者可互换，带撇号的名称仅保留下来以避免重命名）；[Res : [P, X] ⟶ [ObjCat, X] :=
 诱导的 DiscInc], 定理的 X^i。[eq_refl] 的回读：
 [res_obj]、[res_obj_at]、[res_map] 和 [eval_res_obj] /
 [eval_res_map] — 在限制后进行评估就是在两个函子字段中进行评估。(2) 反思（新内容；#425 仅有相反的 [Eval_PreservesLimitCone]，它取 [L]）。对于 [M : Cone D]，具有每个 [FCone (Eval p) M] 的极限：[ptw_of_cone]（点态极限 M 的评估提供的），[ptw_apex_readback] 和 [ptw_leg_readback]（组装的点态锥的顶点为 M，M 的各条腿在对象上精确匹配），[ptw_map_is_fmap]（相邻点态极限之间的中介是 M 自身的箭头作用，通过 [plim_map_unique]），[ptw_apex_iso]（[P, X] 中的一个同构，其组件是恒等映射）、[ptw_cone_iso : ConeIso M (PointwiseLimitCone D _)]，以及 [Fun_pointwise_reflect : IsLimitCone M] := [limitcone_transport] 沿着它的 [PointwiseIsLimitCone]。（3）由评估的联合创建（Riehl 练习 3.4.v 的类似物）。[ev_family p := Eval p]，[ev_lift]（#425 的点态圆锥由给定的极限圆锥族组装而成），[ev_lift_apex] 和 [ev_lift_leg] 在 [eq_refl]，[ev_lift_over]（一个带有 [iso_id] 的 [ConeIso]），以及 [Fun_Eval_JointlyCreateLimit : JointlyCreateLimit Dev_family]。在 [Eval p] 下提升的像是在顶点和边上与给定圆锥完全一致；圆锥的 RECORDS 不会转换，其一致性字段为重建的证明（探针 N1）。（4）沿限制创生（定理 2），在假设 [L : ∀ p, Limit (Eval p ◯ D)] 下。[res_comp_cone]（在 p 处评估的 [Res ◯ D] 的锥），[res_ump_nat]（下层锥的中介，按分量为按点中介；离散形状上的自然性由 obligation 策略处理），[Res_preserves : IsLimitCone (FCone Res M)] 对于具有极限评估的 M，[res_coneiso_at]（下层锥的同构在每个对象上限制为一个同构），[Res_CreatesLimit L: CreatesLimit D Res] — [creates_lift] 点状锥，[creates_lift_over] 由 [limitcone_iso]，[creates_reflect] 由 [Fun_pointwise_reflect] 在沿 [res_coneiso_at] 传输后 — 它在问题名称下的别名 [discrete_inclusion_creates_limits]（带注释；参见 UNIVERSES），[res_limit L : Limit (Res ◯ D)]，以及 [creation_apex] / [creation_leg] 在 [eq_refl]: 极限 [creates_limit_lift] 推导 apex 和 legs 中 IS #425 的 [Functor_Category_pointwise_limit]。为什么假设成立。[creates_lift] 必须将楼下的一个限制锥变为楼上的锥，即将 [|P|, X] 中限制锥的组成部分作为 X 中的限制锥来读取。Mac Lane 默默地这样做（在一个类别的积中计算极限是在每个因子中进行的）；构造性证明在一个索引——[fun q => if q = p then c else N q]——上修补顶点族，因此需要 [obj P] 上可判定的相等性。树之前做了相同的调用：Construction/Product/Limit.v 提供了 BINARY 积（索引 [bool]）的 [Fst_PreservesLimitCone] / [Snd_PreservesLimitCone]，并且对于通用索引类型的 [PiCat]，只提供 [pi_reflect] 和 [PiCat_JointlyCreateLimit]——没有单投影保持——#425 的 [Eval_PreservesLimitCone] 出于相同原因采用 [L]。一个无假设的 [CreatesLimit D Res] 关于 Construction/Quotient.v 的 [ObjDecEq P] 是后续内容，这里没有写出。(5) 推论。[Res_CreatesAllLimits (HX : Complete X)], [Res_Complete : Complete [P, X]] — [P, X] 的完备性再次出现，现在作为 Structure/Limit/Creation.v 的一般 [creates_limits_Complete]（创建加上 [|P|, X] 的完备性，后者是 #425 的 [Functor_Category_Complete] 在离散形状下）— 以及 [Res_continuous : PreservesLimitCone D Res] 通过 [creates_limits_continuous]（Mac Lane §V.4 定理 2 的后半部分，Structure/Limit/Creation.v 自身的标题；早先的修订版写的是“前半部分”）。(6) 严格性。[strict_self : StrictLift D Res (FCone Res M) := self_lift M]：每一个楼上圆锥在演绎上严格提升它自己的图像（捐赠者自己的词；对每一个函子都成立，并且不针对 [Res] 说任何特定内容）。Riehl 的“严格创造”（定义 3.4.7；[StrictlyCreatesLimit]，其 [slift_eq] 是顶点的 [eq]）需要规范提升的图像等于任意给定圆锥的顶点，一个 [eq] 在函子记录 [DiscreteCat (obj P) ⟶ X] 之间（探针 N3 固定了拒绝；N2 固定了受限函子甚至不是其自身对象映射上的离散函子——箭头域不同）。宇宙（由 [About] 在 [Set Printing Universes] 下的所有 34 个常量中测量）。- [Res@{jo jh co ch u u0 u1}] 精确地包含一个方程，[jh = ch]（[Fun] 的），并且保留 P 的 OBJECT 级别自由：在一个其对象严格位于其 homs 之上的形状中（[Constraint smallh < bigo] 在探针的 Wide 部分）[ObjCat Pw]、[Res Pw Xw] 和类型 [[Pw, Xw] ⟶ [Pw, Xw]] 都被接受。有七个常量共享这种自由：[ObjCat]、[DiscInc]、[Res]、[res_obj]、[res_obj_at]、[res_map]、[strict_self]。- 其他 27 个常量——每一个通过其定义达到 [Eval] 的常量；其中 21 个在其陈述中命名它——继承 [jo <= jh]（P 的对象 ≤ P 的 homs；在它们的块中为 [u1 <= u2] 或 [u <= u0]）。第一个载体是类型 [[P, X] ⟶ X] 本身，
 而不是此文件中的任何内容或 #424 中的：[Fun] 的函子宇宙（自然变换在 P 的对象上量化）位于 jo 之上，
 而 [Functor] 识别源和目标函子宇宙，因此函子 [P, X] ⟶ X 强制 jo ≤ ch = jh。探测器 N5 拒绝裸类型 [[Pw, Xw] ⟶ Xw] 并显示“无法强制 smallh = … 因为 smallh < bigo”；N6 拒绝 [@Eval Pw Xw]；N4 拒绝 #425 的 [Functor_Category_Complete Pw Xw]。[Res] 比其所服务的定理具有更普遍的宇宙泛化。- 具有 J 的上下文中的 20 个节常数（PointwiseReflect、JointCreation、ResCreation）承载 #425 的四个方程 [u0 = u2]、[u0 = u4]、[u0 = u6]、[u2 = u4] 在 [J : Category@{u u0 u0}] 上，[P：Category@{u1 u2 u2}]，[X : Category@{u3 u4 u4}]：J 的 hom = P 的 hom = X 的 hom = [P, X] 的 hom。仅在 [{P X}] 上的九个常数（[eval_res_obj]、[eval_res_map]、[res_obj]、[res_obj_at]、[res_map]、[Res_CreatesAllLimits]、[Res_Complete]、[Res_continuous]、[strict_self]）仅承载 [u0 = u2]；[ev_family] [u2 = u4] 仅承载 [ObjCat] 和 [DiscInc] 不承载任何。三个推论，即在 [{P X : Category}] 上未标注的节常数，保持 P 的对象层与其 hom 层的区别（[u <= u0]，从不 [u = u0]）；[strict_self] 完全没有关联这两者。- [discrete_inclusion_creates_limits] 在定义处有注释（[@{io jo co h +}]，对于 J、P 和 X 的同态层次，四个方程无论如何都会识别）：直接写在 [{J P X : Category}] 上，别名将 P 的对象宇宙最小化到其同态宇宙，并将 J 的同态映射到其中（[{J : Category@{u2 u3 u3}} {P : Category@{u3 u3 u3}}]，已测量）——Instance/Fun/Limit.v 的陷阱，现在在 [:=] 别名上。注释中包含 [jo <= h]，并且没有方程。- STDLIB BOUNDS，缺失于 Instance/Fun/Limit.v，通过 [DiscreteCat] 进入：这是 PointwiseReflect 和 JointCreation 之外的 21 个常量——与上面命名的 [Eval] 不同的一组 21 个常量；它们通过各自的定义达到 [ObjCat] 或 [Res] ——携带 [jo <= eq.u0]、[jo <= Logic_lemmas.equality.u0]、[jh <= eq_ind.u0]、[jh <= Logic_lemmas.equality.u0] 和 [jh <= eq_ind_r.u0]（第一个载体 [ObjCat]，来自 [DiscreteCat] 的等式同态）并且，除了 [ObjCat] 外，也携带 [jh <= eq_rect_r.u1]、[jh <= EqdepFacts.eq_sigT_sig_eq.u2] 和 [JMeq.u0 <= JMeq.u1]（第一个载体 [DiscInc]，来自 [DiscreteCat_Functor'] 上关于等式的 [match]）。PointwiseReflect 和 JointCreation 的 13 个常量没有携带任何值。十个常量（[creation_apex]、[creation_leg]、[discrete_inclusion_creates_limits]、[Fun_Eval_JointlyCreateLimit]、[Fun_pointwise_reflect]、[res_coneiso_at]、[Res_Complete]、[Res_continuous]、[Res_CreatesAllLimits]、[Res_CreatesLimit]）也将界限传递到一个非本地的[Projections]模块，该模块继承自Structure/Limit/Creation.v的[creates_limit_lift]和[creates_limits_Complete]，这里未引入。任何块中都没有字界限的[Set]。计数和约定。- 34 个 [.glob] 声明头（33 个 [def]，1 个 [prf]）加上 9 个 [Program] 义务，[.glob] 无法看到（[ptw_apex_iso] 6，[res_comp_cone] 1，[res_ump_nat] 2），全部“在全局上下文下关闭”，行数为零 [Axioms:]；该门携带 34 个头，完全合格。- 六个 [Defined]（[ptw_cone_iso]，[ev_lift_over]，[Fun_Eval_JointlyCreateLimit]，[Res_preserves]，[res_coneiso_at]，[Res_CreatesLimit]），每个都翻转到 [Qed] 在文件的副本中单独存在：只有 [Res_CreatesLimit] 是承重的（[creation_apex] 读回被拒绝）；其他五个在探针未更改的情况下编译，并保持透明，因为它们的结论是数据（锥体的同构、提升、调解者）。在此标题之外有七个 [Qed] 代币（一个引理，六个公设；另外三个公设由公设策略解除）。- 关闭 52 个文件（不包括自身）：Structure/Limit/Comparison.v 在边际成本为 11（仅对 [DiscreteCat_Functor'] 必需），Instance/Fun/Limit.v 为 9，Structure/Limit/Creation.v 为 1，Theory/Kan/Extension.v 为 1，其余十二个 [Require] 为 0。将 [DiscreteCat_Functor'] 移至 Instance/Discrete.v 可以移除那 11 并为其两个使用者（Comparison.v 和此文件）提供一个来源；显示给维护者，但未执行。零名称冲突：34 个名称中的每一个在树的其他地方声明命中为 0。- Test/ProbeFunCreation426.v 镜像 [Require] 列表并包含 7 个反驳命令（1 个工具 + N1、N2、N3 转换 + N4、N5、N6 宇宙），每次在整个文件的副本中逐一剥离，每个命令旁边都有其已接受的控制；在反驳中覆盖 32 个标识符标记 / 在外部也命名了 26 个，注释已剥离，有六个详尽例外（关键字、一个绑定器、三个被反驳声明的名字、缺失的名字）；重命名模拟 13/13（[Res]、[ObjCat]、[ev_lift]、[PointwiseLimit]、[Functor_Category_Complete]、[Res_CreatesLimit]、[FCone]、[DiscreteCat_Functor']、[Eval]、[strict_self]、[self_lift]、[plim_obj]、[Complete]；模块路径已排除），每个首次中断都在一个正行。[make todo] 仅在那 7 行上增长（2226 → 2233），因此按原文所述，“没有新增命中”的问题框不不符合要求；已披露。 - [(Eval p)] 在整个过程中都被括号或应用于更大的术语中（Instance/Fun/Eval.v 的头部：在定义体头部的裸露位置，它被解析为 [Eval … in] 的俗语）。 - Instance/Fun/Limit.v 中的两个前向引用现在指向此文件；与行无关（先前的修订命名了另一对行，在测量后已更正）。未交付。
 - COLIMIT 部分（Riehl: [ev] 也会创建余极限 — 这个问题的 Riehl 框）：没有写一条余极限线，也没有任何问题包含它（#715 是逐点余极限和预层的余完备性，不是创建）。
 - Riehl 的严格创建（[StrictlyCreatesLimit]）：见 (6) 及探针 N2/N3。
 - 无假设的 [CreatesLimit D Res]（P 上可判定的对象相等会提供它；见 (4)）。
 - Riehl 通过 [Fun_Discrete_PiCat] 和 [PiCat_JointlyCreateLimit] 的路径（未尝试；为此给出的 [Set] 固定理由已撤回 — 见过时前提）。
 - 未对 Instance/Discrete.v、Structure/Limit/Comparison.v、Structure/Limit/Creation.v、Theory/Kan/Extension.v 或 Instance/Fun/Discrete.v 进行编辑。
*)

(* * ** The object-discrete inclusion and the restriction functor / * ** 对象-离散包含与限制函子 *)

Section Restriction.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(* |P|: the discrete category on the objects of P. / |P|：P 的对象上的离散范畴。 *)
Definition ObjCat : Category@{jo jh jh} := DiscreteCat@{jo jh jh} (obj[P]).

(*
 The inclusion |P| ⟶ P, through Structure/Limit/Comparison.v's
 discrete-diagram functor.  An earlier revision of this comment explained
 the choice by “Instance/Discrete.v's unannotated one pins the target's hom
 and proof levels to [Set]”; since the PR “algebraic carriers are sets”
 (2026-09-17) that donor is annotated and [DiscreteCat_Functor'] is a
 transparent alias of it, so either name works here. 

 --------
 通过 Structure/Limit/Comparison.v 的离散图函子包含 |P| ⟶ P。该评论的早期版本通过“Instance/Discrete.v 的未注释项将目标的同态和证明级别固定为 [Set]”解释了这一选择；自从 PR “代数载体是集合”（2026-09-17）之后，该捐赠者已经被注释，而 [DiscreteCat_Functor'] 是它的透明别名，因此这里使用任一名称都可以。
*)
Definition DiscInc : ObjCat ⟶ P := DiscreteCat_Functor' (fun p : P => p).

(*
 Restriction along the inclusion: precomposition, Theory/Kan/Extension.v's
 [Induced]. 

 --------
 沿包含的限制：前组合，理论/Kan/Extension.v 的 [Induced]。
*)
Definition Res : [P, X] ⟶ [ObjCat, X] := @Induced ObjCat P DiscInc X.

End Restriction.

Section Readbacks.

Context {P X : Category}.

Definition res_obj (H : [P, X]) : fobj[@Res P X] H = H ◯ DiscInc := eq_refl.

Definition res_obj_at (H : [P, X]) (p : P) :
  fobj[fobj[@Res P X] H] p = fobj[H] p := eq_refl.

Definition res_map (H K : [P, X]) (s : H ~{[P, X]}~> K) (p : P) :
  transform[fmap[@Res P X] s] p = transform[s] p := eq_refl.

(* Evaluating after restricting IS evaluating, in both data fields. / 在限制后的评估是评估，在两个数据字段中都是如此。 *)
Definition eval_res_obj (p : P) (H : [P, X]) :
  fobj[(@Eval ObjCat X p) ◯ (@Res P X)] H = fobj[@Eval P X p] H := eq_refl.

Definition eval_res_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[(@Eval ObjCat X p) ◯ (@Res P X)] s = fmap[@Eval P X p] s := eq_refl.

End Readbacks.

(* * ** Reflection: a cone whose every evaluation is limiting is limiting / * ** 反思：每次评估都是极限的圆锥就是极限的 *)

Section PointwiseReflect.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(*
 From a cone M in [P, X] all of whose evaluations are limiting, the
 pointwise limit data #425's construction consumes. 

 --------
 从 [P, X] 中的一个锥 M 出发，其所有评估都是极限，点态极限数据 #425 的构造被消耗。
*)
Definition ptw_of_cone (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) : Limit (Eval p ◯ D) :=
  limitcone_limit (FCone (Eval p) M) (H p).

(* The assembled pointwise cone has M's apex and M's legs, objectwise on the nose. / 组装的逐点锥体有 M 的顶点和 M 的边，在物体上位于鼻子处。 *)
Definition ptw_apex_readback (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) :
  fobj[PointwiseLimit D (ptw_of_cone M H)] p = fobj[vertex_obj[M]] p := eq_refl.

Definition ptw_leg_readback (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) (j : J) :
  transform[cone_leg (PointwiseLimitCone D (ptw_of_cone M H)) j] p
    = transform[cone_leg M j] p := eq_refl.

(* The mediator between adjacent pointwise limits IS M's own arrow action, by the uniqueness of the arrow part. / 相邻点极限之间的中介是 M 自身的箭头作用，依据箭头部分的唯一性。 *)
Lemma ptw_map_is_fmap (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) {x y : P} (f : x ~{P}~> y) :
  plim_map D (ptw_of_cone M H) f ≈ fmap[vertex_obj[M]] f.
Proof.
  apply (plim_map_unique D (ptw_of_cone M H) f).
  intro j.
  symmetry; exact (naturality[cone_leg M j] _ _ f).
Qed.

(* ... so the two cones are isomorphic with IDENTITY components. / ...所以这两个圆锥在恒等分量下是同构的。 *)
Program Definition ptw_apex_iso (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  @Isomorphism ([P, X]) (vertex_obj[M]) (PointwiseLimit D (ptw_of_cone M H)) := {|
  to   := {| transform := fun p => id |};
  from := {| transform := fun p => id |}
|}.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation. rewrite ptw_map_is_fmap; cat. Qed.

Definition ptw_cone_iso (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  ConeIso M (PointwiseLimitCone D (ptw_of_cone M H)).
Proof.
  exists (ptw_apex_iso M H).
  intros j p; simpl.
  apply id_right.
Defined.

(*
 THE REFLECTION — Theorem 1 reformulated: a transport of #425's
 [PointwiseIsLimitCone], not a parallel proof. 

 --------
 反射——定理 1 重新表述：#425 的 [PointwiseIsLimitCone] 的传输，而不是平行证明。
*)
Definition Fun_pointwise_reflect (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) : IsLimitCone M :=
  limitcone_transport (ConeIso_sym (ptw_cone_iso M H))
    (PointwiseIsLimitCone D (ptw_of_cone M H)).

End PointwiseReflect.

(* * ** The family of evaluations jointly creates limits (Riehl Ex 3.4.v) / * ** 评估的集合共同创建界限 (Riehl Ex 3.4.v) *)

Section JointCreation.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

Definition ev_family (p : obj[P]) : [P, X] ⟶ X := (Eval p).

(* The lift is #425's pointwise cone, assembled from the given family. / 该提升是由给定族组装而成的 #425 的逐点锥。 *)
Definition ev_lift (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) : Cone D :=
  PointwiseLimitCone D (fun p => limitcone_limit (N p) (HN p)).

(* The image of the lift under [Eval p] is the given cone in APEX and LEGS on the nose; the whole records do not convert (probe). / 在 [Eval p] 下电梯的图像是在鼻子上的 APEX 和 LEGS 中给定的锥体；整个记录无法转换（探针）。 *)
Definition ev_lift_apex (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) :
  vertex_obj[FCone (Eval p) (ev_lift N HN)] = vertex_obj[N p] := eq_refl.

Definition ev_lift_leg (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) (x : J) :
  cone_leg (FCone (Eval p) (ev_lift N HN)) x = cone_leg (N p) x := eq_refl.

Definition ev_lift_over (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) :
  ConeIso (FCone (Eval p) (ev_lift N HN)) (N p).
Proof.
  exists iso_id.
  intro x; simpl; apply id_right.
Defined.

Definition Fun_Eval_JointlyCreateLimit : JointlyCreateLimit D ev_family.
Proof.
  unshelve refine {| jcreates_lift := ev_lift |}.
  - exact ev_lift_over.
  - exact (Fun_pointwise_reflect D).
Defined.

End JointCreation.

(* * ** Creation along the restriction functor / * ** 沿着限制函子进行的创建 *)

Section ResCreation.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* A cone over [Res ◯ D] in [|P|, X], evaluated at an object p. / 在 [|P|, X] 中针对对象 p 评估的 [Res ◯ D] 上的锥体。 *)
Program Definition res_comp_cone (N : Cone (@Res P X ◯ D)) (p : P) :
  Cone (Eval p ◯ D) := {|
  vertex_obj := fobj[vertex_obj[N]] p;
  coneFrom := {| vertex_map := fun j => transform[cone_leg N j] p |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
  simpl in Hc; apply Hc.
Qed.

(*
 The mediator into the restricted cone: componentwise the pointwise
 mediator; naturality over the discrete shape is free. 

 --------
 受限圆锥中的中介者：按分量是逐点的中介者；在离散形状上的自然性是自由的。
*)
Program Definition res_ump_nat (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (N : Cone (@Res P X ◯ D)) :
  vertex_obj[N] ~{[@ObjCat P, X]}~> fobj[@Res P X] (vertex_obj[M]) := {|
  transform := fun p => unique_obj (H p (res_comp_cone N p))
|}.

(*
 PRESERVATION: a cone all of whose evaluations are limiting has a limiting
 image under [Res]. 

 --------
 保持性：一个所有评估都是极限的锥体在 [Res] 下有一个极限像。
*)
Definition Res_preserves (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  IsLimitCone (FCone (@Res P X) M).
Proof.
  intro N.
  unshelve refine {| unique_obj := res_ump_nat M H N |}.
  - intros j p; simpl.
    exact (unique_property (H p (res_comp_cone N p)) j).
  - intros v Hv p; simpl.
    exact (uniqueness (H p (res_comp_cone N p)) (transform[v] p)
             (fun j => Hv j p)).
Defined.

(* An isomorphism of cones downstairs restricts to one at each object. / 下层圆锥的同构限制在每个对象上也是同构。 *)
Definition res_coneiso_at (L : ∀ p : P, Limit (Eval p ◯ D)) (M : Cone D)
  (i : ConeIso (FCone (@Res P X) M) (FCone (@Res P X) (PointwiseLimitCone D L)))
  (p : P) :
  ConeIso (FCone (Eval p) M) (FCone (Eval p) (PointwiseLimitCone D L)).
Proof.
  exists (fobj_iso (@Eval (@ObjCat P) X p) _ _ (`1 i)).
  intro x.
  exact (`2 i x p).
Defined.

(*
 CREATION — Mac Lane §V.3 Theorem 2 — under the hypothesis that the
 pointwise limits exist (the header explains why the hypothesis stays). 

 --------
 创造 — Mac Lane §V.3 定理 2 — 在点态极限存在的假设下（标题解释了为什么假设成立）。
*)
Definition Res_CreatesLimit (L : ∀ p : P, Limit (Eval p ◯ D)) :
  CreatesLimit D (@Res P X).
Proof.
  unshelve refine {| creates_lift := fun N HN => PointwiseLimitCone D L |}.
  - intros N HN.
    exact (limitcone_iso
             (Res_preserves (PointwiseLimitCone D L)
                (fun p => Eval_pointwise_IsLimitCone D L p)) HN).
  - intros M HM.
    apply (Fun_pointwise_reflect D M).
    intro p.
    apply (limitcone_transport
             (ConeIso_sym
                (res_coneiso_at L M
                   (limitcone_iso HM
                      (Res_preserves (PointwiseLimitCone D L)
                         (fun q => Eval_pointwise_IsLimitCone D L q))) p))).
    exact (Eval_pointwise_IsLimitCone D L p).
Defined.

(* The limit downstairs that the pointwise limits give. / 楼下的极限是点逐极限给出的。 *)
Definition res_limit (L : ∀ p : P, Limit (Eval p ◯ D)) : Limit (@Res P X ◯ D) :=
  limitcone_limit (FCone (@Res P X) (PointwiseLimitCone D L))
    (Res_preserves (PointwiseLimitCone D L)
       (fun p => Eval_pointwise_IsLimitCone D L p)).

(* The creation-derived limit IS #425's pointwise limit, apex and legs on the nose. / 由创造衍生的极限是 #425 的逐点极限，顶点和支腿在鼻子上。 *)
Definition creation_apex (L : ∀ p : P, Limit (Eval p ◯ D)) :
  vertex_obj[@limit_cone _ _ _ (creates_limit_lift (Res_CreatesLimit L) (res_limit L))]
  = vertex_obj[@limit_cone _ _ _ (Functor_Category_pointwise_limit D L)] := eq_refl.

Definition creation_leg (L : ∀ p : P, Limit (Eval p ◯ D)) (j : J) (p : P) :
  transform[cone_leg (@limit_cone _ _ _
    (creates_limit_lift (Res_CreatesLimit L) (res_limit L))) j] p
  = transform[cone_leg (@limit_cone _ _ _
    (Functor_Category_pointwise_limit D L)) j] p := eq_refl.

End ResCreation.

(*
 The issue's name for the theorem, an alias of [Res_CreatesLimit] with the
 same hypothesis.  ANNOTATED: written bare over [{J P X : Category}] the
 alias minimized P's object universe onto its hom universe and J's hom
 onto it (measured; the header records the block).  One hom level [h]
 serves J, P and X, which [Res_CreatesLimit]'s four equations identify
 anyway. 

 --------
 该定理的问题名称，是 [Res_CreatesLimit] 的一个别名，具有相同的假设。注释：在 [{J P X : Category}] 上直接书写，该别名将 P 的对象宇宙最小化到其同态宇宙，并将 J 的同态映射到其中（已测量；标题记录了该块）。一个同态层 [h] 同时服务于 J、P 和 X，而 [Res_CreatesLimit] 的四个方程无论如何都能识别它们。
*)
Definition discrete_inclusion_creates_limits@{io jo co h +}
  {J : Category@{io h h}} {P : Category@{jo h h}} {X : Category@{co h h}}
  (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)) :
  CreatesLimit D (@Res P X) := Res_CreatesLimit D L.

(** ** Corollaries / ** 推论 *)

Section Corollaries.

Context {P X : Category}.

Definition Res_CreatesAllLimits (HX : @Complete X) : CreatesAllLimits (@Res P X) :=
  fun J D => Res_CreatesLimit D (fun p => HX J (Eval p ◯ D)).

(*
 Completeness of [P, X] once more, now through Structure/Limit/Creation.v's
 general theorem (creation + a complete target). 

 --------
 通过 Structure/Limit/Creation.v 的一般定理（创生 + 一个完整的目标），再次证明 [P, X] 的完备性。
*)
Definition Res_Complete (HX : @Complete X) : @Complete ([P, X]) :=
  creates_limits_Complete (@Res P X) (Functor_Category_Complete HX)
    (Res_CreatesAllLimits HX).

Definition Res_continuous (HX : @Complete X) (J : Category) (D : J ⟶ [P, X]) :
  PreservesLimitCone D (@Res P X) :=
  creates_limits_continuous (@Res P X) (Functor_Category_Complete HX)
    (Res_CreatesAllLimits HX) J D.

End Corollaries.

(* * ** Strictness: what converts and what does not / * ** 严格程度：什么可以转换，什么不可以 *)

Section Strictness.

Context {P X : Category}.

(*
 The object action of the restriction is the identity ([res_obj_at]
 above). Every cone upstairs strictly lifts its own image (Structure/Limit/
 Creation.v's [self_lift]); Riehl's “strictly creates” would need every
 cone DOWNSTAIRS to be such an image on the nose, an [eq] between functor
 records that does not hold (probe). 

 --------
 该限制的对象作用是恒等（上面的 [res_obj_at]）。每个楼上的锥严格地提升它自己的像（Structure/Limit/Creation.v 的 [self_lift]）；Riehl 的“严格创造”需要楼下的每个锥都恰好是这样的像，一个在函子之间记录的 [eq] 不成立（探针）。
*)
Definition strict_self {J : Category} (D : J ⟶ [P, X]) (M : Cone D) :
  StrictLift D (@Res P X) (FCone (@Res P X) M) := self_lift M.

End Strictness.
