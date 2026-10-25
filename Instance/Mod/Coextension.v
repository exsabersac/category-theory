(* * * Coextension of scalars: the right adjoint of R-Mod → Ab / * * 标量上的共延伸：R-Mod → Ab 的右伴随 *)

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
 ed., §IV.2 Exercise 2, printed p. 90 (ledger item
 `maclane:IV.2:ex2`, issue #360) — the forgetful functor
 from R-modules to abelian groups has BOTH adjoints.  This
 file is the RIGHT one; the left one is the sibling
 described under PRIOR ART below.
 Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
 hom-set form, which is the presentation used here: the
 [Adjunction] record of Theory/Adjunction.v is a natural
 bijection of hom-setoids, and the unit and counit are its
 derived ⌊id⌋ and ⌈id⌉.
 Book:      Riehl, "Category Theory in Context", Dover 2016, §4.1
 Example 4.1.10 — restriction of scalars has a left adjoint
 (extension) and a right adjoint (coextension, also called
 coinduction).  READ THE RELATION PRECISELY: hers runs
 between two MODULE categories along a ring homomorphism,
 and this one runs into [Ab].  See PRIOR ART; the two are
 not instances of one another in this tree.
 nLab:      https://ncatlab.org/nlab/show/coextension+of+scalars
 nLab:      https://ncatlab.org/nlab/show/restriction+of+scalars
 Wikipedia: https://en.wikipedia.org/wiki/Change_of_rings

 WHAT IS DELIVERED.

 - [coex_group R A], the abelian group of additive maps R → A.  It
 is NOT built: it is Adjunction/Additive.v's [hom_ab] read at
 [Ab_AbEnriched], so carrier, zero, addition and negation are the
 enrichment's own — pinned by [coex_group_carrier],
 [coex_group_plus] and [coex_group_zero] at [eq_refl].
 - [CoextObj R A : RModObject R], that group made a LEFT R-module by
 TRANSLATION: (r · f)(s) = f (s r).
 - [CoextMap] and **[Coextension R : Ab ⟶ RMod R]**, the functor,
 whose arrow action is postcomposition.
 - [coex_to] / [coex_from], the two transposes, and [coex_adj], the
 bijection as an [Isomorphism] of hom-setoids in [Sets].
 - **[coex_adjunction R : RMod_Forget_Ab R ⊣ Coextension R]**, an
 inhabitant of Theory/Adjunction.v's [Adjunction] record, built
 through [Build_Adjunction'].
 - [coex_unit] and [coex_counit], with the reviewer check PINNED:
 **[coex_counit_is_eval_at_one] states that the counit at A,
 applied to φ, IS [cmon_map φ (rig_one R)] — EVALUATION AT 1 — and
 it closes at [eq_refl]**, not up to ≈.  The unit is dual and
 equally strict: [coex_unit_is_smul] gives m ↦ (s ↦ s · m).
 - A ℤ witness: [CoextInt], the additive endomorphisms of ℤ made a
 ℤ-module, with three non-degeneracy results proved by MAPPING OUT
 through the counit.

 NO COMMUTATIVITY HYPOTHESIS, AND THAT IS A THEOREM RATHER THAN A
 PREFERENCE.  The file's ONLY [Context] is [(R : RingObject)]; there
 is no commutativity argument anywhere, and [About CoextObj],
 [About Coextension] and [About coex_adjunction] all display a bare
 [forall R : RingObject].  The two places a reader expects
 commutativity to be spent are exactly the two associativity clauses,
 and both go through on associativity alone:

 - [coex_act_assoc], the module law (r r') · f ≈ r · (r' · f).  At s
 the two sides are f (s (r r')) and f ((s r) r'), and the ONLY law
 consumed is [rig_mul_assoc].
 - [coex_to]'s [rm_map_smul] obligation, which is what makes the
 forward transpose R-linear.  At s the two sides are
 g (s · (r · m)) and g ((s r) · m), and the ONLY law consumed is
 [rm_smul_assoc] of the source module.

 This is a genuine contrast with Instance/Mod/Closed.v, whose own
 header localises its commutativity hypothesis to [hm_smul_linear]:
 there r · φ must be shown LINEAR, and (r·φ)(s·v) is r · (s · φ v)
 where linearity demands s · (r · φ v), so the two scalars must be
 exchanged.  Here they never are.

 THE HANDEDNESS IS FORCED, AND THE SWAP IS PINNED AS A NEGATIVE.  The
 action translates on the RIGHT of the ring argument, (r · f)(s) =
 f (s r), and that is what makes the result a LEFT module: at s,
 ((r r') · f) is f (s (r r')) = f ((s r) r'), while (r · (r' · f)) is
 (r' · f)(s r) = f ((s r) r') — the same term after one
 re-bracketing.  The other spelling, f (r s), would give
 ((r r') · f)(s) = f ((r r') s) against (r · (r' · f))(s) = f ((r' r) s),
 which is an ANTI-action and hence a right module; over a commutative
 ring the two coincide and the distinction is invisible, which is
 exactly why it is pinned (CONVERSION negative 3).  No swap was
 needed: the handedness compiles as first written.  Classically this
 is the left action induced by the RIGHT action of R on itself, i.e.
 R read as an (R,R)-bimodule; that reading is NOT invoked below —
 Instance/Mod.v's [Ring_Bimodule] exists and is never consulted, and
 its [bm_compat] field is exactly the [rig_mul_assoc] spent directly.

 WHY A RING AND NOT A RIG.  [hom_ab] demands an [AbEnriched] category,
 and the negation it supplies on the hom-group is A's; the source
 [ring_ab R] must likewise be an object of [Ab].  So [ring_neg] is
 spent NOWHERE in this file directly; its whole role is that
 [ring_ab R] is an abelian group at all.  A rig-level analogue would
 need the [Preadditive] reading of a hom-setoid — the commutative
 monoid of homomorphisms.  What is absent is narrower than it first
 looks, and the wide claim would be false: Instance/FdVect/
 DoubleDual.v's [dual_cmon] and [dual_ab] ARE that
 reading, their plus and zero being [RMod_Preadditive]'s own [padd]
 and [pzero].  What the tree lacks is a GENERAL operator
 [Preadditive C → x → y → CMonObject] — [dual_cmon] is instance-level
 with its codomain fixed at [Ring_RMod] — and the NAME [hom_cmon],
 which occurs nowhere.

 WHAT IS REUSED, NOT REBUILT.

 - Adjunction/Additive.v: **[hom_ab]**, the hom-setoid of an
 Ab-enriched category read as an [AbObject].  This is the whole
 carrier; the file adds only the action.
 - Structure/AbCategory.v: [Ab_AbEnriched], and through it
 [ab_hom_add] / [ab_hom_zero] / [ab_hom_neg].
 - Instance/Rng.v: [ring_ab], the additive group of a ring.
 - Instance/Mod.v: [RModObject], [RModHom], [RMod],
 **[RMod_Forget_Ab]** (the LEFT adjoint of the delivered
 adjunction, taken as given), [rm_smul_zero_l], [rm_smul_zero_r],
 [Ring_RMod], [Int_RMod].
 - Instance/Ab.v: [AbHom], and Instance/CMon.v's [cmon_hom_compose],
 which is what makes the arrow action postcomposition on the nose.
 - Theory/Adjunction.v: [Build_Adjunction'], [unit], [counit].

 NO INDUCTION AND NO FIXPOINT.  Neither tactic nor keyword is invoked
 below.  A case-INSENSITIVE sweep for the first returns exactly two
 lines: this heading, and one word of the Riehl citation above.  A
 case-SENSITIVE sweep for the second, spelled as Coq spells it,
 returns none.  Nothing here is a quotient, so there is no elimination
 to perform: every obligation is an equation between two values of a
 hom-setoid, checked at an argument.  Correspondingly the file has no
 analogue of a universal-property "agreement on generators" step —
 the hard direction of the bijection is carried by the module laws of
 the source module instead.

 WHICH LEMMA SPENDS WHICH LAW.  Read as a ledger; nothing else of R is
 consumed, and in particular [rig_mul_zero_r], [rig_add_assoc],
 [rig_add_comm] and [ring_neg] are spent nowhere directly.

 [coex_act]          respectfulness ← [rig_mul_respects]
 zero ← [rig_mul_zero_l], [cmon_map_zero] of f
 additivity ← [rig_distr_r], [cmon_map_plus] of f
 [coex_act_respects] ← [rig_mul_respects]
 [coex_act_distr_l]  ← NOTHING; it closes by [reflexivity]
 [coex_act_distr_r]  ← [rig_distr_l], [cmon_map_plus] of f
 [coex_act_assoc]    ← [rig_mul_assoc]        (associativity ONLY)
 [coex_act_one]      ← [rig_mul_one_r]
 [coex_map_ab]       ← nothing of R; [cmon_map_zero] and
 [cmon_map_plus] of the given f
 [CoextMap]'s [rm_map_smul], and [Coextension]'s [fmap_id] and
 [fmap_comp] ← NOTHING; all three close by [reflexivity]
 [coex_to_inner]     ← [rm_smul_respects], [rm_smul_zero_l],
 [rm_smul_distr_r] of M
 [coex_to_ab]        ← [rm_smul_respects], [rm_smul_zero_r],
 [rm_smul_distr_l] of M
 [coex_to]           ← [rm_smul_assoc] of M   (associativity ONLY)
 [coex_from]         ← NOTHING of R and NOTHING of M's action: only
 the three [CMonHom] laws of the given h, each
 read at [rig_one].  In particular the
 R-linearity of h is NOT consumed by the
 untranspose.
 [coex_adj] to∘from  ← [rm_map_smul] of h, then [rig_mul_one_l]
 [coex_adj] from∘to  ← [rm_smul_one] of M
 [Build_Adjunction']'s first naturality ← [rm_map_smul] of g;
 its second ← NOTHING, by [reflexivity]

 BOTH DISTRIBUTIVITY LAWS AND BOTH UNIT LAWS OF R ARE SPENT, AT
 DIFFERENT PLACES, AND OVER A NON-COMMUTATIVE RING THOSE ARE FOUR
 SEPARATE AXIOMS.  [rig_distr_r] is what makes r · f a homomorphism at
 all (additivity in the ring argument), while [rig_distr_l] is what
 makes the action additive in the SCALAR; [rig_mul_one_r] closes the
 module law 1 · f ≈ f, while [rig_mul_one_l] closes the round trip
 [coex_to (coex_from h)] ≈ h.  Neither pair could be collapsed without
 commutativity, so this is a real observation and not bookkeeping.

 STRENGTHS, MEASURED STRICT-FIRST.  Twenty identifications close at
 [eq_refl] and are shipped as [Example]s — twenty occurrences in CODE
 with comments and [Fail]s excluded, a figure a naive grep overstates
 by one because it also matches this paragraph:

 - the three data fields of the carrier ([coex_group_carrier],
 [coex_group_plus], [coex_group_zero]) — so the group is [hom_ab]
 on the nose and nothing was rebuilt;
 - the action at a point ([coex_act_at]) and the arrow action at a
 point ([coex_map_at]);
 - both transposes at a point ([coex_to_at], [coex_from_at]);
 - **the counit IS evaluation at 1 ([coex_counit_is_eval_at_one])**
 — the reviewer check, definitional rather than up to ≈ — and the
 unit IS m ↦ (s ↦ s · m) ([coex_unit_is_smul]);
 - the adjunction's forward transpose IS [coex_to] and its backward
 transpose IS [coex_from] ([coex_adj_to_is_coex_to],
 [coex_adj_from_is_coex_from]), so nothing downstream reads a
 different map than the one this header names;
 - the functor's two actions ([coex_fobj_is_CoextObj],
 [coex_fmap_is_CoextMap]) and the left adjoint's object action
 ([coex_forget_is_rm_ab]);
 - over ℤ, multiplication by n at a point, the counit computing to 3
 and to 0, and the action computing 2 · (·3) to 6;
 - and two probe controls, the handedness and the pointwise reading
 of left distributivity.

 EXACTLY THREE IDENTIFICATIONS FALL BACK TO ≈, AND THEIR CAUSES
 DIFFER.  Two are the round trips of the bijection: [coex_from
 (coex_to g)] evaluates to g (1 · m) and [coex_to (coex_from h)]
 evaluates the inner homomorphism at 1 · s; [rm_smul_one] and
 [rig_mul_one_l] are what remove the residues, and both are abstract
 fields of a class, so neither side reduces and no downstream
 transparency would help.  The third is different in kind and is
 measured as such: left distributivity holds POINTWISE at [eq_refl]
 (control beside negative 4), yet the two RECORDS are not convertible,
 because [coex_act] is a [Program Definition] whose [cmon_map_zero]
 and [cmon_map_plus] obligations are opaque and are built at different
 arguments on the two sides.  So there the DATA agrees on the nose and
 only the law fields separate.

 UNIVERSES, MEASURED AND ATTRIBUTED.  Scope this to the five
 constants named, because as a claim about the FILE all three clauses
 are false: the four [coex_ctrl_*] probe controls each carry ten
 equations [u = u0] .. [u = u9]; sixteen constants carry a strict
 constraint other than [u < u2]; and each of the five named carries
 [u <= u1] and [u0 <= u1], bounds between this file's OWN declared
 levels rather than against any donor.  Of [coex_act], [coex_group],
 [CoextObj], [Coextension] and [coex_adjunction], then: their only
 universe EQUATIONS are [u = u0] and [u = u1] — the ring's three
 universes collapse to one — carried identically by all five; the
 only STRICT constraint among them is [u < u2], which [coex_act]
 does not carry at all; and the rest of their blocks is a bound
 against [Basics.compose], [prod_rect], [ID], [projections] and
 [Logic_lemmas.equality].  Where the identification enters is measured
 rather than guessed, and it is NOT this file's.  With the ring's
 first and third universes declared strictly apart, [RMod Ru],
 [ring_ab Ru], [RMod_Forget_Ab Ru], [hom_ab Ab_AbEnriched Au Bu],
 [Ab ⟶ RMod Ru] and [Ring_RMod Ru] all elaborate, while
 [AbHom (ring_ab Ru) Au] is REJECTED — so the wall is met already at
 the point where a ring's additive group is read as the source of a
 homomorphism of abelian groups, before any construction of this file
 is reached, and before [Ab]-the-category is mentioned.  A SECOND and
 INDEPENDENT donor is pinned beside it: Instance/Mod.v's own
 [Ring_RMod Ru : obj[RMod Ru]] is rejected at the very same levels
 with the very same message, and it mentions neither [Ab] nor
 anything here, so the identification would still be met if the
 abelian side were repaired.  Neither is claimed unavoidable; no
 re-annotation was attempted.

 PRIOR ART, AND WHAT IT DOES AND DOES NOT SHARE WITH THIS FILE.

 - Instance/Mod/BaseChange.v, written in this same branch for the
 OTHER half of issue #360, delivers
 [ZExt R ⊣ RMod_Forget_Ab R]: extension of scalars along ℤ → R as
 A ↦ R ⊗ A, over Instance/Ab/Tensor.v's ℤ-tensor.  Together with
 the adjunction below that is the adjoint TRIPLE
 [ZExt R ⊣ RMod_Forget_Ab R ⊣ Coextension R] on ONE functor, which
 is exactly what `maclane:IV.2:ex2` asks for.  **The two files
 share no construction**: that one's carrier is [AbTensor] and
 this one's is [hom_ab], their declared name sets are disjoint,
 and neither defines an [Ltac].  Read that as "no OWN artifact in
 common" — the ordinary tactics are of course shared, and so are
 at least ten DONORS, not the two an earlier draft of this
 paragraph listed: [ring_ab], [RMod_Forget_Ab], [Build_Adjunction],
 [cmon_hom_compose], [Int_RMod], [Ring_RMod], [ab_hom_add],
 [rm_smul_zero_r], [AbHom], [RModObject], plus [unit]/[counit].
 This file does NOT [Require] it, so the two compile
 independently and the triple is NOT stated here as a single
 artifact — that statement would need both in one scope and is
 listed as not delivered.  (The description above is from reading
 that file, not from a check performed in this one.)
 - Instance/Mod/Extension.v (pre-existing, _CoqProject, issue
 #312) is a DIFFERENT pair over a different pair of categories:
 [ExtendScalars phi Hc ⊣ Restrict phi] between [RMod R] and
 [RMod S] along an arbitrary ring homomorphism, over
 Instance/Mod/Tensor.v's R-tensor and under a [CentralImage]
 hypothesis.  Its own right-hand neighbour — the coextension
 Hom_R(S, −) along phi, right adjoint to [Restrict phi] — is built
 neither there nor here.  This file is not an instance of it: at
 phi : ℤ → R that file's restriction runs [RMod R ⟶ RMod Int_Ring]
 while this one's left adjoint runs [RMod R ⟶ Ab].  State the
 obstruction precisely: "the tree carries no functor relating
 [Ab] and [RMod Int_Ring]" would be FALSE — [RMod_Forget_Ab
 Int_Ring] is one, and this file uses it at that very ring in its
 own ℤ witness.  An earlier revision went on: "What is absent is
 an [Ab ⟶ RMod Int_Ring] carrying each abelian group ITS OWN
 ℤ-action, which is what Instance/Ab/Free.v, Instance/Mod/Quotient.v
 and Instance/Mod/Tensor.v each record."  Since #454 that functor
 exists, Instance/Mod/Cogenerator.v's [Ab_to_ZMod] (each group with
 its own [zsmul] action), and those three files carry the same
 correction; what is still absent is an equivalence
 [Ab ≃ RMod Int_Ring].  Nothing is shared and that
 file is not [Require]d either.

 AXIOMS.  73/73 constants report "Closed under the global context"
 (49 source-declared plus 24 [Program] obligations that no source
 sweep sees, queried by fully qualified name).  Zero of the 73 names
 occur anywhere else in the tree, checked name by name.

 NEGATIVES.  Fifteen [Fail] commands: fourteen guarded negatives —
 five CONVERSION, two TYPING, seven FORMABILITY — each beside an
 APPLIED positive control, plus one scope-free instrument check.  Each
 was stripped of its [Fail] and compiled alone and its WHOLE error
 read; the classification is recorded at the probe section.  Every
 constant named inside a negative is also named outside one, so a
 rename cannot turn a guard vacuously green.

 WHAT IS NOT DELIVERED.

 - No coextension along an arbitrary ring homomorphism, so nothing
 here is a right adjoint to Instance/Rng/Mod.v's [Restrict phi];
 the base is [Ab] throughout.
 - No statement of the adjoint triple as one artifact, since
 Instance/Mod/BaseChange.v is deliberately not [Require]d, and no
 comparison of [Coextension] with anything in
 Instance/Mod/Extension.v.
 - No monad or comonad from the adjunction, and no Eilenberg–Moore
 or Kleisli reading.
 - No triangle identities restated in this file's own vocabulary
 (they are Theory/Adjunction.v's derived corollaries and are not
 specialised), and no uniqueness statement for the right adjoint.
 - No enriched reading: both hom-sets in play are abelian groups and
 Adjunction/Additive.v's [adj_hom_ab_iso] is one Require away, and
 the bijection is NOT exhibited as an isomorphism in [Ab], nor is
 any additivity of either adjoint claimed.  An earlier revision
 gave as the reason that [adj_hom_ab_iso] "needs [AbEnriched (RMod
 R)], which the tree does not have (Instance/Mod.v supplies only
 [RMod_Preadditive])"; Instance/Mod/Bimodule.v's [RMod_AbEnriched]
 supplies it, so the hypothesis is available and [adj_hom_ab_iso]
 is simply not applied here.
 - No isomorphism Hom_ℤ(ℤ, A) ≅ A, hence nothing says
 [Coextension Int_Ring] is equivalent to the identity; the ℤ
 witness pins Hom(ℤ, ℤ) only through maps OUT of it, and
 [CoextInt] is refuted equal to [Int_RMod] on the nose.  (Since
 #454 Instance/Mod/Watts.v's [ab_hom_Z_iso] gives Ab(ℤ, X) ≅ X,
 natural in X, with ℤ the free abelian group on one point
 [FreeAb SetsOne]; that is not [Int_Ring]'s group, whose
 comparison with the free one Instance/Ab/Generator.v records as
 not built, so this bullet stands.)
 - No [RigObject] variant, no right-module or bimodule reading, and
 no [Instance] registered for typeclass resolution: [CoextObj],
 [Coextension] and [coex_adjunction] are plain [Definition]s.
 - No finiteness, no basis, no rank and no decision procedure for
 equality in the coextension; every negative goes through a map
 OUT. 

 --------
 书籍：Mac Lane，《为工作的数学家准备的范畴论》，第二版，第 IV.2 节习题 2，印刷页 90（账目项目 `maclane:IV.2:ex2`，第 360 期）——从 R-模到阿贝尔群的遗忘函子有两个伴随函子。这个文件是右伴随；左伴随在下文“先前技术”中描述的同类项中。书籍：Mac Lane，同上，第 IV.1 节，印刷页 79–80——以 Hom 集形式的伴随，这是这里使用的表示：Theory/Adjunction.v 的 [Adjunction] 记录是 Hom-集合体的自然双射，单位和余单位是其派生的 ⌊id⌋ 和 ⌈id⌉。书籍：Riehl，《上下文中的范畴论》，Dover 2016，第4.1节
 示例 4.1.10 — 标量约束有一个左伴随（扩展）和一个右伴随（余扩展，也称为余归纳）。精确阅读关系：她的关系是沿环同态在两个模范畴之间的，而这个关系是进入 [Ab]。参见先前工作；这两个在这个树中不是彼此的实例。nLab：https://ncatlab.org/nlab/show/coextension+of+scalars
 nLab：https://ncatlab.org/nlab/show/restriction+of+scalars
 维基百科：https://en.wikipedia.org/wiki/Change_of_rings

 交付的内容是什么。- [coex_group R A]，R → A 的加法映射的阿贝尔群。它**未被构建**：它是从 Adjunction/Additive.v 的 [hom_ab] 在 [Ab_AbEnriched] 中读取的，所以 carrier、零、加法和取负是该富结构自身的——由 [coex_group_carrier]、[coex_group_plus] 和 [coex_group_zero] 在 [eq_refl] 中固定。- [CoextObj R A : RModObject R]，通过 TRANSLATION 将该群构造成一个左 R-模：(r · f)(s) = f(s r)。- [CoextMap] 和 **[Coextension R : Ab ⟶ RMod R]**，函子，其箭头作用是后复合。- [coex_to] / [coex_from]，两个转置，以及 [coex_adj]，作为 [Isomorphism] 的同构，在 [Sets] 中的 hom-集合同态中。- **[coex_adjunction R : RMod_Forget_Ab R ⊣ Coextension R]**，Theory/Adjunction.v 的 [Adjunction] 记录的一个元素，通过 [Build_Adjunction'] 构建。- [coex_unit] 和 [coex_counit]，审查员检查后固定：
 ** [coex_counit_is_eval_at_one] 表明，在 A 上的余单位，
 作用于 φ 时，是 [cmon_map φ (rig_one R)] —— 在 1 处的求值 —— 并且
 它在 [eq_refl] 处闭合 **，而不是大约。该单位是对偶且
 同样严格：[coex_unit_is_smul] 给出 m ↦ (s ↦ s · m)。- 一个 ℤ 见证：[CoextInt]，即 ℤ 的加性自同态形成 ℤ-模，通过余单位的映射证明了三个非退化性结果。没有交换性假设，这是一个定理而不是偏好。该文件唯一的 [Context] 是 [(R : RingObject)]；没有任何地方使用交换性论证，而 [About CoextObj]、[About Coextension] 和 [About coex_adjunction] 都显示了一个单独的 [forall R : RingObject]。读者期望使用交换性的两个地方恰好是两个结合性条款，并且两者仅凭结合性就成立：

 - [coex_act_assoc]，模律 (r r') · f ≈ r · (r' · f)。在 s 处，两边分别为 f (s (r r')) 和 f ((s r) r')，唯一使用的律是 [rig_mul_assoc]。
 - [coex_to] 的 [rm_map_smul] 义务，这使得前向转置是 R-线性的。在 s 处，两边分别为 g (s · (r · m)) 和 g ((s r) · m)，唯一使用的律是源模的 [rm_smul_assoc]。这与 Instance/Mod/Closed.v 形成了真正的对比，其自身的头文件将它的交换性假设本地化到 [hm_smul_linear]：必须证明 r · φ 是线性的，并且 (r·φ)(s·v) 等于 r · (s · φ v)，而线性要求 s · (r · φ v)，因此这两个标量必须交换。在这里它们从未被交换。手性是被强制的，并且交换被固定为负。这个操作在环的参数右侧进行，(r · f)(s) = f (s r)，这就是使结果成为左模的原因：在 s 点上，((r r') · f) 是 f (s (r r')) = f ((s r) r')，而 (r · (r' · f)) 是 (r' · f)(s r) = f ((s r) r') — 在一次重新加括号后是相同的项。另一种写法 f (r s) 会导致 ((r r') · f)(s) = f ((r r') s) 与 (r · (r' · f))(s) = f ((r' r) s) 相对立，这是一个反作用，因此是一个右模；在交换环上，两者一致，区别不可见，这正是为什么它被固定（CONVERSION 负 3）。不需要交换：手性编译时按最初写法进行。按照经典理解，这是由 R 在自身上的右作用诱导的左作用，即R 被作为一个 (R,R)-双模读取；下面没有调用这种读取——
 Instance/Mod.v 的 [Ring_Bimodule] 存在但从未被使用，并且它的 [bm_compat] 字段正好是直接消耗的 [rig_mul_assoc]。为什么是环而不是半环。[hom_ab] 需要一个 [AbEnriched] 类别，并且其在同态群上提供的否定是 A 的；源 [ring_ab R] 同样必须是 [Ab] 的一个对象。因此 [ring_neg] 在这个文件中直接未被使用；它的全部作用只是 [ring_ab R] 能成为阿贝尔群而已。半环级的类比则需要同态集合的 [Preadditive] 阅读——同态的交换幺半群。缺失的内容比最初看起来更狭窄，而广泛的说法是错误的：Instance/FdVect/DoubleDual.v 的 [dual_cmon] 和 [dual_ab] 就是这种阅读方式，它们的加法和零分别是 [RMod_Preadditive] 自身的 [padd] 和 [pzero]。这棵树缺少一个通用操作符
 [Preadditive C → x → y → CMonObject] — [dual_cmon] 是实例级别的
 其余范围固定在 [Ring_RMod] — 并且名称为 [hom_cmon]，
 它从未出现过。

 重用的内容，而不是重建。- Adjunction/Additive.v: **[hom_ab]**，Ab-增强范畴的同类集合读作 [AbObject]。这是整个承载体；文件只增加了作用。 
 - Structure/AbCategory.v: [Ab_AbEnriched]，通过它 [ab_hom_add] / [ab_hom_zero] / [ab_hom_neg]。 
 - Instance/Rng.v: [ring_ab]，环的加法群。 
 - Instance/Mod.v: [RModObject]，[RModHom]，[RMod]，**[RMod_Forget_Ab]**（所给附随对的左伴随，按给定取），[rm_smul_zero_l]，[rm_smul_zero_r]，[Ring_RMod]，[Int_RMod]。 
 - Instance/Ab.v: [AbHom]，以及 Instance/CMon.v 的 [cmon_hom_compose]，这正是让箭头作用在后复合上成立的原因。 
 - Theory/Adjunction.v: [Build_Adjunction']，[unit]，[counit]。没有归纳法，也没有不动点。在下面没有调用任何战术或关键字。对第一个的大小写不敏感搜索恰好返回两行：这一标题，以及上面 Riehl 引用中的一个单词。按 Coq 拼写的第二个进行大小写敏感搜索，则没有返回结果。这里没有任何是商，因此无需执行消去：每个义务都是在一个同类集合的两个值之间的等式，在一个参数上进行检查。因此该文件没有类似于通用性质“生成元一致性”的步骤——双射的难方向由源模块的模块法则承担。

 哪个引理用到了哪个法则。作为账本来阅读；没有其他 R 被消耗，尤其是 [rig_mul_zero_r]、[rig_add_assoc]、[rig_add_comm] 和 [ring_neg] 在任何地方都没有直接被使用。

 [coex_act]           尊重性 ←  [rig_mul_respects] 
 零 ←  [rig_mul_zero_l] ,  [cmon_map_zero]  的 f
 可加性 ←  [rig_distr_r] ,  [cmon_map_plus]  的 f
 [coex_act_respects]  ←  [rig_mul_respects] 
 [coex_act_distr_l]   ← 无; 它通过 [reflexivity] 关闭
 [coex_act_distr_r]   ←  [rig_distr_l] ,  [cmon_map_plus]  的 f
 [coex_act_assoc]     ←  [rig_mul_assoc]         （仅结合性）
 [coex_act_one]       ←  [rig_mul_one_r] 
 [coex_map_ab]        ← R 的无;  [cmon_map_zero]  和
 [cmon_map_plus]  给定 f 的
 [CoextMap] 的  [rm_map_smul] , 和  [Coextension] 的  [fmap_id] 和
 [fmap_comp]  ← 无; 三者都通过 [reflexivity] 关闭
 [coex_to_inner]      ←  [rm_smul_respects] ,  [rm_smul_zero_l] ,
 [rm_smul_distr_r]  的 M
 [coex_to_ab]         ←  [rm_smul_respects] ,  [rm_smul_zero_r] ,
 [rm_smul_distr_l]  的 M
 [coex_to]←  [rm_smul_assoc] 的 M （仅结合律）
 [coex_from]          ← R 的 NOTHING 和 M 的作用的 NOTHING：仅有
 给定 h 的三个 [CMonHom] 定律，每个
 在 [rig_one] 阅读。特别是，h 的 R 线性并未被 untranspose 消耗。[coex_adj]  到∘从 ← [rm_map_smul] 的 h，然后 [rig_mul_one_l] [coex_adj] 从∘到 ← [rm_smul_one] 的 M [Build_Adjunction'] 的第一个自然性 ← [rm_map_smul] 的 g；其第二个 ← 没有，由 [reflexivity]R 的两个分配律和两个单位律在不同地方被使用，在非交换环上它们是四条独立的公理。[rig_distr_r] 是使 r · f 成为同态的原因（在环变量上满足可加性），而 [rig_distr_l] 则使作用在标量上可加；[rig_mul_one_r] 完成了模法则 1 · f ≈ f，而 [rig_mul_one_l] 完成了循环 [coex_to (coex_from h)] ≈ h。没有交换性，这两对都无法合并，因此这是一个真实的观察，而不是记账。

 优势，严格优先测量。在 [eq_refl] 上有二十个标识被关闭，并作为 [Example] 发送——在代码中有二十次出现带注释，并且排除了 [Fail]，一次天真的 grep 会多统计一次，因为它也匹配了这段文字:- 载体的三个数据字段（[coex_group_carrier], [coex_group_plus], [coex_group_zero]）——所以该组合正好是[hom_ab]，而且没有进行重建；
 - 在一点的作用（[coex_act_at]）以及箭头在一点的作用（[coex_map_at]）；
 - 一点的两个转置（[coex_to_at], [coex_from_at]）；
 - **余单位在1处的评估（[coex_counit_is_eval_at_one]）**——审阅者检查，定义性而非约等于——以及单位为m ↦ (s ↦ s · m)（[coex_unit_is_smul]）；
 - 函合的正向转置为[coex_to]，其反向转置为[coex_from]（[coex_adj_to_is_coex_to], [coex_adj_from_is_coex_from]），因此下游没有任何部分读取与此标题所命名的映射不同的映射；
 - 函子的两个作用（[coex_fobj_is_CoextObj], [coex_fmap_is_CoextMap]）以及左伴随的对象作用（[coex_forget_is_rm_ab]）；- 在 ℤ 上，某一点上的 n 乘法，余单位计算为 3 和 0，以及作用计算 2 · (·3) 为 6；
 - 以及两个探针控制，分别是手性和左分配律的逐点读取。恰好有三种识别回退到≈，并且其原因不同。两种是双射的往返旅行：[coex_from (coex_to g)] 计算为 g (1 · m)，而 [coex_to (coex_from h)] 在 1 · s 处计算内部同态；[rm_smul_one] 和 [rig_mul_one_l] 是用来去除剩余项的，它们都是一个类的抽象字段，因此两边都不会被简化，后续的透明化也无济于事。第三种在性质上不同，并且按此进行测量：在 [eq_refl]（控制在负4旁边）处左分配性逐点成立，然而两个 RECORDS 不可转换，因为 [coex_act] 是一个 [Program Definition]，其 [cmon_map_zero] 和 [cmon_map_plus] 义务是不可见的，并且在两边的参数上构建不同。因此，DATA 在表面上是完全一致的，只有法规字段不同。宇宙，被测量和归属。将其范围限定为五个已命名的常数，因为作为对文件的声明，三条条款都是错误的：四个 [coex_ctrl_*] 探针控制器每个都包含十个方程 [u = u0] .. [u = u9]；十六个常数除 [u < u2] 外都有严格约束；五个已命名的常数每个都带有 [u <= u1] 和 [u0 <= u1]，这些界限在该文件自身声明的级别之间，而不是针对任何捐赠者。在 [coex_act]、[coex_group]、[CoextObj]、[Coextension] 和 [coex_adjunction] 中：它们唯一的宇宙方程是 [u = u0] 和 [u = u1]——环的三个宇宙坍缩为一个——所有五个都完全相同地携带；它们之间唯一的严格约束是 [u < u2]，而 [coex_act] 完全不携带；它们其余的区块是对 [Basics.compose]、[prod_rect]、[ID]、[projections] 和 [Logic_lemmas.equality] 的束缚。识别的进入是测量得出的，而不是猜测的，并且这不是该文件的。随着环的第一个和第三个宇宙被明确区分开来，[RMod Ru]、[ring_ab Ru]、[RMod_Forget_Ab Ru]、[hom_ab Ab_AbEnriched Au Bu]、[Ab ⟶ RMod Ru] 和 [Ring_RMod Ru] 均被详细说明，而 [AbHom (ring_ab Ru) Au] 被拒绝——因此墙壁已经在环的加法群被读取为阿贝尔群同态来源的点上遇到，在达到该文件的任何构造之前，并且在提到 [Ab] 类别之前。一个第二且独立的提供者被固定在旁边：Instance/Mod.v 自身的 [Ring_RMod Ru : obj[RMod Ru] 在完全相同的层级以完全相同的信息被拒绝，并且它既未提及 [Ab]，也未提及此处的任何内容，因此即使阿贝尔侧被修复，标识仍将被满足。两者都未被认为是不可避免的；未尝试重新标注。现有技术，以及它与本文件共享和不共享的内容。- Instance/Mod/BaseChange.v，在同一个分支中为问题 #360 的另一部分编写，提供了 [ZExt R ⊣ RMod_Forget_Ab R]：通过 ℤ → R 延拓标量，作为 A ↦ R ⊗ A，在 Instance/Ab/Tensor.v 的 ℤ-张量之上。结合下面的伴随，这构成了在单个函子上的伴随三重 [ZExt R ⊣ RMod_Forget_Ab R ⊣ Coextension R]，这正是 `maclane:IV.2:ex2` 所需要的。**这两个文件没有共享任何构造**：前者的承载类型是 [AbTensor]，后者的承载类型是 [hom_ab]，它们声明的名称集合是互不相交的，且都没有定义 [Ltac]。将其解读为“没有共同的 OWN 工件”——普通策略当然是共享的，至少有十个捐赠者，而不是这一段早期草稿中列出的两个：[ring_ab]、[RMod_Forget_Ab]、[Build_Adjunction]、[cmon_hom_compose]、[Int_RMod]、[Ring_RMod]、[ab_hom_add]、[rm_smul_zero_r]、[AbHom]、[RModObject]，加上 [unit] / [counit]。该文件不包含 [Require]，因此这两个独立编译，三重项在此未被声明为单一工件——该声明需要两者在同一个范围内，并被列为未交付。（上面的描述来自于读取该文件，而不是在此文件中执行的检查。）
 - Instance/Mod/Extension.v（预先存在的，_CoqProject，问题 #312）是在不同的类别对上的一对不同的对象：
 [ExtendScalars phi Hc ⊣ Restrict phi] 位于 [RMod R] 和 [RMod S] 之间，沿着任意环同态，在 Instance/Mod/Tensor.v 的 R-张量下并在 [CentralImage] 假设下。它自身右侧的邻居——沿 phi 的余拓展 Hom_R(S, −)，是 [Restrict phi] 的右伴随——既不在那里构建，也不在这里构建。此文件不是它的实例：在 phi : ℤ → R 时，该文件的限制运行 [RMod R ⟶ RMod Int_Ring]，而此文件的左伴随运行 [RMod R ⟶ Ab]。准确说明阻碍："树没有关联 [Ab] 和 [RMod Int_Ring] 的函子" 是错误的——[RMod_Forget_Ab Int_Ring] 就是一个，而该文件在其自身的 ℤ 证据中使用了它。早期的修订版本继续写道："缺少的是一个 [Ab ⟶ RMod Int_Ring]，为每个阿贝尔群提供它自身的 ℤ-作用，这正是 Instance/Ab/Free.v、Instance/Mod/Quotient.v 和 Instance/Mod/Tensor.v 各自记录的内容。" 自 #454 起，该函子已存在，Instance/Mod/Cogenerator.v 的 [Ab_to_ZMod]（每个群都有自己的 [zsmul] 作用）以及这三个文件也都进行了相同的修正；仍然缺少的是真值 [Ab ≃ RMod Int_Ring]。当中没有共享内容，并且该文件也不是 [Require] d。公理。73/73 个常量报告“在全局上下文下关闭”（49 个源声明的加上 24 个 [Program] 义务，源扫描无法看到，通过完全限定的名称查询）。在树的其他任何地方都没有出现这 73 个名称，一一核对名称。

 否定。十五个 [Fail] 命令：十四个受保护的否定——五个转换，两个类型检查，七个形式可构造性——每个旁边都有一个已应用的正控制，加上一个无作用域的工具检查。每一个都被去掉 [Fail] 并单独编译，读取其全部错误；分类记录在探测部分。每个在否定中命名的常量也在否定外被命名，因此重命名无法使保护自动变为绿色。

 未交付的内容。- 没有沿任意环同态的共延拓，因此这里没有任何内容是 Instance/Rng/Mod.v 的 [Restrict phi] 的右伴随；基础在整个过程中是 [Ab]。- 没有将伴随三重作为一个整体声明，因为 Instance/Mod/BaseChange.v 特意没有 [Require] d，也没有将 [Coextension] 与 Instance/Mod/Extension.v 中的任何内容进行比较。- 没有由伴随产生的单子或余单子，也没有 Eilenberg–Moore 或 Kleisli 的解释。- 没有在该文件自己的词汇中重述三角形恒等式（它们是 Theory/Adjunction.v 的推导推论，并且没有被专门化），也没有右伴随的唯一性声明。- 没有丰富化的阅读：两个正在使用的同态集都是阿贝尔群，而 Adjunction/Additive.v 的 [adj_hom_ab_iso] 只差一步要求，并且在 [Ab] 中没有将双射展示为同构，也没有声明任一伴随函数的可加性。早期的修订版本给出的原因是 [adj_hom_ab_iso] “需要 [AbEnriched (RMod R)]，但树中没有（Instance/Mod.v 只提供了 [RMod_Preadditive]）”；Instance/Mod/Bimodule.v 的 [RMod_AbEnriched] 提供了它，因此假设是可用的，而 [adj_hom_ab_iso] 只是没有在此处应用。- 没有同构 Hom_ℤ(ℤ, A) ≅ A，因此没有任何内容表明 [Coextension Int_Ring] 等价于恒等式；ℤ 的证据只能通过从它引出的映射固定 Hom(ℤ, ℤ)，并且 [CoextInt] 被直接反驳等于 [Int_RMod]。(由于 #454 Instance/Mod/Watts.v 的 [ab_hom_Z_iso] 给出了 Ab(ℤ, X) ≅ X，对 X 是自然的，其中 ℤ 是基于一个点的自由阿贝尔群 [FreeAb SetsOne]；这不是 [Int_Ring] 的群，其与自由群的比较在 Instance/Ab/Generator.v 中记录为未建立，所以这个要点仍然成立。) - 没有 [RigObject] 变体，没有右模或双模解释，也没有 [Instance] 用于类型类解析：[CoextObj]、[Coextension] 和 [coex_adjunction] 是普通的 [Definition]。 - 在余扩张中没有有限性、没有基、没有秩，也没有等式判断程序；每个否定都通过一个映射 OUT。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Adjunction.Additive.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

Section Coextension.

Context (R : RingObject).

Local Notation RS := (carrier (rig_setoid (ring_rig R))).
Local Notation RG := (ring_ab R).

Definition coex_group (A : AbObject) : AbObject :=
  hom_ab Ab_AbEnriched RG A.

Example coex_group_carrier (A : AbObject) :
  carrier (cmon_setoid (coex_group A)) = (RG ~{Ab}~> A) := eq_refl.

Example coex_group_plus (A : AbObject) :
  cmon_plus (coex_group A) = @ab_hom_add RG A := eq_refl.

Example coex_group_zero (A : AbObject) :
  cmon_zero (coex_group A) = @ab_hom_zero RG A := eq_refl.

(* * ** The scalar action: translation in the ring argument / * ** 标量作用：环论中的平移 *)

Program Definition coex_act (A : AbObject) (r : RS) (f : AbHom RG A) :
  AbHom RG A := {|
  cmon_map := {| morphism := fun s =>
    cmon_map f (rig_mul (ring_rig R) s r) |}
|}.
Next Obligation.
  intros A r f s s' Hs.
  exact (proper_morphism (cmon_map f) _ _
           (rig_mul_respects (ring_rig R) s s' Hs r r (reflexivity r))).
Qed.
Next Obligation.
  intros A r f; simpl.
  transitivity (cmon_map f (rig_zero (ring_rig R))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_mul_zero_l (ring_rig R) r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A r f s s'; simpl.
  transitivity (cmon_map f (rig_add (ring_rig R)
                              (rig_mul (ring_rig R) s r)
                              (rig_mul (ring_rig R) s' r))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_distr_r (ring_rig R) s s' r)).
  - exact (cmon_map_plus f _ _).
Qed.

Example coex_act_at (A : AbObject) (r s : RS) (f : AbHom RG A) :
  cmon_map (coex_act A r f) s
    = cmon_map f (rig_mul (ring_rig R) s r) := eq_refl.

(** ** The four module laws / ** 四个模块法则 *)

Lemma coex_act_respects (A : AbObject) :
  Proper (equiv ==> equiv ==> equiv) (coex_act A).
Proof.
  intros r r' Hr f g Hfg s; simpl.
  transitivity (cmon_map f (rig_mul (ring_rig R) s r')).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_mul_respects (ring_rig R) s s (reflexivity s) r r' Hr)).
  - exact (Hfg _).
Qed.

Lemma coex_act_distr_l (A : AbObject) (r : RS) (f g : AbHom RG A) :
  coex_act A r (cmon_plus (coex_group A) f g)
    ≈ cmon_plus (coex_group A) (coex_act A r f) (coex_act A r g).
Proof. intro s; reflexivity. Qed.

Lemma coex_act_distr_r (A : AbObject) (r r' : RS) (f : AbHom RG A) :
  coex_act A (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (coex_group A) (coex_act A r f) (coex_act A r' f).
Proof.
  intro s; simpl.
  transitivity (cmon_map f (rig_add (ring_rig R)
                              (rig_mul (ring_rig R) s r)
                              (rig_mul (ring_rig R) s r'))).
  - exact (proper_morphism (cmon_map f) _ _
             (rig_distr_l (ring_rig R) s r r')).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma coex_act_assoc (A : AbObject) (r r' : RS) (f : AbHom RG A) :
  coex_act A (rig_mul (ring_rig R) r r') f
    ≈ coex_act A r (coex_act A r' f).
Proof.
  intro s; simpl.
  exact (proper_morphism (cmon_map f) _ _
           (symmetry (rig_mul_assoc (ring_rig R) s r r'))).
Qed.

Lemma coex_act_one (A : AbObject) (f : AbHom RG A) :
  coex_act A (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro s; simpl.
  exact (proper_morphism (cmon_map f) _ _
           (rig_mul_one_r (ring_rig R) s)).
Qed.

Definition CoextObj (A : AbObject) : RModObject R := {|
  rm_ab            := coex_group A;
  rm_smul          := coex_act A;
  rm_smul_respects := coex_act_respects A;
  rm_smul_distr_l  := coex_act_distr_l A;
  rm_smul_distr_r  := coex_act_distr_r A;
  rm_smul_assoc    := coex_act_assoc A;
  rm_smul_one      := coex_act_one A
|}.

(* * ** The arrow action: postcomposition, and the functor / * ** 箭头操作：后合成，以及函子 *)

Program Definition coex_map_ab {A B : AbObject} (f : AbHom A B) :
  AbHom (coex_group A) (coex_group B) := {|
  cmon_map := {| morphism := fun phi =>
    (cmon_hom_compose f phi : AbHom RG B) |}
|}.
Next Obligation.
  intros A B f phi phi' Hphi s; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hphi s)).
Qed.
Next Obligation.
  intros A B f s; simpl.
  exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A B f phi psi s; simpl.
  exact (cmon_map_plus f _ _).
Qed.

Example coex_map_at {A B : AbObject} (f : AbHom A B)
  (phi : AbHom RG A) (s : RS) :
  cmon_map (cmon_map (coex_map_ab f) phi) s
    = cmon_map f (cmon_map phi s) := eq_refl.

Program Definition CoextMap {A B : AbObject} (f : AbHom A B) :
  CoextObj A ~{RMod R}~> CoextObj B := {|
  rm_hom := coex_map_ab f
|}.
Next Obligation. intros A B f r phi s; reflexivity. Qed.

Program Definition Coextension : Ab ⟶ RMod R := {|
  fobj := CoextObj;
  fmap := @CoextMap
|}.
Next Obligation.
  intros A B f g Hfg phi s; simpl.
  exact (Hfg _).
Qed.
Next Obligation. intros A phi s; reflexivity. Qed.
Next Obligation. intros A B C f g phi s; reflexivity. Qed.

(** ** The two transposes / ** 两个转置 *)

Program Definition coex_to_inner {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) (m : carrier (cmon_setoid (rm_ab M))) :
  AbHom RG A := {|
  cmon_map := {| morphism := fun s => cmon_map g (rm_smul M s m) |}
|}.
Next Obligation.
  intros A M g m s s' Hs.
  exact (proper_morphism (cmon_map g) _ _
           (rm_smul_respects M s s' Hs m m (reflexivity m))).
Qed.
Next Obligation.
  intros A M g m; simpl.
  transitivity (cmon_map g (cmon_zero (rm_ab M))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_zero_l M m)).
  - exact (cmon_map_zero g).
Qed.
Next Obligation.
  intros A M g m s s'; simpl.
  transitivity (cmon_map g (cmon_plus (rm_ab M) (rm_smul M s m)
                                                (rm_smul M s' m))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_distr_r M s s' m)).
  - exact (cmon_map_plus g _ _).
Qed.

Program Definition coex_to_ab {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) : AbHom (rm_ab M) (coex_group A) := {|
  cmon_map := {| morphism := fun m => coex_to_inner g m |}
|}.
Next Obligation.
  intros A M g m m' Hm s; simpl.
  exact (proper_morphism (cmon_map g) _ _
           (rm_smul_respects M s s (reflexivity s) m m' Hm)).
Qed.
Next Obligation.
  intros A M g s; simpl.
  transitivity (cmon_map g (cmon_zero (rm_ab M))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_zero_r M s)).
  - exact (cmon_map_zero g).
Qed.
Next Obligation.
  intros A M g m n s; simpl.
  transitivity (cmon_map g (cmon_plus (rm_ab M) (rm_smul M s m)
                                                (rm_smul M s n))).
  - exact (proper_morphism (cmon_map g) _ _ (rm_smul_distr_l M s m n)).
  - exact (cmon_map_plus g _ _).
Qed.

Program Definition coex_to {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) : M ~{RMod R}~> CoextObj A := {|
  rm_hom := coex_to_ab g
|}.
Next Obligation.
  intros A M g r m s; simpl.
  symmetry.
  exact (proper_morphism (cmon_map g) _ _ (rm_smul_assoc M s r m)).
Qed.

Program Definition coex_from {A : AbObject} {M : RModObject R}
  (h : M ~{RMod R}~> CoextObj A) : AbHom (rm_ab M) A := {|
  cmon_map := {| morphism := fun m =>
    cmon_map (cmon_map (rm_hom h) m) (rig_one (ring_rig R)) |}
|}.
Next Obligation.
  intros A M h m m' Hm.
  exact (proper_morphism (cmon_map (rm_hom h)) m m' Hm
           (rig_one (ring_rig R))).
Qed.
Next Obligation.
  intros A M h; simpl.
  exact (cmon_map_zero (rm_hom h) (rig_one (ring_rig R))).
Qed.
Next Obligation.
  intros A M h m n; simpl.
  exact (cmon_map_plus (rm_hom h) m n (rig_one (ring_rig R))).
Qed.

Example coex_to_at {A : AbObject} {M : RModObject R}
  (g : AbHom (rm_ab M) A) (m : carrier (cmon_setoid (rm_ab M)))
  (s : RS) :
  cmon_map (cmon_map (rm_hom (coex_to g)) m) s
    = cmon_map g (rm_smul M s m) := eq_refl.

Example coex_from_at {A : AbObject} {M : RModObject R}
  (h : M ~{RMod R}~> CoextObj A)
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (coex_from h) m
    = cmon_map (cmon_map (rm_hom h) m) (rig_one (ring_rig R)) := eq_refl.

(* * ** The hom-set bijection and the adjunction / * ** 同构集合的双射与伴随 *)

Program Definition coex_adj_to (M : RModObject R) (A : AbObject) :
  {| carrier := rm_ab M ~{Ab}~> A;
     is_setoid := @homset Ab (rm_ab M) A |}
    ~{Sets}~>
  {| carrier := M ~{RMod R}~> CoextObj A;
     is_setoid := @homset (RMod R) M (CoextObj A) |} := {|
  morphism := fun g => coex_to g
|}.
Next Obligation. intros M A g g' Hg m s; exact (Hg _). Qed.

Program Definition coex_adj_from (M : RModObject R) (A : AbObject) :
  {| carrier := M ~{RMod R}~> CoextObj A;
     is_setoid := @homset (RMod R) M (CoextObj A) |}
    ~{Sets}~>
  {| carrier := rm_ab M ~{Ab}~> A;
     is_setoid := @homset Ab (rm_ab M) A |} := {|
  morphism := fun h => coex_from h
|}.
Next Obligation. intros M A h h' Hh m; exact (Hh m _). Qed.

Program Definition coex_adj (M : RModObject R) (A : AbObject) :
  @Isomorphism Sets
    {| carrier := rm_ab M ~{Ab}~> A;
       is_setoid := @homset Ab (rm_ab M) A |}
    {| carrier := M ~{RMod R}~> CoextObj A;
       is_setoid := @homset (RMod R) M (CoextObj A) |} := {|
  to   := coex_adj_to M A;
  from := coex_adj_from M A
|}.
Next Obligation.
  intros M A h m s; simpl.
  transitivity (cmon_map (coex_act A s (cmon_map (rm_hom h) m))
                  (rig_one (ring_rig R))).
  - exact (rm_map_smul h s m (rig_one (ring_rig R))).
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom h) m)) _ _
             (rig_mul_one_l (ring_rig R) s)).
Qed.
Next Obligation.
  intros M A g m; simpl.
  exact (proper_morphism (cmon_map g) _ _ (rm_smul_one M m)).
Qed.

Definition coex_adjunction : RMod_Forget_Ab R ⊣ Coextension.
Proof.
  unshelve eapply (@Build_Adjunction' Ab (RMod R) (RMod_Forget_Ab R)
                     Coextension coex_adj).
  - intros M N A f g m s; simpl.
    exact (proper_morphism (cmon_map f) _ _ (rm_map_smul g s m)).
  - intros M A B f g m s; reflexivity.
Defined.

(* * ** Unit, counit, and the strict readings / * ** 单位、余单位以及严格读法 *)

Definition coex_unit (M : RModObject R) :
  M ~{RMod R}~> CoextObj (rm_ab M) :=
  @unit Ab (RMod R) (RMod_Forget_Ab R) Coextension coex_adjunction M.

Definition coex_counit (A : AbObject) :
  rm_ab (CoextObj A) ~{Ab}~> A :=
  @counit Ab (RMod R) (RMod_Forget_Ab R) Coextension coex_adjunction A.

(* THE REVIEWER CHECK. The counit IS evaluation at 1, on the nose. / 审稿人检查。该单元的评估为1，完全正确。 *)
Example coex_counit_is_eval_at_one (A : AbObject) (phi : AbHom RG A) :
  cmon_map (coex_counit A) phi
    = cmon_map phi (rig_one (ring_rig R)) := eq_refl.

Example coex_unit_is_smul (M : RModObject R)
  (m : carrier (cmon_setoid (rm_ab M))) (s : RS) :
  cmon_map (cmon_map (rm_hom (coex_unit M)) m) s = rm_smul M s m
  := eq_refl.

Example coex_adj_to_is_coex_to (M : RModObject R) (A : AbObject)
  (g : rm_ab M ~{Ab}~> A) :
  to (@adj Ab (RMod R) (RMod_Forget_Ab R) Coextension
        coex_adjunction M A) g = coex_to g := eq_refl.

Example coex_adj_from_is_coex_from (M : RModObject R) (A : AbObject)
  (h : M ~{RMod R}~> CoextObj A) :
  from (@adj Ab (RMod R) (RMod_Forget_Ab R) Coextension
          coex_adjunction M A) h = coex_from h := eq_refl.

Example coex_fobj_is_CoextObj (A : AbObject) :
  fobj[Coextension] A = CoextObj A := eq_refl.

Example coex_fmap_is_CoextMap (A B : AbObject) (f : A ~{Ab}~> B) :
  fmap[Coextension] f = CoextMap f := eq_refl.

Example coex_forget_is_rm_ab (M : RModObject R) :
  fobj[RMod_Forget_Ab R] M = rm_ab M := eq_refl.

End Coextension.

(** ** A concrete witness over ℤ / ** 一个关于 ℤ 的具体例子 *)

(*
   * The coextension of ℤ along ℤ: the abelian group of additive
   endomorphisms of ℤ, made a ℤ-module by translation. 

   --------
   * 沿着 ℤ 的 ℤ 的共延伸：ℤ 的加性自同态的阿贝尔群，通过平移构成一个 ℤ-模。
*)
Definition CoextInt : RModObject Int_Ring :=
  CoextObj Int_Ring (ring_ab Int_Ring).

(*
   * Multiplication by [n], obtained as the unit at [Int_RMod] rather
   than hand-built: [coex_unit] sends m to (s ↦ s · m). 

   --------
   * 通过 [n] 进行的乘法，它是作为 [Int_RMod] 处的单位获得的，而不是手工构建的：[coex_unit] 将 m 发送到 (s ↦ s · m)。
*)
Definition coex_int_mul (n : Z) :
  carrier (cmon_setoid (rm_ab CoextInt)) :=
  cmon_map (rm_hom (coex_unit Int_Ring Int_RMod)) n.

Example coex_int_mul_at (n s : Z) :
  cmon_map (coex_int_mul n) s = (s * n)%Z := eq_refl.

(** The comparison map out: evaluation at 1, which is the counit. / 比较图：在 1 处评估，即余单位。 *)
Definition coex_int_eval :
  rm_ab CoextInt ~{Ab}~> ring_ab Int_Ring :=
  coex_counit Int_Ring (ring_ab Int_Ring).

Example coex_int_eval_computes :
  cmon_map coex_int_eval (coex_int_mul 3) = 3%Z := eq_refl.

Example coex_int_eval_zero :
  cmon_map coex_int_eval (cmon_zero (rm_ab CoextInt)) = 0%Z := eq_refl.

Example coex_int_act_computes :
  cmon_map coex_int_eval
    (rm_smul CoextInt 2%Z (coex_int_mul 3)) = 6%Z := eq_refl.

Lemma coex_int_nonzero : coex_int_mul 1 ≈ cmon_zero (rm_ab CoextInt) →
  False.
Proof.
  intro Hz.
  assert (Hev : (1%Z = 0%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

Lemma coex_int_muls_distinct : coex_int_mul 3 ≈ coex_int_mul 5 → False.
Proof.
  intro Hz.
  assert (Hev : (3%Z = 5%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

(*
   * The action is not trivial: 2 · (multiplication by 3) is not
   (multiplication by 3). 

   --------
   * 这个动作并不微不足道：2 · （乘以3）并不等于（乘以3）。
*)
Lemma coex_int_act_nontrivial :
  rm_smul CoextInt 2%Z (coex_int_mul 3) ≈ coex_int_mul 3 → False.
Proof.
  intro Hz.
  assert (Hev : (6%Z = 3%Z)) by
    exact (proper_morphism (cmon_map coex_int_eval) _ _ Hz).
  discriminate.
Qed.

(*
   * ** Probes

   Every strength claim the header makes is pinned here, each negative
   beside an APPLIED positive control.  Each was stripped of its [Fail]
   and compiled alone, and its WHOLE error read: negatives 1-4 and 7
   end in [cannot unify] (CONVERSION); negatives 5 and 6 are plain type
   mismatches with no [cannot unify] and no universe clause (TYPING);
   negatives 8-14 end in
   [universe inconsistency: Cannot enforce rc = ra] (FORMABILITY).
   Fifteen [Fail] commands in all: fourteen guarded negatives and one
   scope-free instrument check. 

   --------
   * ** 探针

   每一个头部提出的强度声明都在这里被验证，每一个阴性都与一个应用过的阳性对照相对应。每个声明都被剥离了其 [Fail] 并单独编译，其完整错误记录如下：阴性 1-4 和 7 以 [cannot unify] 结尾（转换）；阴性 5 和 6 是纯类型不匹配，没有 [cannot unify]，也没有通用条款（类型错误）；阴性 8-14 以 [universe inconsistency: Cannot enforce rc = ra] 结尾（可形成性）。总共有十五条 [Fail] 命令：十四条受保护的阴性和一条无作用域的仪器检查。
*)

Section CoexProbeStrength.

Context (R : RingObject) (A : AbObject) (M : RModObject R).
Context (g : rm_ab M ~{Ab}~> A) (h : M ~{RMod R}~> CoextObj R A).
Context (f f' : ring_ab R ~{Ab}~> A).
Context (m : carrier (cmon_setoid (rm_ab M))).
Context (r s : carrier (rig_setoid (ring_rig R))).

(*
 CONTROL for negative 1: the round trip DOES hold at ≈, and the proof
 term names the exact law that closes the gap. 

 --------
 对于负一的控制：往返确实在 ≈ 处成立，并且证明项命名了弥合差距的确切法则。
*)
Example coex_ctrl_from_to :
  cmon_map (coex_from R (coex_to R g)) m ≈ cmon_map g m
  := proper_morphism (cmon_map g) _ _ (rm_smul_one M m).

(*
 NEGATIVE 1 (CONVERSION).  [coex_from (coex_to g)] evaluates to
 g (1 · m), and 1 · − is not the identity by conversion:
 [rm_smul_one] is an abstract field of [RModObject], so neither side
 reduces and no downstream transparency would help. 

 --------
 负 1（转换）。[coex_from (coex_to g)] 评估为 g (1 · m)，并且 1 · − 并不是通过转换得到的恒等式：[rm_smul_one] 是 [RModObject] 的一个抽象域，因此两边都不能简化，后续的透明化也无济于事。
*)
Fail Example coex_probe_from_to_strict :
  cmon_map (coex_from R (coex_to R g)) m = cmon_map g m := eq_refl.

(* CONTROL for negative 2. / 负2的控制。 *)
Example coex_ctrl_to_from :
  cmon_map (cmon_map (rm_hom (coex_to R (coex_from R h))) m) s
    ≈ cmon_map (cmon_map (rm_hom h) m) s
  := iso_to_from (coex_adj R M A) h m s.

(* NEGATIVE 2 (CONVERSION). The other round trip evaluates the inner homomorphism at 1 · s rather than at s; [rig_mul_one_l] removes the residue and is likewise an abstract field. / 负二（转换）。另一次往返在 1 · s 上而不是在 s 上评估内部同态；[rig_mul_one_l] 移除剩余项，同样是一个抽象域。 *)
Fail Example coex_probe_to_from_strict :
  cmon_map (cmon_map (rm_hom (coex_to R (coex_from R h))) m) s
    = cmon_map (cmon_map (rm_hom h) m) s := eq_refl.

(* CONTROL for negative 3: the handedness that is actually built. / 对于负3的控制：实际建立的手性。 *)
Example coex_ctrl_handedness :
  cmon_map (coex_act R A r f) s
    = cmon_map f (rig_mul (ring_rig R) s r) := eq_refl.

(*
 NEGATIVE 3 (CONVERSION).  The OTHER handedness — translation on the
 left, (r · f)(s) = f (r s) — is a different map.  Over a
 non-commutative ring the two genuinely differ, and it is the built
 one that gives a LEFT module. 

 --------
 负三（换位）。另一个手性——左边的平移，(r · f)(s) = f(r s)——是一种不同的映射。在非交换环上，这两者确实不同，而构造的那个给出了一个左模。
*)
Fail Example coex_probe_handedness_swapped :
  cmon_map (coex_act R A r f) s
    = cmon_map f (rig_mul (ring_rig R) r s) := eq_refl.

(* CONTROL for negative 4: the underlying FUNCTIONS agree on the nose, which is why [coex_act_distr_l] closes by [reflexivity]. / 负 4 的控制：底层函数完全一致，这就是为什么 [coex_act_distr_l] 由 [reflexivity] 关闭。 *)
Example coex_ctrl_distr_l_pointwise :
  cmon_map (coex_act R A r (cmon_plus (coex_group R A) f f')) s
    = cmon_map (cmon_plus (coex_group R A)
                  (coex_act R A r f) (coex_act R A r f')) s := eq_refl.

(*
 NEGATIVE 4 (CONVERSION).  The two RECORDS are nevertheless distinct:
 [coex_act] is a [Program Definition], so each side carries its own
 opaque [cmon_map_zero] and [cmon_map_plus] obligations, built at
 different arguments.  So what separates them is exactly the law
 fields, the data having been shown to agree just above. 

 --------
 负 4（转换）。这两个记录仍然是不同的：
 [coex_act] 是一个 [Program Definition]，因此每一方都承担自己不透明的 [cmon_map_zero] 和 [cmon_map_plus] 义务，这些义务是基于不同的参数建立的。因此，将它们区分开的是确切的法律字段，数据已在上文显示一致。
*)
Fail Example coex_probe_distr_l_record :
  coex_act R A r (cmon_plus (coex_group R A) f f')
    = cmon_plus (coex_group R A)
        (coex_act R A r f) (coex_act R A r f') := eq_refl.

(* CONTROL for negative 5: the counit IS an arrow of [Ab]. / 负5的控制：余单位是 [Ab] 的一个箭头。 *)
Check (coex_counit R A : rm_ab (CoextObj R A) ~{Ab}~> A).

(*
 NEGATIVE 5 (TYPING).  It is NOT an arrow of [RMod R] — [A] is an
 [AbObject] and there is no coercion into [obj[RMod R]].  This is the
 shape of the adjunction rather than an accident: for a RIGHT adjoint
 the counit lives upstairs, in [Ab]. 

 --------
 负 5（打字）。它不是 [RMod R] 的箭头 —— [A] 是一个 [AbObject]，并且没有被强制成为 [obj[RMod R]。这是伴随的形状，而不是偶然：对于一个右伴随，辅单位位于上层，在 [Ab] 中。
*)
Fail Check (coex_counit R A : CoextObj R A ~{RMod R}~> A).

(* CONTROL for negative 6: the adjunction as delivered. / 负6的控制：所提供的附加。 *)
Check (coex_adjunction R : RMod_Forget_Ab R ⊣ Coextension R).

(*
 NEGATIVE 6 (TYPING).  The direction is not negotiable: coextension is
 the RIGHT adjoint, so the forgetful functor sits on the left. 

 --------
 负六（打字）。方向不可协商：共延伸是右伴随，所以遗忘函子位于左侧。
*)
Fail Check (coex_adjunction R : Coextension R ⊣ RMod_Forget_Ab R).

End CoexProbeStrength.

(* CONTROL for negative 7: the comparison map out exists and computes. / 对于负7的控制：比较映射存在并计算。 *)
Check (cmon_map coex_int_eval (coex_int_mul 3)).

(*
 NEGATIVE 7 (CONVERSION).  Hom(ℤ, ℤ) is NOT ℤ on the nose — the
 carriers are [AbHom (ring_ab Int_Ring) (ring_ab Int_Ring)] and [Z] —
 so [coex_int_muls_distinct] is a statement about a genuinely
 constructed object and not about ℤ in disguise. 

 --------
 负七（转换）。Hom(ℤ, ℤ) 并不严格等于 ℤ——其承载体是 [AbHom (ring_ab Int_Ring) (ring_ab Int_Ring)] 和 [Z]——所以 [coex_int_muls_distinct] 是关于一个真正构造的对象的陈述，而不是伪装成 ℤ 的陈述。
*)
Fail Example coex_probe_int_strict : CoextInt = Int_RMod := eq_refl.

Section CoexProbeUniverses.

Universes ra rb rc.
Constraint ra < rc.

Context (Ru : RingObject@{rc ra rb}) (Au Bu : AbObject).

(*
 CONTROLS.  With the ring's FIRST and THIRD universes declared strictly
 apart, all of these are formable, each APPLIED to the argument that
 carries the levels — so the identification below is neither the module
 category's, nor [ring_ab]'s, nor the forgetful functor's, nor
 [hom_ab]'s, nor the functor TYPE's. 

 --------
 控制。随着戒指的第一和第三宇宙被严格区分开来，所有这些都是可形成的，每一个都应用于承载这些层级的参数——因此下述的识别既不是模块范畴的，也不是 [ring_ab] 的，也不是遗忘函子的，也不是 [hom_ab] 的，也不是函子 TYPE 的。
*)
Check (RMod Ru).
Check (ring_ab Ru).
Check (RMod_Forget_Ab Ru).
Check (hom_ab Ab_AbEnriched Au Bu).
Check (Ab ⟶ RMod Ru).
Check (Ring_RMod Ru).
Check (obj[RMod Ru]).

(*
 NEGATIVE 8 (FORMABILITY).  THE DONOR, and it is neither this file's
 nor [Ab]-the-category's: the wall is met already at [AbHom], i.e. the
 moment a ring's additive group is read as the SOURCE of a
 homomorphism of abelian groups.  That is where [coex_group] begins,
 and everything below inherits it. 

 --------
 负 8（可成形性）。供体，并且既不是这个文件的，也不是 [Ab] 类别的：壁已经在 [AbHom] 遇到，即当一个环的加法群被作为阿贝尔群同态的源时的时刻。那就是 [coex_group] 开始的地方，下面的所有内容都继承它。
*)
Fail Check (AbHom (ring_ab Ru) Au).

(* NEGATIVE 9 (FORMABILITY). The same wall met the other way round. / 负 9（可成型性）。同一堵墙以相反方式遇到。 *)
Fail Check (ring_ab Ru : obj[Ab]).

(* NEGATIVE 10 (FORMABILITY). Hence the scalar action. / 负10（可形成性）。因此这个标量作用。 *)
Fail Check (coex_act Ru Au).

(* NEGATIVE 11 (FORMABILITY). Hence the carrier. / 负 11（可形成性）。因此是载体。 *)
Fail Check (coex_group Ru Au).

(*
 NEGATIVE 12 (FORMABILITY).  A SECOND, INDEPENDENT donor:
 Instance/Mod.v's own [Ring_RMod] is rejected at the very same levels
 with the very same message, and it mentions neither [Ab] nor this
 file.  So the identification would be met here even if the abelian
 side were repaired. 

 --------
 否定 12（可形成性）。第二个独立的供体：实例/Mod.v 自身的 [Ring_RMod] 在完全相同的级别被拒绝，并显示完全相同的消息，同时它既没有提到 [Ab]，也没有提到这个文件。因此，即使阿贝尔侧被修复，这里的识别仍然会成立。
*)
Fail Check (Ring_RMod Ru : obj[RMod Ru]).

(* NEGATIVE 13 (FORMABILITY). Hence the functor. / 负13（可形成性）。因此这个函子。 *)
Fail Check (Coextension Ru).

(* NEGATIVE 14 (FORMABILITY). And hence the headline. / 负14（可形成性）。因此才有了这个标题。 *)
Fail Check (coex_adjunction Ru).

End CoexProbeUniverses.

(* INSTRUMENT CHECK, scope-free: [Fail] itself is working. / 仪器检查，无范围限制：[Fail] 本身正在工作。 *)
Fail Example coex_probe_instrument : (true = false) := eq_refl.
