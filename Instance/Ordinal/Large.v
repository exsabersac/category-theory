Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * The large thin preorder of small ordinals / * * 小序数的大薄预序 *)

(*
 Mac Lane §V.6, book pp. 122-123 (maclane:V.6:remark-ord-counterexample);
 Awodey §9.8 Remark 9.30, printed pp. 253-254 (awodey:9.8:remark30).
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
 https://ncatlab.org/nlab/show/von+Neumann+ordinal
 https://ncatlab.org/nlab/show/W-type

 BACKGROUND.  Mac Lane's §V.6 remark is that the solution set condition
 cannot be dropped from the adjoint functor theorems, and his first
 witness is the ordered class of all small ordinals: it is small-complete
 (read in the direction in which a small product is a supremum), the
 constant one-point functor on it preserves every small limit, and yet
 that functor is not representable, because a representing object would
 be a largest small ordinal.  Awodey's Remark 9.30 makes the same point
 about the size discipline generally: the solution set must be a genuine
 set and the source complete at that size, or the theorem is not true.

 The ordinals here are the Aczel/W-type presentation rather than the von
 Neumann one: an ordinal IS a family of smaller ordinals, indexed by a
 small type -- the W-type W(Type, id).  Aczel introduced this shape for
 the type-theoretic interpretation of constructive set theory (Aczel,
 "The type theoretic interpretation of constructive set theory", Logic
 Colloquium '77, North-Holland 1978), and Taylor develops the ordinals of
 it (Taylor, "Intuitionistic sets and ordinals", Journal of Symbolic
 Logic 61, 1996).  The familiar Brouwer ordinal notations
 ([Zero | Succ | Lim (nat -> _)]) are the branching-restricted special
 case, not a different idea.  The ORDER is the extensional one: [x <= y]
 when every element of [x] is dominated by some element of [y].  That
 relation is reflexive and transitive but not antisymmetric, which is
 exactly what the library's Instance/Proset.v asks for -- a preorder, not
 a poset -- and is why no quotient is taken here.

 WHY THE UNIVERSE LEVEL IS THE WHOLE POINT.  [SmallOrd@{u}] is declared at
 [Type@{u+1}] while its index types range over [Type@{u}].  So the
 construction [osup] accepts exactly the [Type@{u}]-indexed families --
 the SMALL ones -- and [SmallOrd@{u}] itself is not among the types it
 accepts.  Every small family has a supremum ([ojoin]); the family of ALL
 ordinals does not, and could not, because a supremum of it would be a
 greatest element and [osucc] refutes that.  The two facts are not in
 tension only because of the level gap, and this file states them at
 levels that are MEASURED rather than asserted: see UNIVERSES below, where
 the same constant [Complete] is inhabited at one instance and refuted at
 another.

 The size boundary is the one Adjunction/GAFT.v describes and
 Structure/Complete.v cites Freyd for: a SMALL complete category is
 a preorder (Structure/Complete/Freyd.v's [small_complete_is_thin]).  The
 category below is a preorder, so it is consistent with Freyd's collapse
 and does not contradict it; what it adds is that being large is what lets
 a small-complete preorder have no top.

 WHAT IS DELIVERED (41 declaration heads -- 2 [Inductive], 39
 [Definition]/[Fixpoint]/[Lemma]/[Theorem]/[Example] -- introducing 43
 names once the two constructors [osup] and [opair] are counted;
 [Print Assumptions] reports "Closed under the global context" for all 43
 -- see the PRINT ASSUMPTIONS paragraph).
 (1) THE TYPE AND THE ORDER.  [SmallOrd@{u} : Type@{u+1}] with the single
 constructor [osup : forall Ix : Type@{u}, (Ix -> SmallOrd) ->
 SmallOrd]; the destructors [oidx] (the index type) and [oelt] (the
 indexed family); [ole] by structural recursion on its FIRST
 argument only -- [osup A f <= osup B g] iff every [f a] is below
 some [g b] -- and [olt x y] as "[x] is below some element of [y]".
 [ole_unfold] is the destructor-shaped characterisation; it is the
 one lemma proved by destructing both ordinals, and every later
 proof goes through it instead, which is what keeps the induction
 hypotheses usable.  [ole_refl], [ole_elem] (an element of an
 ordinal precedes it), [ole_trans], and the [PreOrder] instance
 [ole_preorder].  NO antisymmetry is claimed or needed.
 (2) THE THIN CATEGORY.  [SmallOrd_Proset] is [Proset ole_preorder] and
 [SmallOrd_op_Proset] is [Proset (op_PreOrder ole_preorder)] -- the
 same objects with the order reversed, which is what Mac Lane's
 "Ord^op" is.  Hom-sets are subsingletons on the nose:
 [smallord_equiv_is_True] records [(f ≈ g) = True] at [eq_refl], and
 [SmallOrd_Thin] / [SmallOrd_op_Thin] package that as
 Structure/Thin.v's predicate.  [SmallOrd_op_Proset] is used, rather
 than [SmallOrd_Proset^op], because the two categories are NOT
 convertible, and the divergence was LOCATED rather than guessed.
 In a section over an arbitrary [(P : PreOrder R)], under this
 file's import list, [eq_refl] is accepted for
 [obj[Proset (op_PreOrder P)] = obj[(Proset P)^op]] and for the
 same equation at [@hom], [@id], [@compose], and at the [equiv]
 component of the hom-setoid; it is REFUSED at
 [@Setoid.setoid_equiv _ (@homset (Proset (op_PreOrder P)) x y) =
 @Setoid.setoid_equiv _ (@homset ((Proset P)^op) x y)] and hence at
 [@homset] and at the whole [Category] record.  So the obstacle is
 not the category LAWS: it is the [Qed]-opaque [Program] obligation
 inside Instance/Proset.v's hom-setoid, which is one constant
 applied to [P] on one side and to [op_PreOrder P] on the other.
 (Instance/Proset/Limit.v records a DIFFERENT non-equality, of
 [Cocomplete (Proset P)] with [Complete (Proset (op_PreOrder P))];
 it is not this one.)  All the order machinery of
 Instance/Proset/Limit.v is stated over an arbitrary [PreOrder], so
 it applies to the reversed preorder directly and nothing is lost by
 using it.
 (3) SMALL SUPREMA.  [osum]/[opair] is the dependent-pair index type,
 declared here rather than taken from [sigT] so that BOTH components
 stay in [Type@{u}] by declaration instead of by inference;
 [ojoin A f] is [osup] of the disjoint union of the index types of
 the [f a], hence a small ordinal again.  [ojoin_ub] and
 [ojoin_least] say it is a least upper bound, and [ojoin_IsLUB]
 packages that as Instance/Proset/Limit.v's [IsLUB].  Note that
 [osup A f] itself is NOT the supremum of the [f a] -- it is the
 supremum of their successors -- which is why [ojoin] flattens.
 [ozero] is [osup] of the empty family and [ozero_least] makes it a
 bottom; [osucc] is [osup] of a [poly_unit]-indexed family, with
 [ole_osucc], [olt_osucc] and [osucc_not_ole].
 (4) SMALL-COMPLETENESS OF THE OPPOSITE.  [SmallOrd_HasAllJoins :
 HasAllJoins ole] is [ojoin] read through the bound predicates, and
 [SmallOrd_op_Complete : @Complete SmallOrd_op_Proset] is
 Instance/Proset/Limit.v's [Proset_op_Complete_of_all_joins] applied
 to it.  Its measured universe instance is the content: see
 UNIVERSES.  [SmallOrd_op_indexed_limit] is the indexed-product
 reading for a single family ([Proset_LUB_Limit], the shape being
 [DiscreteCat_Functor]), and [SmallOrd_op_Terminal] is the nullary
 case, the terminal object of [SmallOrd^op] being the least ordinal.
 [smallord_lub_not_zero] is the non-vacuity control in the style of
 Instance/Proset/Limit.v's [nat_glb_not_4]: [IsLUB] is a
 refutable predicate here, so the positive statements are not
 statements about a uniformly inhabited type.
 (5) NO GREATEST ELEMENT, AND THE UNIVERSE ARGUMENT MADE EXPLICIT.
 [olt_irrefl] (no ordinal is one of its own elements) is the one
 genuinely inductive negative lemma; from it [osucc_not_ole] and
 then [SmallOrd_no_greatest : forall m, ¬ forall x, ole x m].  The
 categorical readings are [SmallOrd_no_Terminal] and
 [SmallOrd_op_no_Initial].  Two further statements isolate WHERE the
 level gap does the work:
 - [SmallOrd_no_small_cofinal_family]: there is no [A : Type@{u}]
 and [e : A -> SmallOrd@{u}] with every ordinal below some
 [e a].  So [SmallOrd@{u}] is not cofinally [Type@{u}]-small --
 the sup construction of (3) cannot be applied to the whole
 class, and this is the precise sense in which (4) and (5) are
 compatible.
 - [SmallOrd_op_no_self_limit] and
 [SmallOrd_op_not_large_complete]: the identity diagram on
 [SmallOrd_op_Proset] has no limit, since a cone over it is a
 greatest element; hence [Complete] read with the DIAGRAM shape
 at the category's own object level is refuted, while (4)
 inhabits [Complete] with the diagram shape one level down.
 The two are instances of one constant at two universe
 instances, printed below.

 UNIVERSES (every line below is an [About] reading taken under
 [Set Printing Universes] on the compiled file; the constraint blocks are
 quoted verbatim except where a line says which entries are elided).
 - 27 of the 43 names carry an EMPTY constraint block over a single
 universe [u]: [SmallOrd@{u} : Type@{u+1}], [osup], [oidx@{u} :
 SmallOrd@{u} -> Type@{u}], [oelt], [ole@{u} : SmallOrd@{u} ->
 SmallOrd@{u} -> Prop], [ole_unfold], [ole_refl], [ole_elem],
 [ole_trans], [olt], [olt_ole], [olt_irrefl], [osum], [opair],
 [ojoin@{u} : forall A : Type@{u}, (A -> SmallOrd@{u}) ->
 SmallOrd@{u}], [ojoin_ub], [ojoin_least], [ozero], [ozero_least],
 [osucc], [ole_osucc], [olt_osucc], [osucc_not_ole],
 [SmallOrd_no_greatest@{u}], [SmallOrd_no_small_cofinal_family@{u}],
 [oidx_osup], [oelt_osup].  Nothing is identified with anything and
 [u] is free: the entire order theory, including both negative
 theorems of section 5, is one-universe.
 - [ole_preorder@{u} : PreOrder ole@{u}] is the first constant to leave
 that block, and it leaves it only for [u < RelationClasses.Defs.u0]
 -- the stdlib's own level for [PreOrder], not a level of this
 development.
 - [SmallOrd_Proset@{u u0 u1} : Category@{u u0 u0}] with [u1 < u]
 (the rest of its block is [u1 < RelationClasses.Defs.u0],
 [u <= RelationClasses.Defs.u0],
 [u <= Relation_Definitions.Relation_Definition.u0]).  Here [u1] is
 the ordinals' own universe and [u] the category's object universe:
 the category is LARGE by exactly one level, by construction and not
 by accident.  [SmallOrd_op_Proset] and [SmallOrd_op_Terminal] have
 the same signature shape.
 - [SmallOrd_HasAllJoins@{u u0 u1 u2 u3} : HasAllJoins@{u u0 u0 u1 u2 u3}
 ole@{u1}] with [u1 < u], [u <= u0], [u2 <= u0] (and
 [u <= Relation_Definitions.Relation_Definition.u0]).  The index
 universe of [HasAllJoins] -- its fourth binder, and the THIRD of
 [HasAllMeets], which [HasAllJoins] instantiates -- is
 [u1], the ordinals' own universe, one level BELOW the [u] at which
 [SmallOrd@{u1}] itself lives.  That identification is what makes the
 next line say "small", and it is forced by [ojoin], which accepts
 only a [Type@{u1}]-indexed family.
 - THE SLOT DECODER, so that the two [Complete] readings below can be
 compared without guessing.  [SmallOrd_op_indexed_limit@{u u0 u1 u2
 u3 u4 u5}] reads [forall (A : Type@{u}) (d : A -> SmallOrd@{u}),
 Limit@{u0 u u1 u2} (DiscreteCat_Functor@{u u1 u1 u2 u1 u1 u3} d)]
 with [u < u2].  Its diagram shape is [DiscreteCat A] with
 [A : Type@{u}] and its ambient category is [SmallOrd_op_Proset] at
 object level [u2]; so in [Limit@{a b c d}] the SECOND slot is the
 shape's object universe, the THIRD the shared hom universe, and the
 FOURTH the ambient category's object universe.  [Complete@{a b c d} :
 Category@{d c c} -> Type] follows the same layout, and
 Structure/Complete.v now writes those four out as [@{r so h o}].
 - [SmallOrd_op_Complete@{u u0 u1 u2 u3 u4 u5 u6 u7} :
 Complete@{u u0 u1 u2}] with [u0 < u2] among its constraints.  Read
 through the decoder: the diagram shape's objects sit at [u0] and the
 ambient category's at [u2], with [u0 < u2] between them.  That is
 small-completeness, in the only vocabulary the library has for it.

 RECORDED CORRECTION.  An earlier revision of these two bullets
 quoted [Limit@{u u Set u0}], [DiscreteCat_Functor@{u u0 u1 Set}] and
 [Complete@{u u Set u0}], each with a literal [Set] in the hom slot,
 and read the strict bound as [u < u0].  Those [Set]s were a
 universe-minimization artifact of Instance/Discrete.v's then
 unannotated [DiscreteCat_Functor]; it was annotated in place at its
 declaration in the PR "algebraic carriers are sets" (2026-09-17), the [Set]s
 are gone, and the binder lists lengthened, which is why the names of
 the strict bound moved.  The READING is unchanged: shape objects
 strictly below ambient objects, which is the whole point of the
 pair below.
 - [SmallOrd_op_not_large_complete@{u u0 u1 u2} : Complete@{u u1 u2 u1}
 -> False] with [u0 < u1], [u1 <= u], [u2 <= u].  The second and
 fourth slots are now the SAME universe [u1]: the diagram shape
 ranges over the ambient category's own object level.  Compare the
 previous line, where they are [u] and [u0] with [u < u0] between.
 One constant, inhabited at one instance and refuted at another: that
 is the universe argument, printed rather than narrated.
 [SmallOrd_op_no_self_limit@{u u0 u1 u2} : Limit@{u u1 u2 u1}
 Id@{u1 u2} -> False] is the same reading one layer down.
 - Stdlib levels reached.  [Proset] carries [RelationClasses.Defs.u0]
 and [Relation_Definitions.Relation_Definition.u0], inherited by
 every category-level constant here.  [SmallOrd_op_Complete]
 additionally carries, from [Proset_op_Complete_of_all_joins],
 [JMeq.JMeq.u0 <= JMeq.JMeq.u1], [u <= eq.u0],
 [u <= Logic_lemmas.equality.u0] and several
 [projections]/[Projections] bounds.  An earlier revision added "and
 four [Set < ...] bounds"; measured after the PR "algebraic carriers
 are sets" (2026-09-17) there are NONE -- zero word-bounded [Set]
 anywhere in that constant's block, the strict bounds now being
 [u0 < u2], [u1 < u4], [u1 < u5] and three against stdlib levels.
 Those are level constraints only: [Print Assumptions] on all 43
 names reports "Closed under the global context", with no [Axioms:]
 line anywhere.
 - Instance/Discrete.v's [DiscreteCat_Functor] does NOT pin the SOURCE
 SHAPE's objects to [Set] here, and since the repair it pins nothing
 at all.  Measured: [DiscreteCat_Functor@{u u1 u1 u2 u1 u1 u3} d] in
 [SmallOrd_op_indexed_limit] has the shape's object universe at [u],
 the family's own, and carries no literal [Set] in any slot.  An
 earlier revision of this bullet read [DiscreteCat_Functor@{u u0 u1
 Set} d], noted that the [Set] was "only in the fourth slot" with a
 [Set < u1] side constraint, and said the same of the [Set] in
 [Limit@{u u Set u0}] -- the HOM level, "harmless because every
 hom-set of a [Proset] and of a [DiscreteCat] is a proposition".
 That was the right reading of the artifact issue #1309 tracked, and
 the artifact was removed by applying #1309's repair in the PR
 "algebraic carriers are sets" (2026-09-17).  No object type of this
 development is at [Set], then or now.

 ONE TRAP WORTH RECORDING.  [I] is the Prelude's constructor of [True], so
 a [match] branch written [osup I f => I] is read with [I] as a PATTERN
 CONSTANT, and the elaborator reports "The term ... is expected to have
 type True" pointing at the binder.  The index binder is therefore named
 [Ix] in the inductive and [A]/[B] in every [match] below.  The message is
 stable under any import list, since it comes from the Prelude.

 PRINT ASSUMPTIONS.  Every one of the 43 names reports "Closed
 under the global context"; there are no [Axioms:] lines.  That includes
 [SmallOrd_op_Complete], which reaches [Proset_op_Complete_of_all_joins]
 and through it Structure/Limit.v and Instance/Discrete.v.

 STALE PREMISES OF ISSUE #444, RE-MEASURED (commands run over the [.v]
 files of the tree excluding [doc/], with [find . -name '*.v' | xargs
 grep], since [grep] here honours [.gitignore] on recursive traversal).
 - "The library has no ordinals as a category ([rg -w 'Ord|OrdCat'] -> a
 lone prose cross-reference in Instance/Proset.v)": the CONCLUSION
 is true, the evidence is not.  That figure is not re-measurable and an earlier revision of this
 sentence gave it as "96 hits in 8 files"; re-measured here with the
 command stated, [find . -name '*.v' -not -path './Instance/Ordinal/Large.v'
 | xargs grep -wn 'Ord\|OrdCat' | wc -l], the tree gives 79 matching
 lines (93 occurrences under [grep -wo]).  The exact figure is not the
 point and is recorded only so the sentence can be checked; what matters
 is that the issue's "a lone prose cross-reference" is wrong by two
 orders of magnitude
 category of PREORDERS (Mac Lane's Preord, #372), with satellites
 Instance/Ord/Poset.v, Test/ProbeOrd372.v, Instance/Roster.v,
 Construction/Reflective/Colimit.v, Construction/Subcategory/Dense.v
 and Instance/Top/Kolmogorov.v.  Neither that [Ord] nor
 Instance/Ordinal.v's [Ordinal (n : nat) : Category] (the FINITE
 ordinal [n] read as a category) is a category of ordinals, so no
 existing name is displaced and none is reused; this file's names are
 all prefixed [SmallOrd] or [o] and none of the 43 occurs elsewhere in
 the tree (checked word-wise, with a positive control).
 - "no smallness/largeness machinery": FALSE.  Theory/Size.v has
 [Class LocallySmall], [Class Small],
 [locally_small_ambient], [small_locally_small] and the witness
 [One_Small].  This file does not consume them -- see NOT DELIVERED --
 but the premise that they are missing is wrong.  The same claim in
 the issue's Awodey §9.8 checkbox ("the library has no smallness or
 local-smallness predicate at all") is wrong for the same reason.
 - "it records no example of a continuous functor without a left adjoint
 ([rg -i 'counterexample|no left adjoint'] -> nothing of this kind)":
 the grep is off (60 hits in more than 20 files), the conclusion
 stands for the sharp reading.  [not representable|continuous yet
 not|continuous but not] has exactly ONE hit in the tree,
 Adjunction/GAFT.v, and it is PROSE -- the Joyal/Mac Lane product
 of representables over the simple groups, cited, not built.
 Instance/Sets/NoAdjoint.v's twelve no-adjoint theorems are
 obstructions by limit preservation, a different shape.
 - "Complete Boolean algebras and Solovay's theorem are entirely absent
 ([rg -i 'solovay|complete boolean|CABA'] -> 0 hits)": ONE hit, not
 zero -- Instance/FdVect/NoRightAdjoint.v names Solovay, for the
 Solovay/Shelah measurability result, not for complete Boolean
 algebras.  The conclusion (no complete Boolean algebras, no free-CBA
 theorem) stands.
 - The cited background prose: the Adjunction/GAFT.v passage is the
 size obstruction, as claimed; the Structure/Complete.v passage is
 Freyd's collapse, as claimed; the Instance/Poset.v passage is NOT
 the adjoint functor discussion -- at the lines cited the file is on
 Lawvere's enrichment over the truth values.  The intended paragraph
 is the one after it, "Thinness also marks a size boundary in the
 adjoint functor theorems".
 - The dependency on #422 is live: Instance/Proset/Limit.v supplies
 [IsLUB], [HasAllJoins], [Proset_op_Complete_of_all_joins] and
 [Proset_LUB_Limit], all consumed here unchanged.

 NOT DELIVERED.
 - The functor half of the counterexample.  The constant one-point
 functor [SmallOrd^op ⟶ Sets], its continuity, and the refutation of
 its representability are NOT in this file; it supplies the category
 and the two order facts they need ([SmallOrd_op_Complete] and
 [SmallOrd_no_greatest], the latter in the categorical forms
 [SmallOrd_no_Terminal] and [SmallOrd_op_no_Initial]).  The issue
 places that half in Adjunction/GAFT/Necessity.v.
 - The Solovay/complete-Boolean-algebra half of §V.6: untouched.
 - Any connection to Theory/Size.v.  [SmallOrd_Proset] is NOT shown to
 be [LocallySmall] and is NOT shown to be non-[Small]; the largeness
 here is a universe-level fact recorded by [About], not a term of
 Theory/Size.v.  Making it one is a separate piece of work, because
 [Small] asks for a resizing of the OBJECT type and refuting it needs
 an argument that no such resizing exists, which is not what the
 universe gap gives on its own.
 - Antisymmetry, trichotomy, well-foundedness of [olt], ordinal
 arithmetic, the comparison with Instance/Omega.v's ω or with
 Instance/Ordinal.v's finite ordinals: none of it.  [ole] is a
 preorder and nothing more is claimed of it.
 - A [Test/] refutation probe.  The two refusals this file relies on for
 its strength claims (the non-convertibility of
 [Proset (op_PreOrder P)] with [(Proset P)^op], and the universe
 instance separating the two readings of [Complete]) are measured and
 quoted above but are not pinned by a refutation probe, so a later
 change could weaken them silently.  Filing that probe, in the style
 of the [Test/Probe*] files, is outstanding work.
 - No edit to any existing [.v] file.  Four support edits were made and
 are listed here so nothing is smuggled: the [_CoqProject] line; the
 two file counts in CLAUDE.md (981/985 -> 982/986, so that
 [make claude-md-counts-check] stays green) together with the
 [Instance/Ordinal.v] entry of its Order map; one bullet appended to
 docs/INDEX.md under "Concrete Instances" (269 -> 270 bullets, five
 headings before and after, [make index-check] green); and one
 [Print Assumptions] block appended to the Makefile's
 [print-assumptions] gate carrying all 43 names fully qualified. 

 --------
 Mac Lane §V.6，书页 122-123（maclane:V.6:remark-ord-counterexample）；
 Awodey §9.8 注释 9.30，印刷页 253-254（awodey:9.8:remark30）。
 nLab：https://ncatlab.org/nlab/show/adjoint+functor+theorem
 https://ncatlab.org/nlab/show/von+Neumann+ordinal
 https://ncatlab.org/nlab/show/W-type背景。Mac Lane 在 §V.6 中的评论是，解集条件不能从伴随函子定理中去掉，他的第一个例证是所有小序数的有序类：它是小完备的（以小积是上确界的方向来理解），对它的常数单点函子保持每个小极限，但该函子不可表示，因为一个表示对象将是最大的一个小序数。Awodey 的第 9.30 条评论也从一般的大小约束提出了同样的观点：解集必须是真正的集合，并且源在该大小下是完备的，否则定理不成立。这里的序数是 Aczel/W 型表示法，而不是冯·诺依曼的表示法：序数是较小序数的族，由一个小类型索引——即 W 型 W(Type, id)。Aczel 为构造性集合论的类型理论解释引入了这种形式（Aczel，《构造性集合论的类型理论解释》，逻辑研讨会 '77，北荷兰出版社 1978 年），而 Taylor 则发展了它的序数（Taylor，《直觉主义集合与序数》，符号逻辑杂志 61，1996 年）。熟悉的布劳威尔序数符号（[Zero | Succ | Lim (nat -> _)]）是分支受限的特殊情况，并不是不同的概念。序列是外延的：[x <= y] 当 [x] 的每个元素都被 [y] 的某个元素支配时。该关系是自反的和传递的，但不是反对称的，这正是库中的 Instance/Proset.v 所要求的——一个预序，而不是一个偏序——这也是这里没有取商的原因。为什么宇宙层次才是关键。[SmallOrd@{u}] 在 [Type@{u+1}] 声明，而其索引类型在 [Type@{u}] 上变化。因此构造 [osup] 恰好接受 [Type@{u}] 索引的族——也就是小族——而 [SmallOrd@{u}] 本身不在它接受的类型之中。每个小族都有一个上确界（[ojoin]）；所有序数的族没有，也不可能有，因为它的上确界将是一个最大元素，而 [osucc] 否认了这一点。这两条事实之所以不会冲突，仅仅因为层次差距，并且这个文件在被测量的层次上而非被断言的层次上陈述它们：见下面的 UNIVERSES，其中同一个常量 [Complete] 在一个实例中是可构造的，而在另一个实例中被否定。尺寸边界是 Adjunction/GAFT.v 所描述的，并且 Structure/Complete.v 引用了 Freyd 的内容：一个小的完备范畴是一个预序（Structure/Complete/Freyd.v 的 [small_complete_is_thin]）。下面的范畴是一个预序，因此它与 Freyd 的塌缩是一致的，并不与之矛盾；它所补充的是，成为大的恰恰是让一个小完备预序没有最大元的原因。交付内容是什么（41 个声明头——2 个 [Inductive]，39 个 [Definition] / [Fixpoint] / [Lemma] / [Theorem] / [Example]——在计算两个构造函数 [osup] 和 [opair] 后引入 43 个名称；[Print Assumptions] 对所有 43 个名称报告“在全局上下文下已封闭”——见 PRINT ASSUMPTIONS 段落）。（1）类型和顺序。[SmallOrd@{u} : Type@{u+1}]，单个构造函数 [osup : forall Ix : Type@{u}, (Ix -> SmallOrd) -> SmallOrd]；析构函数 [oidx]（索引类型）和 [oelt]（索引族）；[ole] 仅通过对其第一个参数进行结构递归——[osup A f <= osup B g] 当且仅当每个 [f a] 低于某个 [g b]——以及 [olt x y] 标记为“[x] 低于 [y] 的某个元素。”[ole_unfold] 是以析构器形式表示的特征化；它是通过析构两个序数证明的唯一引理，并且之后的每个证明都通过它进行，这也是保持归纳假设可用的原因。[ole_refl]、[ole_elem]（一个序数的元素在它之前）、[ole_trans]，以及 [PreOrder] 的实例 [ole_preorder]。没有要求或需要反对称性。(2) 薄范畴。[SmallOrd_Proset] 是 [Proset ole_preorder]，[SmallOrd_op_Proset] 是 [Proset (op_PreOrder ole_preorder)]——相同的对象但顺序颠倒，这就是 Mac Lane 的“Ord^op”。Hom-集是严格的子单集：[smallord_equiv_is_True] 记录 [(f ≈ g) = True] 在 [eq_refl]，[SmallOrd_Thin] / [SmallOrd_op_Thin] 将其打包为 Structure/Thin.v 的谓词。使用 [SmallOrd_op_Proset]，而不是 [SmallOrd_Proset^op]，因为这两类不可互换，并且分歧是被定位的，而不是猜测的。在一个关于任意 [(P : PreOrder R)] 的章节中，在此文件的导入列表下，[eq_refl] 被接受用于 [obj[Proset (op_PreOrder P)] = obj [(Proset P)^op] ] 以及在 [@hom]、[@id]、[@compose] 的相同方程，以及在同态集的 [equiv] 分量；它在 [@Setoid.setoid_equiv _ (@homset (Proset (op_PreOrder P)) x y) = @Setoid.setoid_equiv _ (@homset ((Proset P)^op) x y)] 被拒绝，因此在 [@homset] 以及整个 [Category] 记录中也被拒绝。所以障碍不是类别 LAWS：它是 Instance/Proset.v 的 hom-setoid 内的 [Qed] 不透明 [Program] 义务，它是在一侧对 [P] 应用一个常数，在另一侧对 [op_PreOrder P] 应用同一常数。（Instance/Proset/Limit.v 记录了一个不同的不等式，即 [Cocomplete (Proset P)] 与 [Complete (Proset (op_PreOrder P))]；这不是这个。）Instance/Proset/Limit.v 的所有序结构机制都是在任意 [PreOrder] 上表述的，因此它直接适用于反向预序，使用它时不会丢失任何信息。（3）小上确界。[osum] / [opair] 是依赖对索引类型，这里声明它而不是从 [sigT] 获取，以便两个组成部分通过声明而非推断保持在 [Type@{u}] 中；[ojoin A f] 是 [osup] 的 [f a] 索引类型的析取联合，因此又是一个小序数。[ojoin_ub] 和 [ojoin_least] 表示它是最小上界，[ojoin_IsLUB] 将其打包为 Instance/Proset/Limit.v 中的 [IsLUB]。注意 [osup A f] 本身不是 [f a] 的上确界——它是它们后继的上确界——这就是 [ojoin] 展平的原因。[ozero] 是空族的 [osup]，[ozero_least] 使它成为底部；[osucc] 是 [poly_unit] 索引族的 [osup]，并且包括 [ole_osucc]、[olt_osucc] 和 [osucc_not_ole]。(4) 对偶的小完备性。[SmallOrd_HasAllJoins : HasAllJoins ole] 是 [ojoin]，通过约束谓词进行读取，而 [SmallOrd_op_Complete : @Complete SmallOrd_op_Proset] 是 Instance/Proset/Limit.v 的 [Proset_op_Complete_of_all_joins] 应用于它。其测量宇宙实例为内容：见 UNIVERSES。[SmallOrd_op_indexed_limit] 是单个族的索引积读取（[Proset_LUB_Limit]，形状为 [DiscreteCat_Functor]），而 [SmallOrd_op_Terminal] 是零元情况，[SmallOrd^op] 的终端对象是最小序数。[smallord_lub_not_zero] 是非空性控制，风格类似于 Instance/Proset/Limit.v 的 [nat_glb_not_4]：[IsLUB] 在此是可反驳的谓词，因此正面陈述并不是关于均匀充实类型的陈述。(5) 无最大元素，并且明确提出宇宙论证。[olt_irrefl]（没有序数是其自身的元素）是真正的归纳负引理；由它得出 [osucc_not_ole] 然后是 [SmallOrd_no_greatest : forall m, ¬ forall x, ole x m]。范畴性读法是 [SmallOrd_no_Terminal] 和 [SmallOrd_op_no_Initial]。还有两个陈述指出了层级差距发挥作用的地方：
 - [SmallOrd_no_small_cofinal_family]：不存在 [A : Type@{u}] 和 [e : A -> SmallOrd@{u}]，使得每个序数都小于某个 [e a]。因此 [SmallOrd@{u}] 并不是按共尾关系 [Type@{u}]-小——(3) 的上确界构造不能应用于整个类，这正是 (4) 和 (5) 兼容的确切意义。- [SmallOrd_op_no_self_limit] 和 [SmallOrd_op_not_large_complete]：[SmallOrd_op_Proset] 上的恒等图没有限制，因为它的上锥是一个最大元素；因此，在该范畴自身对象层次上使用 DIAGRAM 形状读取 [Complete] 是被否定的，而 (4) 则在下一级图形中驻留于 [Complete]。两者是同一个常量在两个宇宙实例中的例子，如下所示。宇宙（下面的每一行都是在已编译文件下进行的 [About] 读数；约束块被逐字引用，除非某行说明哪些条目被省略）.- 在 43 个名字中，有 27 个名字在单一宇宙上携带空约束块 [u]：[SmallOrd@{u} : Type@{u+1}]，[osup]，[oidx@{u} : SmallOrd@{u} -> Type@{u}]，[oelt]，[ole@{u} : SmallOrd@{u} -> SmallOrd@{u} -> Prop]，[ole_unfold]，[ole_refl]，[ole_elem]，[ole_trans]，[olt]，[olt_ole]，[olt_irrefl]，[osum]，[opair]，[ojoin@{u} : forall A : Type@{u}, (A -> SmallOrd@{u}) -> SmallOrd@{u}]，[ojoin_ub]，[ojoin_least]，[ozero]，[ozero_least]，[osucc]，[ole_osucc]，[olt_osucc]，[osucc_not_ole]，[SmallOrd_no_greatest@{u}]，[SmallOrd_no_small_cofinal_family@{u}]，[oidx_osup]，[oelt_osup]。没有任何事物与任何事物同一，[u] 是自由的：整个序理论，包括第 5 节的否定定理，都是一个宇宙。 - [ole_preorder@{u} : PreOrder ole@{u}] 是第一个离开该区块的常量，它只为 [u < RelationClasses.Defs.u0] 离开该区块——这是 stdlib 自身的 [PreOrder] 层次，而不是本开发的层次。 - [SmallOrd_Proset@{u u0 u1} : Category@{u u0 u0}] 与 [u1 < u]（其区块的其余部分是 [u1 < RelationClasses.Defs.u0]、[u <= RelationClasses.Defs.u0]、[u <= Relation_Definitions.Relation_Definition.u0]）。这里 [u1] 是序数的自身宇宙，而 [u] 是范畴的对象宇宙：该范畴恰好比一个层次大，根据构造而非偶然。[SmallOrd_op_Proset] 与 [SmallOrd_op_Terminal] 具有相同的签名形式。- [SmallOrd_HasAllJoins@{u u0 u1 u2 u3} : HasAllJoins@{u u0 u0 u1 u2 u3} ole@{u1}] 与 [u1 < u], [u <= u0], [u2 <= u0]（以及 [u <= Relation_Definitions.Relation_Definition.u0]）。[HasAllJoins] 的索引宇宙——它的第四个绑定器，以及 [HasAllMeets] 的第三个，[HasAllJoins] 实例化——是 [u1]，序数自身的宇宙，比 [u] 所在的级别低一级，而 [SmallOrd@{u1}] 本身就存在于该级别。正是这种识别使下一行显示为“小”，并且这是由 [ojoin] 强制的，[ojoin] 仅接受 [Type@{u1}] 索引的族。- 槽解码器，因此下面的两个 [Complete] 读数可以在不猜测的情况下进行比较。[SmallOrd_op_indexed_limit@{u u0 u1 u2 u3 u4 u5}] 读取 [forall (A : Type@{u}) (d : A -> SmallOrd@{u}), Limit@{u0 u u1 u2} (DiscreteCat_Functor@{u u1 u1 u2 u1 u1 u3} d)]，带有 [u < u2]。其图形形状为 [DiscreteCat A]，带有 [A : Type@{u}]，其环境范畴为 [SmallOrd_op_Proset]，在对象层次 [u2]；因此在 [Limit@{a b c d}] 中，第二个槽是形状的对象宇宙，第三个是共享的 Hom 宇宙，第四个是环境范畴的对象宇宙。[Complete@{a b c d} : Category@{d c c} -> Type] 遵循相同的布局，Structure/Complete.v 现在将这四个写为 [@{r so h o}]。-[SmallOrd_op_Complete@{u u0 u1 u2 u3 u4 u5 u6 u7} : Complete@{u u0 u1 u2}] 带有 [u0 < u2] 作为其约束之一。通过解码器阅读：图形形状的对象位于 [u0]，环境类别的对象位于 [u2]，它们之间是 [u0 < u2]。这就是小完备性，这是库中仅有的描述它的词汇。已记录更正。之前对这两个项目符号的修订引用了 [Limit@{u u Set u0}]、[DiscreteCat_Functor@{u u0 u1 Set}] 和 [Complete@{u u Set u0}]，每个在 hom 位置都有一个文字 [Set]，并且将严格界限读取为 [u < u0]。这些 [Set] 是 Instance/Discrete.v 当时未注释的 [DiscreteCat_Functor] 的宇宙最小化工件；它在 PR “代数承载体是集合”（2026-09-17）中在其声明位置被注释，[Set] 已经消失，并且绑定列表加长，这就是严格界限名称移动的原因。阅读不变：形状对象严格位于环境对象之下，这就是下面成对内容的全部意义。- [SmallOrd_op_not_large_complete@{u u0 u1 u2} : Complete@{u u1 u2 u1} -> False] 与 [u0 < u1]、[u1 <= u]、[u2 <= u]。第二和第四个插槽现在是同一宇宙 [u1]：图表形状跨越了环境类别自身的对象层级。比较前一行，它们是 [u] 和 [u0]，中间有 [u < u0]。一个常量，在某一实例中存在而在另一实例中被否定：这就是宇宙论证，以打印形式而非叙述形式呈现。[SmallOrd_op_no_self_limit@{u u0 u1 u2} : Limit@{u u1 u2 u1} Id@{u1 u2} -> False] 在下一层的读法是相同的。- 已达到标准库级别。[Proset] 承载 [RelationClasses.Defs.u0] 和 [Relation_Definitions.Relation_Definition.u0]，被此处每个类别级常量继承。[SmallOrd_op_Complete] 另外承载自 [Proset_op_Complete_of_all_joins] 的 [JMeq.JMeq.u0 <= JMeq.JMeq.u1]、[u <= eq.u0]、[u <= Logic_lemmas.equality.u0] 以及几个 [projections] / [Projections] 上界。早期的修订增加了“以及四个 [Set < ...] 边界”；在 PR“代数载体是集合”(2026-09-17)之后测量，根本没有——在该常量块中的任何地方都没有字界 [Set]，现在严格的边界为 [u0 < u2]、[u1 < u4]、[u1 < u5] 以及对标准库级别的三个约束。这些只是级别约束：[Print Assumptions] 在所有 43 个名称上报告“在全局上下文下封闭”，没有任何 [Axioms:] 行。- Instance/Discrete.v 的 [DiscreteCat_Functor] 并未将 SOURCE SHAPE 的对象固定在此处的 [Set] 上，并且自修复以来，它根本没有固定任何对象。测量结果：[DiscreteCat_Functor@{u u1 u1 u2 u1 u1 u3} d] 在 [SmallOrd_op_indexed_limit] 中，其形状对象的宇宙位于 [u]，即家族自身，并且在任何槽中都不携带字面 [Set]。此要点的早期版本写作 [DiscreteCat_Functor@{u u0 u1 Set} d]，指出 [Set] “只在第四个位置”，且具有 [Set < u1] 的附加约束，并对 [Set] 在 [Limit@{u u Set u0}] 中也作了同样的说明——HOM 级别，“无害，因为每个 [Proset] 与 [DiscreteCat] 的 hom 集都是一个命题”。这是对跟踪的工件问题 #1309 的正确解读，该工件通过在 PR “代数承载是集合” (2026-09-17) 中应用 #1309 的修复而被移除。此开发的任何对象类型无论当时还是现在都不在 [Set]。一个值得记录的陷阱。[I] 是 Prelude 中 [True] 的构造函数，所以一个写作 [osup I f => I] 的 [match] 分支被作为 PATTERN CONSTANT 使用 [I] 读取，并且 elaborator 会在绑定器处报告“期望...的类型为 True”。因此，在归纳中索引绑定器被命名为 [Ix]，而在下面的每个 [match] 中则命名为 [A] / [B]。这个消息在任何导入列表下都是稳定的，因为它来源于 Prelude。

 打印假设。43个名字中的每一个都报告“在全局上下文下封闭”；没有 [Axioms:] 行。其中包括 [SmallOrd_op_Complete]，它可以追溯到 [Proset_op_Complete_of_all_joins]，并通过它访问 Structure/Limit.v 和 Instance/Discrete.v。问题 #444 的陈旧前提，重新测量（命令在树的 [.v] 文件上运行，不包括 [doc/]，用 [find . -name '*.v' | xargs grep]，因为此处的 [grep] 在递归遍历中遵循 [.gitignore]）。- “该库没有作为类别的序数（[rg -w 'Ord|OrdCat'] -> Instance/Proset.v 中的孤立散文交叉引用）”：结论是正确的，证据却不正确。该数字不可重新测量，句子的早期版本给出的数字是“8 个文件中 96 次命中”；在这里用所述命令重新测量 [find . -name '*.v' -not -path './Instance/Ordinal/Large.v' | xargs grep -wn 'Ord\|OrdCat' | wc -l]，树中给出 79 条匹配行（[grep -wo] 下有 93 次出现）。确切数值并不重要，并且仅记录以便可以检查句子；重要的是，该问题中的“一个孤立的散文交叉引用”错误了两个数量级，属于 PREORDERS 类别（Mac Lane 的 Preord，第 372 号），相关文件有 Instance/Ord/Poset.v, Test/ProbeOrd372.v, Instance/Roster.v, Construction/Reflective/Colimit.v, Construction/Subcategory/Dense.v 和 Instance/Top/Kolmogorov.v。既不是 [Ord]，也不是 Instance/Ordinal.v 的 [Ordinal (n : nat) : Category]（将有限序数 [n] 作为一个类别来读取）是序数类别，因此没有现有的名称被替代，也没有名称被重用；该文件的名称均以 [SmallOrd] 或 [o] 为前缀，并且这 43 个名称在整个树中均未出现过（以词为单位检查，并设有阳性对照）。- “没有小/大机制”：错误。Theory/Size.v 包含  
 [Class LocallySmall]，[Class Small]，  
 [locally_small_ambient]，[small_locally_small] 以及见证 [One_Small]。该文件并未使用它们——见“未交付”——  
 但它们缺失的前提是错误的。同样地，在该问题的 Awodey §9.8 复选框中（“库中根本没有小性或局部小性谓词”）的说法也是错误的，原因相同。  

 - “它没有记录没有左伴随的连续函子示例（[rg -i 'counterexample|no left adjoint'] -> 没有此类东西）”：  
 grep 搜索有误（在 20 多个文件中有 60 次命中），对于严格的解读，结论仍然成立。[不可表示|连续但未表示
 不可|连续但不] 在树中恰好有一次命中，
 Adjunction/GAFT.v，它是 PROSE -- Joyal/Mac Lane 对简单群上可表示对象的积，已引用，未构造。Instance/Sets/NoAdjoint.v 的十二个无伴随定理是
 由极限保持带来的障碍，形状不同。- “完备布尔代数和 Solovay 定理完全缺失
 ([rg -i 'solovay|complete boolean|CABA'] -> 0 命中)”: 一次命中，不是零 -- Instance/FdVect/NoRightAdjoint.v 提到 Solovay，用于
 Solovay/Shelah 可测性结论，不是用于完备布尔代数。结论（无完备布尔代数，无自由-CBA 定理）依然成立。- 引用的背景文本：Adjunction/GAFT.v 段落是大小障碍，正如所声称的；Structure/Complete.v 段落是 Freyd 的坍缩，正如所声称的；Instance/Poset.v 段落**不是**伴随函子讨论——在引用的行，该文件讨论的是 Lawvere 在真值上的增强。意图段落是其后的段落，“稀薄性也标志着伴随函子定理中的大小边界”。- 对 #422 的依赖是活跃的：Instance/Proset/Limit.v 提供 [IsLUB]、[HasAllJoins]、[Proset_op_Complete_of_all_joins] 和 [Proset_LUB_Limit]，均在此处未作修改地被使用。未交付。- 反例的函子部分。常数单点函子 [SmallOrd^op ⟶ Sets]、其连续性以及其表示性的反驳不在此文件中；该文件提供它们所需的范畴和两个序事实（[SmallOrd_op_Complete] 和 [SmallOrd_no_greatest]，后者以范畴形式 [SmallOrd_no_Terminal] 和 [SmallOrd_op_no_Initial] 表示）。此问题将该部分置于 Adjunction/GAFT/Necessity.v 中。- §V.6 的 Solovay/完备布尔代数部分：未触及。- 与 Theory/Size.v 的任何关联 [SmallOrd_Proset] 尚未显示为 [LocallySmall]，亦未显示为非 [Small]；此处的大量性是由 [About] 记录的宇宙级事实，而不是 Theory/Size.v 的项。将其合并为一个是另一项独立的工作，因为
 [Small]  要求对 OBJECT 类型进行调整大小，而反驳它需要一个论证，即不存在这样的调整大小，这不是宇宙差距本身给出的。- 反对称性、三分性、[olt] 的良基性、序数算术、与 Instance/Omega.v 的 ω 或与 Instance/Ordinal.v 的有限序数的比较：这些都没有。[ole] 是一个预序，并且没有声称它具有更多性质。- 一个 [Test/] 反驳探针。本文件所依赖的两项拒绝理由来支撑其强度主张（[Proset (op_PreOrder P)] 与 [(Proset P)^op] 的不可转换性，以及区分 [Complete] 两种读法的宇宙实例）已在上文进行了测量和引用，但尚未通过反驳探针固定，因此后续的更改可能会悄然削弱它们。按照 [Test/Probe*] 文件的风格提交该探针尚属未完成的工作。- 未对任何现有的 [.v] 文件进行编辑。进行了四次支持编辑，并在此列出，以确保没有任何内容被隐瞒：[_CoqProject] 行；CLAUDE.md 中的两个文件计数（981/985 -> 982/986，以保持 [make claude-md-counts-check] 绿色）以及其 Order map 的 [Instance/Ordinal.v] 条目；在 docs/INDEX.md 的“Concrete Instances”下添加了一个项目符号（从 269 -> 270 项符号，前后各五个标题，[make index-check] 绿色）；以及在 Makefile 的 [print-assumptions] 门上附加了 [Print Assumptions] 块，包含全部 43 个完全限定的名称。
*)

(** ** The type of small ordinals / ** 小序数的类型 *)

(* An ordinal is a [Type@{u}]-indexed family of ordinals. The result lives at [Type@{u+1}], one level above the types that may index it: that gap is the whole subject of this file. / 序数是一个以 [Type@{u}] 为索引的序数族。结果位于 [Type@{u+1}]，比可以索引它的类型高一级：这个差距是本文件的整个主题。 *)
Inductive SmallOrd@{u} : Type@{u+1} :=
  osup : forall (Ix : Type@{u}), (Ix -> SmallOrd) -> SmallOrd.

(* The index type of an ordinal, and its indexed family of elements. The index binder is written [A] and never [I]: see the trap recorded in the header. / 一个序数的索引类型及其索引的元素族。索引绑定器写作 [A]，而从不写作 [I]：参见标题中记录的陷阱。 *)
Definition oidx@{u} (x : SmallOrd@{u}) : Type@{u} :=
  match x return Type@{u} with osup A _ => A end.

Definition oelt@{u} (x : SmallOrd@{u}) : oidx@{u} x -> SmallOrd@{u} :=
  match x as x0 return (oidx@{u} x0 -> SmallOrd@{u}) with osup _ f => f end.

(* Both destructors compute on a constructor application. / 两个析构函数都在构造函数的应用上进行计算。 *)
Example oidx_osup@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  oidx (osup A f) = A := eq_refl.

Example oelt_osup@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  oelt (osup A f) = f := eq_refl.

(** ** The extensional order / ** 外延顺序 *)

(*
 [x <= y] when every element of [x] is dominated by some element of [y].
 The recursion is structural in the FIRST argument alone -- the inner
 [match] on [y] is a case analysis, not a recursive call -- which is what
 keeps the definition inside Coq's guard condition without a mutual
 fixpoint. 

 --------
 当  [x] 的每个元素都被  [y] 的某个元素支配时，[x <= y] 。递归仅在第一个参数中是结构化的 —— 内部在 [y] 上的 [match] 是一个情况分析，而不是递归调用 —— 这就是为什么定义能够在 Coq 的守护条件内，而不需要互相的 fixpoint。
*)
Fixpoint ole@{u} (x : SmallOrd@{u}) : SmallOrd@{u} -> Prop :=
  match x with
  | osup A f =>
      fun y => match y with
               | osup B g => forall a : A, exists b : B, ole (f a) (g b)
               end
  end.

(*
 The destructor-shaped reading of [ole].  Every proof below goes through
 this rather than destructing an ordinal, which is what keeps the
 induction hypotheses usable. 

 --------
 [ole] 的析构器形阅读。下面的每个证明都通过这个进行，而不是析构一个序数，这就是保持归纳假设可用的原因。
*)
Lemma ole_unfold@{u} (x y : SmallOrd@{u}) :
  ole x y <-> (forall a : oidx x, exists b : oidx y, ole (oelt x a) (oelt y b)).
Proof. destruct x, y; simpl; split; exact (fun h => h). Qed.

Lemma ole_refl@{u} (x : SmallOrd@{u}) : ole x x.
Proof. induction x as [A f IH]; simpl; intro a; exists a; exact (IH a). Qed.

(*
 Each element of an ordinal precedes it; equivalently, [osup A f] is an
 upper bound of its own family [f].  It is discharged by the induction
 hypothesis alone, with no case analysis on [f a]. 

 --------
 序数的每个元素都在其之前；等价地，[osup A f] 是其自身族 [f] 的上界。它仅通过归纳假设被消解，而无需对 [f a] 进行情况分析。
*)
Lemma ole_elem@{u} (x : SmallOrd@{u}) (a : oidx x) : ole (oelt x a) x.
Proof.
  revert a; induction x as [A f IH]; intro a.
  apply ole_unfold; intro a0; exists a; exact (IH a a0).
Qed.

Lemma ole_trans@{u} (x y z : SmallOrd@{u}) : ole x y -> ole y z -> ole x z.
Proof.
  revert y z; induction x as [A f IH]; intros y z Hxy Hyz.
  apply ole_unfold; intro a.
  destruct (proj1 (ole_unfold _ _) Hxy a) as [b Hb].
  destruct (proj1 (ole_unfold _ _) Hyz b) as [c Hc].
  exists c; exact (IH a _ _ Hb Hc).
Qed.

(*
 A preorder, and deliberately no more: [ole] is not antisymmetric, and a
 thin category needs only reflexivity and transitivity. 

 --------
 一个前序，并且刻意仅此而已：[ole] 不是反对称的，而薄范畴只需要自反性和传递性。
*)
Definition ole_preorder@{u} : PreOrder ole@{u} :=
  {| PreOrder_Reflexive  := ole_refl@{u}
   ; PreOrder_Transitive := ole_trans@{u} |}.

(* The strict order: [x] precedes some element of [y]. / 严格顺序：[x] 出现在 [y] 的某个元素之前。 *)
Definition olt@{u} (x y : SmallOrd@{u}) : Prop :=
  exists b : oidx y, ole x (oelt y b).

Lemma olt_ole@{u} (x y : SmallOrd@{u}) : olt x y -> ole x y.
Proof. intros [b Hb]; exact (ole_trans _ _ _ Hb (ole_elem y b)). Qed.

(* No ordinal precedes one of its own elements. This is the only genuinely inductive negative fact in the file, and everything that says "there is no top" reduces to it. / 没有序数先于它自身的某个元素。这是文件中唯一真正的归纳否定事实，所有说“没有顶”的说法都归结于它。 *)
Lemma olt_irrefl@{u} (x : SmallOrd@{u}) : olt x x -> False.
Proof.
  induction x as [A f IH]; intros [a Ha].
  exact (IH a (proj1 (ole_unfold _ _) Ha a)).
Qed.

(* * ** The thin category, and its opposite / * ** 瘦的类别及其相反的类别 *)

(*
 The objects are the small ordinals -- a [Type@{u+1}] -- and a hom-set is
 the PROPOSITION [ole x y]. 

 --------
 这些对象是小序数 —— 一个 [Type@{u+1}] —— 而一个同态集合是命题 [ole x y]。
*)
Definition SmallOrd_Proset : Category := @Proset SmallOrd ole ole_preorder.

(*
 Mac Lane's [Ord^op], built as the proset of the reversed preorder rather
 than as [SmallOrd_Proset^op].  The two are not convertible: they agree at
 [obj], [hom], [id], [compose] and the hom-setoid's [equiv], and diverge at
 [setoid_equiv], which is a [Qed]-opaque [Program] obligation of
 Instance/Proset.v applied to two different preorders (located, not
 guessed; the measurement is in the header).  Every theorem of
 Instance/Proset/Limit.v is stated over an arbitrary [PreOrder], so
 nothing is lost by building the reversed one directly. 

 --------
 Mac Lane 的 [Ord^op]，是作为逆序前序的 proset 构建的，而不是作为 [SmallOrd_Proset^op]。这两者不可互换：它们在 [obj]、[hom]、[id]、[compose] 以及 Hom-setoid 的 [equiv] 上一致，但在 [setoid_equiv] 上出现分歧，[setoid_equiv] 是 Instance/Proset.v 应用于两个不同前序的 [Qed] -不透明 [Program] 义务（已定位，不是猜测；度量位于标题中）。Instance/Proset/Limit.v 的每一个定理都是针对任意 [PreOrder] 陈述的，因此直接构建逆序的 proset 并不会丢失任何内容。
*)
Definition SmallOrd_op_Proset : Category :=
  @Proset SmallOrd (op_rel ole) (op_PreOrder ole_preorder).

(*
 Hom-sets are subsingletons on the nose: the hom-setoid of a proset
 relates any two parallel morphisms by [True], and that holds by
 reduction. 

 --------
 Hom-集在本质上是子单元：一个前序集合的 hom-等价类通过 [True] 关联任何两个平行态射，并且这是通过化简成立的。
*)
Example smallord_equiv_is_True (x y : SmallOrd)
  (f g : x ~{SmallOrd_Proset}~> y) : (f ≈ g) = True := eq_refl.

Definition SmallOrd_Thin : Thin SmallOrd_Proset :=
  fun _ _ _ _ => Logic.I.

Definition SmallOrd_op_Thin : Thin SmallOrd_op_Proset :=
  fun _ _ _ _ => Logic.I.

(** ** Small suprema / ** 小极值 *)

(*
 The index type of a join: the disjoint union, over [a : A], of the index
 types of the [f a].  It is declared here rather than taken from [sigT]
 so that both components are held at [Type@{u}] by DECLARATION; that is
 what keeps [ojoin] a small ordinal rather than making its smallness
 depend on how [sigT]'s levels happen to be inferred. 

 --------
 连接的索引类型：索引类型的析取并集，取自  [a : A] ，索引类型来自  [f a] 。它在此处声明，而不是从  [sigT]  获取，以便两个组件都通过 DECLARATION 保留在  [Type@{u}] ；这就是保持  [ojoin]  是一个小序数的原因，而不是使其小性依赖于 [sigT] 的层次是如何被推断的。
*)
Inductive osum@{u} (A : Type@{u}) (B : A -> Type@{u}) : Type@{u} :=
  opair : forall a : A, B a -> osum.

Arguments opair {A B} a b.

(*
 The supremum of a SMALL family of ordinals.  Note that [osup A f] is not
 itself that supremum -- it is the supremum of the successors of the
 [f a] -- so the construction flattens one level. 

 --------
 一小族序数的上确界。注意，[osup A f] 本身并不是该上确界——它是 [f a] 的后继的上确界——因此该构造将一个层次平坦化。
*)
Definition ojoin@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) : SmallOrd@{u} :=
  osup (osum A (fun a => oidx (f a)))
       (fun p => match p with opair a k => oelt (f a) k end).

Lemma ojoin_ub@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) (a : A) :
  ole (f a) (ojoin A f).
Proof. apply ole_unfold; intro k; exists (opair a k); exact (ole_refl _). Qed.

Lemma ojoin_least@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) (y : SmallOrd@{u})
  (H : forall a, ole (f a) y) : ole (ojoin A f) y.
Proof.
  apply ole_unfold; intros [a k].
  exact (proj1 (ole_unfold _ _) (H a) k).
Qed.

(* The two clauses packaged as Instance/Proset/Limit.v's predicate. / 作为 Instance/Proset/Limit.v 谓词打包的两个子句。 *)
Definition ojoin_IsLUB@{u +} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  IsLUB ole f (ojoin A f) :=
  (ojoin_ub A f, fun n Hn => ojoin_least A f n Hn).

(* The least ordinal: the empty family. [False] serves as the empty index type at every level, by cumulativity, so no [Set]-level empty type is pinned here. / 最小的序数：空族。[False] 作为每一级的空索引类型，由于累积性，因此没有 [Set] 级别的空类型被固定在这里。 *)
Definition ozero@{u} : SmallOrd@{u} := osup False (fun e => match e with end).

Lemma ozero_least@{u} (x : SmallOrd@{u}) : ole ozero x.
Proof. apply ole_unfold; intros []. Qed.

(* The successor: a one-element family. [poly_unit] is the library's universe-polymorphic unit (Lib/Setoid.v); [unit] would pin the index type to [Set]. / 继承者：一个单元素的族。[poly_unit] 是库的宇宙多态单元（Lib/Setoid.v）；[unit] 会将索引类型固定为 [Set]。 *)
Definition osucc@{u} (x : SmallOrd@{u}) : SmallOrd@{u} :=
  osup poly_unit@{u} (fun _ => x).

Lemma ole_osucc@{u} (x : SmallOrd@{u}) : ole x (osucc x).
Proof. exact (ole_elem (osucc x) ttt). Qed.

Lemma olt_osucc@{u} (x : SmallOrd@{u}) : olt x (osucc x).
Proof. exists ttt; exact (ole_refl x). Qed.

(* The successor is STRICTLY above: this is [olt_irrefl] read at [x]. / 继任者严格在上：这是在 [x] 读取的 [olt_irrefl]。 *)
Lemma osucc_not_ole@{u} (x : SmallOrd@{u}) : ole (osucc x) x -> False.
Proof. intro H; exact (olt_irrefl x (proj1 (ole_unfold _ _) H ttt)). Qed.

(* * ** Small-completeness of the opposite category / * ** 对偶范畴的小完备性 *)

(*
 Every [Type@{u}]-indexed family of ordinals has a join.  The index
 universe of [HasAllJoins] is the ordinals' OWN universe here, which is
 what turns the next definition into a small-completeness statement; the
 measured instance is quoted in the header. 

 --------
 每个 [Type@{u}] 索引的序数族都有一个并集。[HasAllJoins] 的索引宇宙在这里是序数自身的宇宙，这使得下一个定义成为一个小完备性陈述；测量实例在标题中被引用。
*)
Definition SmallOrd_HasAllJoins : HasAllJoins ole :=
  fun A f => existT _ (ojoin A f) (ojoin_IsLUB A f).

(*
 Mac Lane's "Ord^op is small-complete".  Every diagram whose shape
 category has objects at the ordinals' own universe -- one level BELOW
 the object type of [SmallOrd_op_Proset] -- has a limit. 

 --------
 Mac Lane 的“Ord^op 是小完备的”。每一个图的形状范畴的对象位于序数自身的宇宙中——比 [SmallOrd_op_Proset] 的对象类型低一个层次——都有极限。
*)
Definition SmallOrd_op_Complete : @Complete SmallOrd_op_Proset :=
  Proset_op_Complete_of_all_joins ole_preorder SmallOrd_HasAllJoins.

(*
 The indexed-product reading of one family, through
 Instance/Proset/Limit.v's [Proset_LUB_Limit]: the limit in
 [SmallOrd^op] of a discrete diagram is the join of its objects. 

 --------
 一个族的索引积读取，通过 Instance/Proset/Limit.v 的 [Proset_LUB_Limit]：一个离散图在 [SmallOrd^op] 中的极限是其对象的联合。
*)
Definition SmallOrd_op_indexed_limit@{u +}
  (A : Type@{u}) (d : A -> SmallOrd@{u}) :
  Limit (DiscreteCat_Functor (C:=SmallOrd_op_Proset) d) :=
  Proset_LUB_Limit ole_preorder d (ojoin A d) (ojoin_IsLUB A d).

(*
 The nullary case: the terminal object of [SmallOrd^op] is the least
 ordinal.  (The INITIAL object of [SmallOrd^op] would be a greatest
 ordinal, and is refuted below.) 

 --------
 零元情况：[SmallOrd^op] 的终对象是最小的序数。（[SmallOrd^op] 的初始对象将是最大的序数，下面将对此进行驳斥。）
*)
Definition SmallOrd_op_Terminal : @Terminal SmallOrd_op_Proset :=
  Proset_Terminal (op_PreOrder ole_preorder) ozero ozero_least.

(* Non-vacuity, in the sense of Instance/Proset/Limit.v's [nat_glb_not_4]: [IsLUB] is refutable here, so the positive statements above are not statements about a uniformly inhabited type. Zero is not a join of {zero, zero+1}. / 非空性，在 Instance/Proset/Limit.v 的意义上，[nat_glb_not_4] : [IsLUB] 在这里是可反驳的，因此上面的肯定陈述不是关于统一填充类型的陈述。零不是 {零, 零+1} 的并集。 *)
Lemma smallord_lub_not_zero@{u +} :
  IsLUB ole@{u} (pair_family ozero@{u} (osucc@{u} ozero@{u})) ozero@{u}
  -> False.
Proof. intros [Hub _]; exact (osucc_not_ole ozero (Hub false)). Qed.

(* * ** No greatest ordinal, and where the universe gap does the work / * ** 没有最大的序数，并且当宇宙间隙起作用时 *)

(* There is no greatest small ordinal: the successor of a candidate would have to precede it, and [olt_irrefl] refutes that. / 没有最大的最小序数：一个候选者的后继必须早于它，而 [olt_irrefl] 证明了这一点是错误的。 *)
Theorem SmallOrd_no_greatest@{u} (m : SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, ole x m) : False.
Proof. exact (osucc_not_ole m (H (osucc m))). Qed.

(*
 THE UNIVERSE ARGUMENT, STATED.  [SmallOrd@{u}] has no cofinal family
 indexed by a [Type@{u}]: if it had one, [ojoin] would turn it into a
 greatest element.  So the supremum construction of the previous section,
 which accepts every [Type@{u}]-indexed family, cannot be applied to the
 class of ALL ordinals -- not because the construction is partial, but
 because [SmallOrd@{u} : Type@{u+1}] is not a [Type@{u}] and no
 [Type@{u}] is cofinal in it.  This is the precise sense in which
 small-completeness and the absence of a top are compatible. 

 --------
 宇宙论证，阐述如下。  [SmallOrd@{u}] 没有由 [Type@{u}] 索引的上界族：如果它有的话，[ojoin] 会将其转化为最大元素。因此，上节中的上确界构造，它接受每一个 [Type@{u}] 索引的族，却不能应用于所有序数的类——不是因为该构造是部分的，而是因为 [SmallOrd@{u} : Type@{u+1}] 不是 [Type@{u}]，并且没有 [Type@{u}] 在其中是上界族。这正是小完备性与缺乏最大元素相兼容的精确意义。
*)
Theorem SmallOrd_no_small_cofinal_family@{u}
  (A : Type@{u}) (e : A -> SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, exists a : A, ole x (e a)) : False.
Proof.
  apply (SmallOrd_no_greatest (ojoin A e)); intro x.
  destruct (H x) as [a Ha].
  exact (ole_trans _ _ _ Ha (ojoin_ub A e a)).
Qed.

(* The order facts read categorically. / 顺序事实是按类别读取的。 *)
Theorem SmallOrd_no_Terminal (T : @Terminal SmallOrd_Proset) : False.
Proof.
  exact (SmallOrd_no_greatest _ (terminal_is_greatest ole_preorder T)).
Qed.

Theorem SmallOrd_op_no_Initial (Iobj : @Initial SmallOrd_op_Proset) : False.
Proof.
  exact (SmallOrd_no_greatest _
           (initial_is_least (op_PreOrder ole_preorder) Iobj)).
Qed.

(*
 The identity diagram on [SmallOrd^op] has no limit: a cone over it has a
 leg to every object, and in the reversed order that leg family IS the
 statement that the apex is a greatest ordinal.  Only the CONE is used,
 not the universal property. 

 --------
 在 [SmallOrd^op] 上的恒等图没有极限：其上的锥体对每个对象都有一条支腿，并且在逆序中，该支腿族就是顶点是最大序数的陈述。这里只使用了锥体，而不是泛性质。
*)
Theorem SmallOrd_op_no_self_limit
  (L : Limit (Id[SmallOrd_op_Proset])) : False.
Proof.
  destruct L as [[v legs] _].
  apply (SmallOrd_no_greatest v); intro x.
  exact (@vertex_map _ _ _ _ legs x).
Qed.

(*
 Hence [Complete] is refuted when its DIAGRAM shape is allowed to range
 over the category's own object universe -- while
 [SmallOrd_op_Complete] inhabits [Complete] with the diagram shape one
 universe below.  Same constant, two instances; the printed instances are
 quoted in the header's UNIVERSES paragraph, and they are the sharp form
 of Mac Lane's remark that the size discipline is doing real work. 

 --------
 因此，当其图形形状被允许在该范畴自身的对象宇宙中变化时，[Complete] 被驳斥——而 [SmallOrd_op_Complete] 则位于 [Complete] 内，其图形形状比一个宇宙低。同一个常量，两个实例；印刷的实例在标题的宇宙段落中引用，它们是 Mac Lane 关于大小规则正在发挥实际作用的评论的尖锐形式。
*)
Theorem SmallOrd_op_not_large_complete
  (HC : @Complete SmallOrd_op_Proset) : False.
Proof. exact (SmallOrd_op_no_self_limit (HC SmallOrd_op_Proset Id)). Qed.

(*
   * ** The control that keeps the previous theorem from being a triviality

   [SmallOrd_op_not_large_complete] refutes [Complete] at the diagonal
   instance, and a reader is entitled to ask whether that instance is
   uninhabitable for every category, in which case the refutation would say
   nothing about the ordinals.  It is not.  The SAME diagonal shape is
   inhabited in the UNREVERSED order, where [ozero] is a greatest lower
   bound of the identity diagram because it is least:

   About SmallOrd_self_limit  ->  Limit@{u u1 u0 u1} Id[SmallOrd_Proset]

   slots 2 and 4 both [u1], which is the pairing
   [SmallOrd_op_no_self_limit] refutes on the other side.  So the
   refutation is about the absence of a GREATEST ordinal, not about the
   universe pairing being unusable, and that is exactly the content
   Mac Lane's remark needs. 

   --------
   * ** 控制之前定理不变得平凡的因素

   [SmallOrd_op_not_large_complete] 在对角线实例上驳斥了 [Complete]，读者有权质问这个实例是否对每个范畴都是不可占据的，如果是的话，这个驳斥就无法说明序数。事实并非如此。在未反转的顺序中，同样的对角形是可占据的，其中 [ozero] 是恒等图的最大下界，因为它是最小的：

   关于 SmallOrd_self_limit -> Limit@{u u1 u0 u1} Id [SmallOrd_Proset]

   位置 2 和 4 都是 [u1]，它是配对 [SmallOrd_op_no_self_limit] 在另一边驳斥的。因此，这个驳斥是关于不存在最大序数，而不是关于宇宙配对不可使用，这正是 Mac Lane 的评论所需要的内容。
*)

Definition SmallOrd_self_limit : Limit (Id[SmallOrd_Proset]) :=
  Proset_Limit_general ole_preorder (Id[SmallOrd_Proset]) ozero
    (ozero_least, fun n Hn => Hn ozero).
