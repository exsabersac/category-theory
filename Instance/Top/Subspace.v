Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.SlicedInverse.
Require Import Category.Structure.SlicedInverse.Strict.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.

Generalizable All Variables.

(* * * Subspace and quotient topologies as sliced adjoint inverses / * * 子空间拓扑与商空间拓扑作为切片伴随逆 *)

(*
 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.9, read from the page images: the subspace construction, book
 pp. 132-133 (PDF pp. 141-142), the subspace topology as a
 right-adjoint-right-inverse of the sliced underlying-set functor
 (catalog id maclane:V.9:construction2); Proposition 1, book p. 133
 (PDF p. 142), which consumes it (maclane:V.9:prop1); the quotient
 construction, book pp. 133-134 (PDF pp. 142-143), the quotient
 topology as a left-adjoint-right-inverse of the cosliced one
 (maclane:V.9:construction3); and the sentence stating the dual of
 Proposition 1, book p. 134 (PDF p. 143), after which "This dual
 proposition and the above adjunction prove that Top has
 coequalizers" (the first clause of maclane:V.9:remark2, #458's
 catalog item).  The book numbers Proposition 1 and none of the
 constructions; the catalog ids are names, not book numbering.
 Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
 Exercise 7.32, printed p. 236 (PDF p. 248): the subspace topology on
 a subset (7sketches:7.3.2:ex7.32), as the catalogue under
 doc/plan/books summarizes it (that book was not consulted)
 nLab:      https://ncatlab.org/nlab/show/subspace+topology
 nLab:      https://ncatlab.org/nlab/show/quotient+space
 nLab:      https://ncatlab.org/nlab/show/initial+topology
 nLab:      https://ncatlab.org/nlab/show/topological+concrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)

 BACKGROUND.  The subspace topology on a subset of a space and the
 quotient topology on a set of equivalence classes are the basic
 induced topologies.  nLab's initial-topology page gives the general
 form: for functions f_i from a set S into spaces X_i, the coarsest
 topology on S making every f_i continuous, with the subspace topology
 the case of one injection; dually the finest topology making maps into
 S continuous, with the quotient topology the case of one surjection.
 nLab's topological concrete categories are the concrete categories
 with "nice features matching the ability to form weak and strong
 topologies in Top" (that page's Idea).  Mac Lane's §V.9 reads the
 one-map case, without the injection or the surjection, as an
 adjunction.  For a space X the underlying-set functor G induces a
 functor on slices,
 G ↓ X : (Top ↓ X) → (Set ↓ GX);
 its right adjoint L gives a set t : S → GX the topology whose opens
 are the preimages along t of the opens of X.  Mac Lane observes that
 G ↓ X after L is the identity and calls L a
 "right-adjoint-right-inverse" of G ↓ X; its counit is the identity,
 which is how Structure/SlicedInverse.v's record reads the name.  The
 book stresses that the universal property is about arbitrary spaces Y
 with arbitrary continuous maps into X, not only about subspaces.
 Dually,
 X ↓ G : (X ↓ Top) → (GX ↓ Set)
 has a left adjoint M giving t : GX → S the topology of the sets with
 open preimage, "with unit the identity map, so M is
 left-adjoint-right-inverse to X↓G".  Proposition 1 turns the first
 into equalizers (an element-free version of the equalizer as the set
 where two maps agree, with the subspace topology), and its dual turns
 the second into coequalizers.

 WHY THIS FILE IS OVER [PTopCat].  Over the tree's Type-valued [Top]
 neither adjunction is an [Adjunction] record.  That is measured at one
 universe assignment ([o < h], [h < so]; Instance/Top/Subspace/
 TypeValued.v's header quotes the refusals) and argued, not measured,
 at every other: [Top@{h o}] puts its homs strictly above its points,
 [o < h], because continuity quantifies over the opens of the codomain;
 a functor that builds spaces on the given point setoids must start
 from the slices of a [Sets] with homs at [o], while the sliced
 underlying-set functors land in the slices of one with homs at [h];
 and Theory/Adjunction.v's [Adjunction] identifies the hom levels of
 its two categories.  The subspace predicate, besides, quantifies over
 the opens of X and sits one universe above the points.
 Instance/Top/Prop.v's Prop-valued encoding removes both obstructions,
 and everything below is stated over it.  The readings that ARE
 formable over [Top] are Instance/Top/Subspace/TypeValued.v.

 WHAT IS HERE.
 - The subspace construction along an ARBITRARY setoid map
 [h : S → X], not only an inclusion.  [PSub X S h] has points [S]
 and the book's opens verbatim: [PSub_open] reads
 [POpen (PSub X S h) V] back as
 [ex (fun U => POpen X U /\ ∀ s, V s <-> U (h s))] at [eq_refl].
 [psub_universal] is the universal property over ARBITRARY spaces
 [Z] mapping in, both directions: a setoid map [g : Z → S] is
 continuous into [PSub X S h] if and only if [h ∘ g] is continuous.
 [psub_lift] is the book's form of it, a continuous [f : Z → X] with
 [f ≈ h ∘ g] making [g] a continuous map into the subspace.
 - Seven Sketches' Exercise 7.32 at a subset [Y ⊆ X] given by a
 predicate [P] ([ex732_Y], the sub-setoid, and [ex732_incl]).
 [ex732_def]: [A] is open iff [A = B ∩ Y] for an open [B] of [X], at
 [eq_refl].  [ex732_part1]: [Y] is open, [B] the whole of [X].
 [ex732_part2]: the three axioms of Definition 7.25, unions over an
 index type at any universe.  [ex732_part3]: the inclusion is
 continuous.
 - The quotient construction along an arbitrary setoid map
 [q : X → T].  [PQuot]'s opens are the [V] with
 [POpen X (fun x => V (q x))] AND respecting the equality of [T]
 ([PQuot_open], at [eq_refl]).  The second conjunct is the setoid
 discipline's addition to the book's predicate: the book's sets
 have an equality every predicate respects, and without it
 [popen_proper] could not hold at [T].  The tree already pairs such
 a respect-the-relation clause with the preimage condition, in
 Instance/Top.v's [CP_open] and Instance/Top/Wedge.v's
 [wedge_open].  [pquot_universal] is the universal property over
 arbitrary spaces [Z] mapping out; [pquot_desc] is the book's form.
 - The sliced functors.  [PForget_over X] (Mac Lane's G ↓ X) and
 [PForget_under X] (X ↓ G) are Structure/SlicedInverse.v's
 [Sliced PForget X] and [Cosliced PForget X] under local names:
 aliases, read back at [eq_refl] by [PForget_over_Sliced] and
 [PForget_under_Cosliced], so every adjunction below is an
 adjunction of the generic sliced functors.  An independent
 [Program] functor with the same actions would not do: in a scratch
 file its object action agrees with [Sliced PForget X] at
 [eq_refl], but the functor equation is refused ("cannot unify"),
 its obligations being [Qed] constants of its own.  [PSub_Functor
 X] (L) and [PQuot_Functor X] (M), and the adjunctions
 [psub_adjunction : PForget_over X ⊣ PSub_Functor X] and
 [pquot_adjunction : PQuot_Functor X ⊣ PForget_under X], each built
 by Theory/Adjunction.v's [Build_Adjunction'] from a hom-set
 bijection ([psub_adj_iso], [pquot_adj_iso]) that is the identity on
 underlying maps.  The object equations [psub_obj] and [pquot_obj]
 (G ↓ X after L, and X ↓ G after M, are the identity on objects) and
 the triangle facts [psub_counit] (the counit is [id_cast] of
 [psub_obj]) and [pquot_unit] (the unit is [id_cast] of the inverse
 of [pquot_obj]) are the convention of Adjunction/LeftInverse.v and
 Theory/Equivalence/Strict.v for "the counit (unit) is the
 identity".
 - The packaged constructions.  [subspace_RARI X :
 RightAdjointRightInverse (Sliced PForget X)] is the subspace
 construction in Structure/SlicedInverse.v's record, and
 [quotient_LARI X : LeftAdjointRightInverse (Cosliced PForget X)]
 the quotient construction in Theory/Equivalence/Strict.v's record,
 each the four facts above assembled ([subspace_RARI_right] and
 [quotient_LARI_left] read the adjoints back at [eq_refl]).
 - [PTop_HasEqualizers], Proposition 1 at [PForget]:
 Structure/SlicedInverse.v's [equalizers_from_sliced_RARI] fed
 [PForget_Faithful], [subspace_RARI] and the equalizers of [Sets]
 that Structure/Pullback/Reduction.v's
 [HasEqualizers_of_HasPullbacks_Terminal] builds from
 Instance/Sets/Pullback.v's [Sets_HasPullbacks] and Instance/Sets.v's
 [Sets_Terminal] -- the term of Adjunction/CokernelPair.v's
 [SetsEqualizers], restated so as not to require that file (see
 ROUTE AND COST).  [PTop_equalizer_obj] reads the equalizer of
 [f g : x ~> y] back at [eq_refl] as [PSub x S s], [s : S → x] the
 chosen [Sets] equalizer of the underlying maps, and
 [PTop_equalizer_arrow] reads its arrow as [psub_incl x S s]: the
 element-free form of the book's "take the set S of points x of X
 with fx = f'x and impose the subspace topology", with whatever
 equalizer the [Sets] donor chooses in place of that set.
 - [PTop_HasCoequalizers], the dual at [PForget]:
 Structure/SlicedInverse/Strict.v's [coequalizers_from_sliced_LARI]
 fed [PForget_Faithful], [quotient_LARI] and
 Instance/Sets/Coequalizer.v's [Sets_HasCoequalizers].
 [PTop_coequalizer_obj] reads the coequalizer back at [eq_refl] as
 [PQuot y (SetsCoeq Gf Gg) (sets_coeq_proj Gf Gg)], [Gf] and [Gg]
 the underlying maps: the quotient topology on the quotient of the
 points of [y] by the equivalence the pair generates; and
 [PTop_coequalizer_arrow] reads its arrow as [pquot_proj].
 - The two witnesses at concrete spaces, over Instance/Top/Prop.v's
 discrete [PPoint] and [PBool]: [PBool_subspace_RARI] and
 [PBool_quotient_LARI] are the two constructions at [PBool].
 [PBool_equalizer] is the equalizer of the identity and the
 constant map [pbool_true] on [PBool], two different maps
 ([pbool_maps_differ]); [PBool_equalizer_obj] reads it back at
 [eq_refl] as [PSub PBool] on the [Sets] equalizer of the
 underlying maps and [PBool_equalizer_rari] as the value of
 [rari_right PBool_subspace_RARI] there, and
 [PBool_equalizer_points] computes which points of [PBool] lie in
 it: exactly [true], so the equalizer is a proper, nonempty
 subspace.  [PBool_coequalizer] is the coequalizer of the two points
 [ppoint_false] and [ppoint_true] of [PBool], maps out of [PPoint]
 that differ ([ppoint_maps_differ]); [PBool_coequalizer_obj] reads
 it back at [eq_refl] as [PQuot PBool] on the [Sets] coequalizer and
 [PBool_coequalizer_lari] as the value of
 [lari_left PBool_quotient_LARI] there, and
 [PBool_coequalizer_points] identifies every point with [true] in
 it, while Instance/Top/Prop.v's [PBool_points_distinct] separates
 [false] from [true] in [PBool]: a proper quotient.

 STRENGTHS, measured strict first.
 - At [eq_refl]: [PSub_carrier], [PSub_open], [PQuot_carrier],
 [PQuot_open], [ex732_def], [psub_lift_map], [pquot_desc_map],
 [PForget_over_Sliced], [PForget_under_Cosliced],
 [PSub_Functor_obj], [PQuot_Functor_obj], the four transpose
 readbacks [psub_adj_to_map], [psub_adj_from_map],
 [pquot_adj_to_map], [pquot_adj_from_map], the object equations at
 an explicit pair, [psub_obj_pair] and [pquot_obj_pair],
 [subspace_RARI_right], [quotient_LARI_left], and the four
 (co)equalizer readbacks [PTop_equalizer_obj],
 [PTop_equalizer_arrow], [PTop_coequalizer_obj] and
 [PTop_coequalizer_arrow], and at the concrete spaces
 [PBool_equalizer_obj], [PBool_equalizer_rari],
 [PBool_coequalizer_obj] and [PBool_coequalizer_lari].
 - Leibniz, not [eq_refl] at a variable: [psub_obj] and [pquot_obj].
 Slice objects are stdlib [sigT] pairs, which have no eta, so at a
 variable [c] the equation takes a [destruct]; measured in a scratch
 file, the [eq_refl] at a variable is refused with "cannot unify" of
 the round trip and [c], while its first component is [eq_refl].
 - Four [Defined], each load-bearing, measured by closing it [Qed]
 alone in a scratch copy of this file.  [psub_obj] and [pquot_obj]:
 the triangle facts need the transport to reduce, and with either
 closed [Qed] the matching triangle fact is refused (Coq: Unable to
 unify "projT1 (id_cast (psub_obj (x; h))) t" with "t", and the
 [pquot_obj] twin).  [psub_adjunction] and [pquot_adjunction]: the
 counit and unit are computed through [Build_Adjunction'] from the
 hom-set bijection, and with either closed [Qed] the matching
 triangle fact is refused (Coq: Unable to unify "t" with "projT1
 counit t", and "projT1 unit t" for the quotient).
 - Up to [≈]: [psub_counit], [pquot_unit] (the record's convention),
 [psub_lift_comm], [pquot_desc_comm], and [PBool_coequalizer_points]
 in the coequalizer's setoid.
 - Propositional equivalences: [psub_universal], [pquot_universal],
 and [PBool_equalizer_points], whose "only if" is the fork equation
 and whose "if" is the equalizer's universal property at the point
 of [PPoint] picking [true].

 UNIVERSES, read by [About] under [Set Printing Universes].
 - [psub_open@{o}], [PSub@{o}], [psub_incl@{o}], [PQuot@{o}]: empty
 blocks.  [psub_universal], [psub_lift], [pquot_universal] and
 [pquot_desc] carry only the three [o <= compose.u*] caps of
 Instance/Sets.v's [setoid_morphism_compose].  [PSub] and [PQuot]
 are accepted at [PTop@{Set}] (scratch).
 - [ex732_Y@{o}] and the constants built on it carry [o <=
 Subset_projections.u0], the stdlib cap of [proj1_sig].
 - The sliced constants take [@{o so u}] (and one more universe for
 the adjunctions and the triangle facts), with [o < so] declared
 and [o < u] Construction/Slice.v's own strict bound of the hom
 level below a [Program] auxiliary universe.  [Set < so] is
 inherited from [PTopCat] and implied by [o < so]; [Set <
 Projections.u0] is implied by [so <= Projections.u0], the cap
 Construction/Slice.v's [Slice] carries on the object universe
 ([projT1]'s).  The adjunctions add the stdlib caps of
 [Build_Adjunction'] ([Logic_lemmas.equality], [prod_rect],
 [projections]), and [pquot_unit] and [quotient_LARI] add [so <=
 Logic_lemmas.equality.u0]: the stdlib [eq_sym] takes its type
 argument at that universe and is applied here to an equation
 between objects at [so], which is also why
 [LeftAdjointRightInverse]'s own block carries the cap on its
 second category's object universe.
 - [subspace_RARI@{o so u u0}] has type [∀ X,
 RightAdjointRightInverse@{so so o u0 u} (Sliced@{so o so o u0 u0
 so so} PForget@{o so} X)] and [quotient_LARI@{o so u u0}] has type
 [∀ X, LeftAdjointRightInverse@{so u0 u so o} (Cosliced@{so o so o
 u0 u0 so so} PForget@{o so} X)]: both slices' hom levels at the
 points' universe [o], and the two slice-auxiliary universes at one
 [u0], the identification Structure/SlicedInverse.v's header
 discloses.
 - [PTop_HasEqualizers@{o so u u0 u1 u2 u3} : HasEqualizers@{so o}
 PTopCat@{o so}] and [PTop_HasCoequalizers@{o so u u0 u1 u2 u3 u4} :
 HasCoequalizers@{so o} PTopCat@{o so}]: the structures sit at the
 category's own levels, and their blocks add only [<=] caps and
 strict bounds of [o] below auxiliary universes to the bounds
 above.
 - The witnesses at concrete spaces keep [o] and [so] throughout:
 [PBool_subspace_RARI@{o so u u0}] has type
 [RightAdjointRightInverse@{so so o u0 u} (Sliced@{so o so o u0 u0
 so so} PForget@{o so} PBool@{o})], [PBool_quotient_LARI@{o so u
 u0}] the cosliced dual; [PBool_equalizer@{o so u u0 u1 u2 u3}] and
 [PBool_coequalizer@{o so u u0 u1 u2 u3 u4}] are the (co)equalizers
 of [PTop_HasEqualizers] and [PTop_HasCoequalizers] at those
 instances, and each readback names them at [o] and [so] by an
 explicit instance, so that no [About] block carries a second copy
 of the two.  [pbool_true@{o}], [ppoint_false@{o}] and
 [ppoint_true@{o}] carry only [o <= Logic_lemmas.equality.u0], the
 cap Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object]
 carry.
 No universe is pinned at [Set], and the only [Set] in any block is the
 two implied bounds above: over the [About] output of all 111 of this
 file's constants (its [Print Module] listing, obligations included),
 [Set < so] occurs in 68 blocks and [Set < Projections.u0] in 17, each
 of those 17 also carrying [so <= Projections.u0]; no block carries an
 equation.

 ROUTE AND COST.  Closure: 81 [Category.*] modules excluding this file
 ([Print Libraries] on a file requiring it).  Before the packaging it
 was 45; adding the Requires in turn, Structure/SlicedInverse.v costs
 12 (to 57), its satellite Structure/SlicedInverse/Strict.v 1 more
 (Theory/Equivalence/Strict.v was required already),
 Instance/Sets/Coequalizer.v 13 (to 71), and the equalizer route
 (Structure/Pullback/Reduction.v with Instance/Sets/Pullback.v) 10 (to
 81).  The equalizer donor was chosen on that measurement against the
 same list: Adjunction/GAFT/Sets.v's [Sets_HasEqualizers] or
 Adjunction/CokernelPair.v's [SetsEqualizers] would give 87, and
 Adjunction/Diagonal/Finite.v's [DiagSets_HasEqualizers] 98.  The
 packaging needs only Structure/SlicedInverse.v (57); the other 24
 modules are spent by [PTop_HasEqualizers], [PTop_HasCoequalizers] and
 their readbacks, which stay here, where #457's plan places them.

 NOT DELIVERED.  Initial and final topologies for FAMILIES of maps and
 the product topology (catalog maclane:V.9:remark1, #458's), and so no
 products, completeness or cocompleteness of [PTopCat].  CORRECTION
 (#458): #458 delivers them, over this file's constructions:
 Instance/Top/Complete.v's [PInit] (the initial topology of a family,
 the product topology [PProd], completeness [PTop_Complete], and the
 book's route [PTop_Complete_via_products] through this file's
 [PTop_HasEqualizers]) and Instance/Top/Cocomplete.v's [PFinal] (the
 final topology, the coproduct [PSigma], cocompleteness
 [PTop_Cocomplete], and [PTop_Cocomplete_via_coproducts] through this
 file's [PTop_HasCoequalizers]); [PInit_one_PSub] and
 [pfinal_one_map_PQuot] there identify [PSub] and [PQuot] as the
 one-map cases, opens for opens.  Also not delivered here: any comparison
 of [PSub] or [PQuot] with the Type-valued constructions (Instance/Top/
 Presheaf.v's open subspaces, Instance/Top/Pushout.v's quotient,
 Instance/Top/Subspace/TypeValued.v's [TQuot]); any comparison of the
 [Sets] equalizer chosen here with the tree's other inhabitants of
 [HasEqualizers Sets]; the preservation corollaries
 ([equalizers_from_sliced_RARI_preserved] and its dual) restated at
 [PForget]; no uniqueness statement for L or M; and no witness whose
 topology is not discrete: at [PBool] the witnesses exhibit which
 points the equalizer and the coequalizer carry, and their opens are
 not computed here. 

 --------
 Mac Lane，《数学工作者的范畴论》，第2版（GTM 5），§V.9，从页面图像阅读：子空间构造，书中第132-133页（PDF第141-142页），子空间拓扑作为切片底集函子的右伴随右逆（目录ID maclane:V.9:construction2）；命题1，书中第133页（PDF第142页），它使用了该构造（maclane:V.9:prop1）；商构造，书中第133-134页（PDF第142-143页），商拓扑作为余切片的左伴随右逆（maclane:V.9:construction3）；以及陈述命题1对偶的句子，书中第134页（PDF第143页），之后“这个对偶命题和上述伴随证明了拓扑范畴具有余等化子”（maclane:V.9:remark2，第#458项目录的第一部分）。书中编号为命题 1，但没有对构造进行编号；目录 ID 是名字，而不是书籍编号。Fong 和 Spivak，《组合性的七个示意图》，§7.3.2，练习 7.32，印刷版第 236 页（PDF 第 248 页）：子集上的子空间拓扑（7sketches:7.3.2:ex7.32），正如 doc/plan/books 下的目录总结的那样（那本书未被查阅）
 nLab:       https://ncatlab.org/nlab/show/subspace+topology 
 nLab:       https://ncatlab.org/nlab/show/quotient+space 
 nLab:       https://ncatlab.org/nlab/show/initial+topology 
 nLab:       https://ncatlab.org/nlab/show/topological+concrete+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Quotient_space_(topology)背景。在空间的子集上的子空间拓扑以及在等价类集合上的商拓扑是基本的诱导拓扑。nLab 的初始拓扑页面给出了通用形式：对于从集合 S 到空间 X_i 的函数 f_i，使每个 f_i 连续的 S 上的最粗拓扑，其中子空间拓扑是一个单射的情况；对偶地，使映射到 S 的映射连续的最细拓扑，其中商拓扑是一射的情况。nLab 的拓扑具体范畴是具有“与在 Top 中形成弱拓扑和强拓扑的能力相匹配的优良特性的具体范畴”（该页面的思路）。Mac Lane 的 §V.9 将单映射情况（没有单射或满射）解读为一个伴随关系。对于一个空间 X，底集合函子 G 在切片上诱导一个函子，
 G ↓ X : (Top ↓ X) → (Set ↓ GX);
 它的右伴随 L 给出一个集合 t : S → GX 的拓扑，其开集是沿 t 的 X 的开集的原像。Mac Lane 观察到 G ↓ X 在 L 之后是恒等函数，并称 L 为 G ↓ X 的“右伴随-右逆”；它的余单位是恒等函数，这正是 Structure/SlicedInverse.v 的记录名称所表示的内容。书中强调，这一泛性质是关于任意空间 Y 及其任何连续映射到 X，而不仅仅是关于子空间。对偶地，
 X ↓ G : (X ↓ Top) → (GX ↓ Set)
 有一个左伴随 M，它给出 t : GX → S 的拓扑，其开集是原像为开集的集合，“其单位映射为恒等映射，因此 M 是 X↓G 的左伴随-左逆”。命题 1 将第一个变为等化器（等化器的无元素版本，作为两个映射相等的集合，并配以子空间拓扑），其对偶将第二个变为余等化器。为什么这个文件在 [PTopCat] 上。 在树的类型值 [Top] 上，
 没有一个陪集是 [Adjunction] 记录。这在一个宇宙赋值下测量（[o < h]，[h < so]；Instance/Top/Subspace/TypeValued.v 的头部引用了拒绝）并进行论证，而不是在其他每个情况测量：[Top@{h o}] 将其同态严格置于其点之上，[o < h]，因为连续性在余域的开集上量化；
 一个在给定点集上构建空间的函子必须从具有同态在 [o] 的 [Sets] 的切片开始，而切片的底层集合函子落在具有同态在 [h] 的对象切片中；
 并且 Theory/Adjunction.v 的 [Adjunction] 识别其两个范畴的同态级别。此外，子空间谓词对 X 的开集进行量化，并位于点的上方一层。Instance/Top/Prop.v 的 Prop 值编码消除了这两个障碍，而下面的所有内容都是基于它陈述的。可以在 [Top] 上形成的读法是 Instance/Top/Subspace/TypeValued.v。这里是什么。——沿任意集值映射 [h : S → X] 的子空间构造，不仅仅是包含。[PSub X S h] 有点 [S]，书中逐字打开：[PSub_open] 读作 [POpen (PSub X S h) V]，回到 [ex (fun U => POpen X U /\ ∀ s, V s <-> U (h s))] 在 [eq_refl]。[psub_universal] 是任意空间上的泛性质 [Z] 映入，两个方向：一个集值映射 [g : Z → S] 连续到 [PSub X S h] 当且仅当 [h ∘ g] 连续。[psub_lift] 是书中的形式，一个连续的 [f : Z → X] 与 [f ≈ h ∘ g] 使 [g] 成为子空间的连续映射。——《七幅素描》第 7.32 练习，在一个由谓词 [P] 给定的子集 [Y ⊆ X]（[ex732_Y]，子集值子集合，和 [ex732_incl]）。[ex732_def]：[A] 是开集当且仅当对 [X] 的开集 [B]，[eq_refl] 成立。[ex732_part1] : [Y] 是开集，[B] 是 [X] 的全部。[ex732_part2] : 定义7.25的三个公理，对任意宇宙中的指数类型的并集。[ex732_part3] : 包含映射是连续的。- 沿任意集合等价映射的商构造 [q : X → T]。[PQuot] 的开集是 [V]，并且 [POpen X (fun x => V (q x))]，且尊重 [T] 的相等性（[PQuot_open]，在 [eq_refl]）。第二个合取是集合等价纪律对书中谓词的补充：书中的集合每个谓词都尊重其相等性，没有它 [popen_proper] 就无法在 [T] 上成立。树已经将这样的尊重关系子句与原像条件配对，在 Instance/Top.v 的 [CP_open] 和 Instance/Top/Wedge.v 的 [wedge_open] 中。[pquot_universal] 是任意空间上的通用性质 [Z] 映射出; [pquot_desc] 是该书的形式。- 切片函子。[PForget_over X]（Mac Lane 的 G ↓ X）和 [PForget_under X]（X ↓ G）是 Structure/SlicedInverse.v 中的 [Sliced PForget X] 和 [Cosliced PForget X]，在本地名称下：别名，通过 [PForget_over_Sliced] 在 [eq_refl] 被读回，以及 [PForget_under_Cosliced]，因此下面的每个伴随都是通用切片函子的伴随。一个具有相同行为的独立 [Program] 函子是不可行的：在一个草稿文件中，它的对象作用在 [eq_refl] 上与 [Sliced PForget X] 一致，但函子方程被拒绝（“无法统一”），其义务为它自己的 [Qed] 常量。[PSub_Functor X]（L）和 [PQuot_Functor X]（M），以及伴随关系 [psub_adjunction : PForget_over X ⊣ PSub_Functor X] 和 [pquot_adjunction : PQuot_Functor X ⊣ PForget_under X]，每个都是由 Theory/Adjunction.v 的 [Build_Adjunction'] 从一个同态集双射（[psub_adj_iso], [pquot_adj_iso]）构建的，该双射在底层映射上是恒等的。对象方程 [psub_obj] 和 [pquot_obj]（G ↓ X 在 L 之后，以及 X ↓ G 在 M 之后，在对象上是恒等的）以及三角事实 [psub_counit]（余单位是 [psub_obj] 的 [id_cast]）和 [pquot_unit]（单位是 [pquot_obj] 的逆映射的 [id_cast]）是 Adjunction/LeftInverse.v 和 Theory/Equivalence/Strict.v 关于“余单位（单位）是恒等”的惯例。- 打包构造。[subspace_RARI X ：RightAdjointRightInverse（Sliced PForget X）] 是 Structure/SlicedInverse.v 的记录中的子空间构造，[quotient_LARI X : LeftAdjointRightInverse (Cosliced PForget X)] 是 Theory/Equivalence/Strict.v 的记录中的商构造，每个都是上述四个事实的组合（[subspace_RARI_right] 和 [quotient_LARI_left] 在 [eq_refl] 处读回伴随）。- [PTop_HasEqualizers]，命题 1 在 [PForget]：Structure/SlicedInverse.v 的 [equalizers_from_sliced_RARI] 输入 [PForget_Faithful]、[subspace_RARI] 以及 [Sets] 的等化器，Structure/Pullback/Reduction.v 的 [HasEqualizers_of_HasPullbacks_Terminal] 从 Instance/Sets/Pullback.v 的 [Sets_HasPullbacks] 和 Instance/Sets.v 的 [Sets_Terminal] 构建——Adjunction/CokernelPair.v 的 [SetsEqualizers] 的项，重新表述以不需要该文件（参见 ROUTE AND COST）。[PTop_equalizer_obj] 读取 [f g : x ~> y] 的等化子 回到 [eq_refl] 作为 [PSub x S s] ，[s : S → x] 作为基础映射的选定 [Sets] 等化子，并且 [PTop_equalizer_arrow] 将其箭头读取为 [psub_incl x S s] ：书中“取集合 X 的点 x 的集合 S 使得 fx = f'x 并施加子空间拓扑”的无元素形式，同时用 [Sets] 捐赠者选择的任何等化子代替该集合。- [PTop_HasCoequalizers] ，在 [PForget] 的对偶：Structure/SlicedInverse/Strict.v 的 [coequalizers_from_sliced_LARI] 喂入 [PForget_Faithful] ，[quotient_LARI] 和 Instance/Sets/Coequalizer.v 的 [Sets_HasCoequalizers] 。[PTop_coequalizer_obj] 将在 [eq_refl] 的余等化器读取为 [PQuot y (SetsCoeq Gf Gg) (sets_coeq_proj Gf Gg)]、[Gf] 和 [Gg] 的基本映射：在 [y] 的点的商上由等价对生成的商拓扑；并且 [PTop_coequalizer_arrow] 将其箭头读取为 [pquot_proj]。- 在具体空间上的两个见证者，在 Instance/Top/Prop.v 的离散 [PPoint] 和 [PBool] 上：[PBool_subspace_RARI] 和 [PBool_quotient_LARI] 是在 [PBool] 的两个构造。[PBool_equalizer] 是 [PBool] 上恒等映射和常值映射 [pbool_true] 的等化器，两个不同的映射（[pbool_maps_differ]）；[PBool_equalizer_obj] 在 [eq_refl] 上将其读回为 [Sets] 上基础映射的等化器上的 [PSub PBool]，以及 [PBool_equalizer_rari] 作为 [rari_right PBool_subspace_RARI] 在那里取的值，并且 [PBool_equalizer_points] 计算 [PBool] 的哪些点位于其中：恰好是 [true]，因此等化器是一个适当的、非空的子空间。[PBool_coequalizer] 是 [PBool] 中两点 [ppoint_false] 和 [ppoint_true] 的余等化器，从 [PPoint] 出来的映射如果有差异（[ppoint_maps_differ]）；[PBool_coequalizer_obj] 在 [eq_refl] 以 [PQuot PBool] 读取它，在 [Sets] 余等化器上，并将其作为 [lari_left PBool_quotient_LARI] 在那里的值，且 [PBool_coequalizer_points] 将其中的每个点与 [true] 认同，而 Instance/Top/Prop.v 的 [PBool_points_distinct] 将 [false] 与 [true] 在 [PBool] 中分开：一个适当的商。优势，严格测量优先。- 在 [eq_refl]：[PSub_carrier]，[PSub_open]，[PQuot_carrier]，[PQuot_open]，[ex732_def]，[psub_lift_map]，[pquot_desc_map]，[PForget_over_Sliced]，[PForget_under_Cosliced]，[PSub_Functor_obj]，[PQuot_Functor_obj]，四个转置回读 [psub_adj_to_map]，[psub_adj_from_map]，[pquot_adj_to_map]，[pquot_adj_from_map]，在一个显式对上的对象方程 [psub_obj_pair] 和 [pquot_obj_pair]，[subspace_RARI_right]，[quotient_LARI_left]，以及四个（共）等化器回读 [PTop_equalizer_obj]，[PTop_equalizer_arrow]，[PTop_coequalizer_obj] 和 [PTop_coequalizer_arrow]，以及在具体空间 [PBool_equalizer_obj]，[PBool_equalizer_rari]，[PBool_coequalizer_obj] 和 [PBool_coequalizer_lari]。- 莱布尼茨，不在变量上的 [eq_refl]：[psub_obj] 和 [pquot_obj]。切片对象是标准库 [sigT] 对，其没有 eta，因此在变量 [c] 处，方程会出现 [destruct]；在一个临时文件中测量，变量处的 [eq_refl] 会被“无法统一”拒绝，往返 [c] 时，而它的第一个组件是 [eq_refl]。- 四个 [Defined]，每个承重，通过在该文件的临时副本中单独闭合 [Qed] 进行测量。[psub_obj] 和 [pquot_obj]：三角形事实需要传输进行简化，并且无论关闭 [Qed]，匹配的三角形事实都会被拒绝（Coq: 无法统一 "projT1 (id_cast (psub_obj (x; h))) t" 与 "t"，以及 [pquot_obj] 双胞）。[psub_adjunction] 和 [pquot_adjunction]：通过 [Build_Adjunction'] 从同态集双射计算余单位和单位，并且无论关闭 [Qed]，匹配三角形事实都会被拒绝（Coq：无法将“t”与“projT1 counit t”以及“projT1 unit t”用于商集统一）。- 直到 [≈]：[psub_counit]，[pquot_unit]（记录约定），[psub_lift_comm]，[pquot_desc_comm]，以及 [PBool_coequalizer_points] 在共等化器的集合同构中。- 命题等价：[psub_universal]，[pquot_universal]，以及 [PBool_equalizer_points]，其“只有当”是叉方程，其“如果”是等化器在 [PPoint] 点选择 [true] 时的泛性质。宇宙，由 [About] 在 [Set Printing Universes] 下读取。- [psub_open@{o}]、[PSub@{o}]、[psub_incl@{o}]、[PQuot@{o}]：空块。[psub_universal]、[psub_lift]、[pquot_universal] 和 [pquot_desc] 仅包含 Instance/Sets.v 的 [setoid_morphism_compose] 的三个 [o <= compose.u*] 上限。[PSub] 和 [PQuot] 在 [PTop@{Set}] 被接受（临时）。- [ex732_Y@{o}] 及其上构建的常量携带 [o <= Subset_projections.u0]，[proj1_sig] 的标准库上限。- 切片常量采用 [@{o so u}]（以及一个用于附加和三角事实的额外宇宙），其中 [o < so] 已声明，并且 [o < u] Construction/Slice.v 的自身严格同构层次下界为 [Program] 辅助宇宙。[Set < so] 继承自 [PTopCat]，并由 [o < so] 推导；[Set < Projections.u0] 由 [so <= Projections.u0] 推导，帽 Construction/Slice.v 的 [Slice] 承载对象宇宙（[projT1] 的）。联接添加了 [Build_Adjunction'] 的 stdlib 帽（[Logic_lemmas.equality]、[prod_rect]、[projections]），而 [pquot_unit] 和 [quotient_LARI] 添加了 [so <= Logic_lemmas.equality.u0]：stdlib [eq_sym] 在该宇宙中获取其类型参数，并在此应用于 [so] 上对象之间的等式，这也是 [LeftAdjointRightInverse] 自身模块在其第二类别的对象宇宙上承载该帽的原因。- [subspace_RARI@{o so u u0}] 的类型是 [∀ X, RightAdjointRightInverse@{so so o u0 u} (Sliced@{so o so o u0 u0 so so} PForget@{o so} X)]，而 [quotient_LARI@{o so u u0}] 的类型是 [∀ X, LeftAdjointRightInverse@{so u0 u so o} (Cosliced@{so o so o u0 u0 so so} PForget@{o so} X)]：两个切片在点的宇宙 [o] 上的同态层，以及两个切片辅助宇宙在一个 [u0] 上，《Structure/SlicedInverse.v》的头部透露了这些信息。- [PTop_HasEqualizers@{o so u u0 u1 u2 u3} : HasEqualizers@{so o} PTopCat@{o so}] 和 [PTop_HasCoequalizers@{o so u u0 u1 u2 u3 u4} : HasCoequalizers@{so o} PTopCat@{o so}]：这些结构存在于类别自身的层次上，它们的模块只在辅助宇宙以下的边界上添加 [<=] 上限和 [o] 严格下界到边界上方。- 在具体空间的见证人保持 [o] 和 [so] 整个过程中：
 [PBool_subspace_RARI@{o so u u0}] 的类型是
 [RightAdjointRightInverse@{so so o u0 u} (Sliced@{so o so o u0 u0
 so so} PForget@{o so} PBool@{o})], [PBool_quotient_LARI@{o so u
 u0}] 的余切对偶；[PBool_equalizer@{o so u u0 u1 u2 u3}] 和
 [PBool_coequalizer@{o so u u0 u1 u2 u3 u4}] 是 [PTop_HasEqualizers] 和 [PTop_HasCoequalizers] 在这些实例上的（余）等化器，每个回读在 [o] 和 [so] 通过显式实例命名它们，以便没有 [About] 块携带两个的第二份副本。[pbool_true@{o}]、[ppoint_false@{o}] 和
 [ppoint_true@{o}] 只携带 [o <= Logic_lemmas.equality.u0]，即 Instance/Sets.v 的 [unit_setoid_object] 和 [bool_setoid_object]。没有宇宙被固定在 [Set]，并且在任何区块中唯一的 [Set] 是上面两个暗示的界限：在这个文件的所有 111 个常量（包括其 [Print Module] 列表和义务）的 [About] 输出之上，[Set < so] 出现在 68 个区块中，[Set < Projections.u0] 出现在 17 个区块中，这 17 个区块中每个也包含 [so <= Projections.u0]；没有区块包含方程。路线和成本。关闭：81 [Category.*] 模块，不包括该文件（[Print Libraries] 在需要该文件的情况下）。在打包之前是45；依次添加 Requires 后，Structure/SlicedInverse.v 成本为12（到57），它的附属文件 Structure/SlicedInverse/Strict.v 再增加1（Theory/Equivalence/Strict.v 已经被需要），Instance/Sets/Coequalizer.v 增加13（到71），以及等化器路径（Structure/Pullback/Reduction.v 与 Instance/Sets/Pullback.v）10（到81）。等化器供体是根据相同列表的测量结果选择的：Adjunction/GAFT/Sets.v 的 [Sets_HasEqualizers] 或 Adjunction/CokernelPair.v 的 [SetsEqualizers] 将给出87，而 Adjunction/Diagonal/Finite.v 的 [DiagSets_HasEqualizers] 给出98。包装只需要 Structure/SlicedInverse.v（57）；其他 24 个模块被 [PTop_HasEqualizers]、[PTop_HasCoequalizers] 及其回读使用，这些模块留在这里，正如 #457 的计划所安排的那样。未发送。FAMILIES映射的初始和最终拓扑以及乘积拓扑（目录maclane:V.9:remark1, #458的），因此没有乘积、完备性或[PTopCat]的余完备性。修正 (#458)：#458提供了它们，基于此文件的构造：Instance/Top/Complete.v 的[PInit]（一个族的初始拓扑，乘积拓扑[PProd]，完备性[PTop_Complete]，以及通过此文件的[PTop_HasEqualizers]的书中的路径[PTop_Complete_via_products]）和Instance/Top/Cocomplete.v 的[PFinal]（最终拓扑，余积[PSigma]，余完备性[PTop_Cocomplete]，以及通过此文件[PTop_HasCoequalizers]的[PTop_Cocomplete_via_coproducts]）；[PInit_one_PSub]和[pfinal_one_map_PQuot]在那里将[PSub]和[PQuot]标识为单映射情况，对开集而言。这里也没有给出：任何对 [PSub] 或 [PQuot] 与类型值构造（Instance/Top/Presheaf.v 的开放子空间、Instance/Top/Pushout.v 的商、Instance/Top/Subspace/TypeValued.v 的 [TQuot]）的比较；这里选择的 [Sets] 等化器与树上 [HasEqualizers Sets] 的其他元素的任何比较；在 [PForget] 重新表述的保持推论（[equalizers_from_sliced_RARI_preserved] 及其对偶）；L 或 M 的唯一性声明；以及没有拓扑非离散的证明者：在 [PBool]，证明者展示了等化器和余等化器所携带的点，并且它们的开集这里没有计算。
*)

#[local] Obligation Tactic := idtac.

(* * ** The subspace (initial) topology along a function / * ** 函数上的子空间（初始）拓扑 *)

Section Subspace.

Universe o.

Context (X : PTop@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S X).

(*
 Mac Lane's predicate: V is open when it is the preimage along [h] of an
 open of X. 

 --------
 Mac Lane 的谓词：当 V 是沿 [h] 的 X 的开集的原像时，V 是开集。
*)
Definition psub_open (V : S → Prop) : Prop :=
  ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s)).

Lemma psub_open_respects (U V : S → Prop) :
  (∀ s, U s <-> V s) → psub_open U → psub_open V.
Proof.
  intros HUV [B [HB HUB]]. exists B; split; [exact HB|].
  intro s; split.
  - intro v; exact (proj1 (HUB s) (proj2 (HUV s) v)).
  - intro b; exact (proj1 (HUV s) (proj2 (HUB s) b)).
Qed.

Lemma psub_open_proper (U : S → Prop) :
  psub_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof.
  intros [B [HB HUB]] s t e u. apply (proj2 (HUB t)).
  exact (popen_proper X B HB (h s) (h t) (proper_morphism h s t e)
           (proj1 (HUB s) u)).
Qed.

(* The union of a family of subspace-opens is the preimage of the union of the family of ALL the opens of X witnessing a member: a Prop-valued family, so no choice of witnesses is made. / 一个子空间开集族的并集是整个 X 的开集族的并集的原像，这个开集族见证了一个成员：一个 Prop 值家族，因此没有对见证者进行选择。 *)
Lemma psub_open_union (F : (S → Prop) → Prop) :
  (∀ V, F V → psub_open V) →
  psub_open (fun s => ex (fun V => F V /\ V s)).
Proof.
  intro HF.
  exists (fun x => ex (fun U => (POpen X U /\
                                 ex (fun V => F V /\ ∀ s, V s <-> U (h s)))
                                /\ U x)).
  split.
  - apply popen_union. intros U [HU _]; exact HU.
  - intro s; split.
    + intros [V [FV v]]. destruct (HF V FV) as [U [HU HVU]].
      exists U. split; [split; [exact HU|]|].
      * exists V; split; [exact FV|exact HVU].
      * exact (proj1 (HVU s) v).
    + intros [U [[_ [V [FV HVU]]] u]].
      exists V; split; [exact FV|exact (proj2 (HVU s) u)].
Qed.

Lemma psub_open_whole : psub_open (fun _ => True).
Proof.
  exists (fun _ => True); split; [exact (popen_whole X)|].
  intro s; exact (iff_refl _).
Qed.

Lemma psub_open_inter (U V : S → Prop) :
  psub_open U → psub_open V → psub_open (fun s => U s /\ V s).
Proof.
  intros [A [HA HUA]] [B [HB HVB]].
  exists (fun x => A x /\ B x); split.
  - exact (popen_inter X A B HA HB).
  - intro s; split.
    + intros [u v]; exact (conj (proj1 (HUA s) u) (proj1 (HVB s) v)).
    + intros [a b]; exact (conj (proj2 (HUA s) a) (proj2 (HVB s) b)).
Qed.

Definition PSub : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := psub_open;
  popen_respects := psub_open_respects;
  popen_proper   := psub_open_proper;
  popen_union    := psub_open_union;
  popen_whole    := psub_open_whole;
  popen_inter    := psub_open_inter
|}.

(* The subspace's points are [S] and its opens are the book's, verbatim. / 子空间的点是 [S]，它的开集和书中的完全相同。 *)
Example PSub_carrier : pt_carrier PSub = S := eq_refl.

Example PSub_open (V : S → Prop) :
  POpen PSub V = ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s))
  := eq_refl.

(* [h] is continuous out of the subspace. / [h] 在子空间之外是连续的。 *)
Lemma psub_incl_cont : @PCont PSub X h.
Proof.
  intros U HU. exists U; split; [exact HU|].
  intro s; exact (iff_refl _).
Qed.

Definition psub_incl : PMor@{o} PSub X :=
  @Build_PMor PSub X h psub_incl_cont.

(*
 The universal property, over ARBITRARY spaces [Z] mapping in: a setoid
 map into the subspace is continuous exactly when its composite with [h]
 is. 

 --------
 在任意空间 [Z] 上的泛性质：映射到一个集合类中，映射到子空间的映射当且仅当其与 [h] 的复合是连续的时才是连续的。
*)
Lemma psub_universal (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z PSub g <-> @PCont Z X (setoid_morphism_compose h g).
Proof.
  split.
  - intros Hg U HU. exact (Hg _ (psub_incl_cont U HU)).
  - intros Hc V [U [HU HVU]].
    apply (popen_respects Z (fun z => U (h (g z)))).
    + intro z; exact (iff_sym (HVU (g z))).
    + exact (Hc U HU).
Qed.

(*
 The book's form: a continuous [f : Z → X] whose underlying function
 factors as [h ∘ g] has [g] continuous into the subspace. 

 --------
 书的形式：一个连续的 [f : Z → X]，其底层函数分解为 [h ∘ g]，[g] 连续映射到子空间。
*)
Definition psub_lift (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  PMor@{o} Z PSub :=
  @Build_PMor Z PSub g
    (proj2 (psub_universal Z g)
       (pcont_respects (pmap f) (setoid_morphism_compose h g) Hfg (pcont f))).

Example psub_lift_map (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  pmap (psub_lift Z f g Hfg) = g := eq_refl.

Lemma psub_lift_comm (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  ∀ z, pmap (pcompose psub_incl (psub_lift Z f g Hfg)) z ≈ pmap f z.
Proof. intro z; symmetry; exact (Hfg z). Qed.

End Subspace.

(* * ** Seven Sketches, Exercise 7.32: the subspace topology on a subset / * ** 七个素描，练习 7.32：子集上的子空间拓扑 *)

Section Ex732.

Universe o.

Context (X : PTop@{o}) (P : X → Prop).

(* The subset [Y ⊆ X], with the equality of [X]. / 子集 [Y ⊆ X]，与 [X] 相等。 *)
Program Definition ex732_Y : SetoidObject@{o o} := {|
  carrier := { x : X | P x };
  is_setoid := {| equiv := fun a b => proj1_sig a ≈ proj1_sig b |}
|}.
Next Obligation.
  constructor.
  - intros a; reflexivity.
  - intros a b H; symmetry; exact H.
  - intros a b c H1 H2; transitivity (proj1_sig b); assumption.
Qed.

Program Definition ex732_incl : SetoidMorphism@{o o o} ex732_Y X := {|
  morphism := fun a => proj1_sig a
|}.
Next Obligation. intros a b H; exact H. Qed.

Definition ex732_Sub : PTop@{o} := PSub X ex732_Y ex732_incl.

(*
 The definition: [A ⊆ Y] is open iff [A = B ∩ Y] for some open [B] of
 [X]. 

 --------
 定义：当且仅当存在 [B] 的某个开集 [X]，使得 [A = B ∩ Y] 时，[A ⊆ Y] 是开的。
*)
Example ex732_def (A : ex732_Y → Prop) :
  POpen ex732_Sub A
  = ex (fun B : X → Prop =>
          POpen X B /\ ∀ y : ex732_Y, A y <-> B (proj1_sig y)) := eq_refl.

(* Part 1: [Y] itself is open, [B] being the whole of [X]. / 第1部分：[Y] 本身是开放的，[B] 是整个 [X] 的全部。 *)
Lemma ex732_part1 :
  POpen X (fun _ => True)
  /\ (∀ y : ex732_Y, True <-> (fun _ : X => True) (proj1_sig y))
  /\ POpen ex732_Sub (fun _ => True).
Proof.
  split; [exact (popen_whole X)|split].
  - intro y; exact (iff_refl _).
  - exists (fun _ => True); split; [exact (popen_whole X)|].
    intro y; exact (iff_refl _).
Qed.

(* Part 2: the three axioms of Seven Sketches' Definition 7.25 -- the whole set, binary intersections, and unions of families indexed by any set [I], here any type at any universe. / 第2部分：七个草图定义7.25的三个公理——整体集合、二元交集，以及由任意集合[I]索引的族的并集，这里的任意类型在任意宇宙中。 *)
Lemma ex732_part2 :
  POpen ex732_Sub (fun _ => True)
  /\ (∀ A B : ex732_Y → Prop, POpen ex732_Sub A → POpen ex732_Sub B →
        POpen ex732_Sub (fun y => A y /\ B y))
  /\ (∀ (I : Type) (A : I → ex732_Y → Prop), (∀ k, POpen ex732_Sub (A k)) →
        POpen ex732_Sub (fun y => ex (fun k => A k y))).
Proof.
  split; [exact (psub_open_whole X ex732_Y ex732_incl)|split].
  - exact (psub_open_inter X ex732_Y ex732_incl).
  - intros I A HA. exact (popen_union_indexed ex732_Sub I A HA).
Qed.

(* Part 3: the inclusion is continuous. / 第3部分：包含是连续的。 *)
Lemma ex732_part3 : @PCont ex732_Sub X ex732_incl.
Proof. exact (psub_incl_cont X ex732_Y ex732_incl). Qed.

Definition ex732_incl_mor : PMor@{o} ex732_Sub X :=
  psub_incl X ex732_Y ex732_incl.

End Ex732.

(* * ** The quotient (final) topology along a function / * ** 沿函数的商（最终）拓扑 *)

Section Quotient.

Universe o.

Context (X : PTop@{o}) (T : SetoidObject@{o o})
        (q : SetoidMorphism@{o o o} X T).

(* Mac Lane's predicate, V open when its preimage along [q] is, together with the setoid bookkeeping: V respects the equality of [T]. / 当其沿着 [q] 的逆像开放时，Mac Lane 的谓词 V，以及集合类簿记：V 尊重 [T] 的等式。 *)
Definition pquot_open (V : T → Prop) : Prop :=
  (∀ t t' : T, t ≈ t' → V t → V t') /\ POpen X (fun x => V (q x)).

Lemma pquot_open_respects (U V : T → Prop) :
  (∀ t, U t <-> V t) → pquot_open U → pquot_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros t t' e v. apply (proj1 (H t')), (Hp t t' e), (proj2 (H t)), v.
  - exact (popen_respects X _ _ (fun x => H (q x)) Ho).
Qed.

Lemma pquot_open_proper (U : T → Prop) :
  pquot_open U → ∀ t t' : T, t ≈ t' → U t → U t'.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma pquot_open_union (F : (T → Prop) → Prop) :
  (∀ V, F V → pquot_open V) →
  pquot_open (fun t => ex (fun V => F V /\ V t)).
Proof.
  intro HF; split.
  - intros t t' e [V [FV v]]. exists V; split; [exact FV|].
    exact (proj1 (HF V FV) t t' e v).
  - apply (popen_respects X
             (fun x => ex (fun U => ex (fun V => F V /\
                                          ∀ y, U y <-> V (q y)) /\ U x))).
    + intro x; split.
      * intros [U [[V [FV HUV]] u]]. exists V.
        split; [exact FV|exact (proj1 (HUV x) u)].
      * intros [V [FV v]]. exists (fun y => V (q y)).
        split; [|exact v]. exists V; split; [exact FV|].
        intro y; exact (iff_refl _).
    + apply popen_union. intros U [V [FV HUV]].
      apply (popen_respects X (fun y => V (q y))).
      * intro y; exact (iff_sym (HUV y)).
      * exact (proj2 (HF V FV)).
Qed.

Lemma pquot_open_whole : pquot_open (fun _ => True).
Proof. split; [intros; exact I|exact (popen_whole X)]. Qed.

Lemma pquot_open_inter (U V : T → Prop) :
  pquot_open U → pquot_open V → pquot_open (fun t => U t /\ V t).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros t t' e [u v]; exact (conj (HpU t t' e u) (HpV t t' e v)).
  - exact (popen_inter X _ _ HoU HoV).
Qed.

Definition PQuot : PTop@{o} := {|
  pt_carrier     := T;
  POpen          := pquot_open;
  popen_respects := pquot_open_respects;
  popen_proper   := pquot_open_proper;
  popen_union    := pquot_open_union;
  popen_whole    := pquot_open_whole;
  popen_inter    := pquot_open_inter
|}.

Example PQuot_carrier : pt_carrier PQuot = T := eq_refl.

Example PQuot_open (V : T → Prop) :
  POpen PQuot V
  = ((∀ t t' : T, t ≈ t' → V t → V t') /\ POpen X (fun x => V (q x)))
  := eq_refl.

Lemma pquot_proj_cont : @PCont X PQuot q.
Proof. intros V HV; exact (proj2 HV). Qed.

Definition pquot_proj : PMor@{o} X PQuot :=
  @Build_PMor X PQuot q pquot_proj_cont.

(*
 The universal property, over ARBITRARY spaces [Z] mapping out: a setoid
 map out of the quotient is continuous exactly when its composite with
 [q] is. 

 --------
 泛性质，对于任意空间 [Z] 的映射：当它与 [q] 复合时，商的映射恰好是连续的。
*)
Lemma pquot_universal (Z : PTop@{o}) (k : SetoidMorphism@{o o o} T Z) :
  @PCont PQuot Z k <-> @PCont X Z (setoid_morphism_compose k q).
Proof.
  split.
  - intros Hk W HW. exact (proj2 (Hk W HW)).
  - intros Hc W HW; split.
    + intros t t' e w.
      exact (popen_proper Z W HW (k t) (k t') (proper_morphism k t t' e) w).
    + exact (Hc W HW).
Qed.

(* The book's form: a continuous [f : X → Z] whose underlying function factors as [k ∘ q] has [k] continuous out of the quotient. / 书的形式：一个连续的 [f : X → Z]，其底层函数分解为 [k ∘ q]，[k] 能从商中连续出来。 *)
Definition pquot_desc (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  PMor@{o} PQuot Z :=
  @Build_PMor PQuot Z k
    (proj2 (pquot_universal Z k)
       (pcont_respects (pmap f) (setoid_morphism_compose k q) Hfk (pcont f))).

Example pquot_desc_map (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  pmap (pquot_desc Z f k Hfk) = k := eq_refl.

Lemma pquot_desc_comm (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  ∀ x, pmap (pcompose (pquot_desc Z f k Hfk) pquot_proj) x ≈ pmap f x.
Proof. intro x; symmetry; exact (Hfk x). Qed.

End Quotient.

(* * ** The sliced forgetful functors and the sliced adjunctions / * ** 切片的遗忘函子和切片的伴随 *)

Section SliceAdjunctions.

Universes o so.
Constraint o < so.

Context (X : PTop@{o}).

Local Notation PT := PTopCat@{o so}.
Local Notation G := PForget@{o so}.

(*
 The forgetful functor sliced over [X], Mac Lane's [G ↓ X]: the generic
 [Sliced] of Structure/SlicedInverse.v at [PForget], under a local name.
 It is an alias, not a second functor, so the adjunction below is at
 once an adjunction of [Sliced G X] and Proposition 1 consumes it. 

 --------
 遗忘函子在  [X] 上切片，Mac Lane 的  [G ↓ X]：Structure/SlicedInverse.v 在  [PForget] 处的通用 [Sliced] ，在本地名称下。它是一个别名，而不是第二个函子，因此下面的伴随关系同时是 [Sliced G X] 的伴随关系，并且命题 1 已经使用了它。
*)
Definition PForget_over : @Slice PT X ⟶ @Slice Sets@{o so} (G X) :=
  Sliced G X.

(*
 The forgetful functor sliced under [X], Mac Lane's [X ↓ G]: the generic
 [Cosliced] at [PForget]. 

 --------
 在  [X] 下切的遗忘函子，Mac Lane 的  [X ↓ G] ：在  [PForget] 的通用  [Cosliced] 。
*)
Definition PForget_under : @Coslice PT X ⟶ @Coslice Sets@{o so} (G X) :=
  Cosliced G X.

Example PForget_over_Sliced : PForget_over = Sliced G X := eq_refl.

Example PForget_under_Cosliced : PForget_under = Cosliced G X := eq_refl.

(*
 Mac Lane's [L]: the subspace along each function into the points of
 [X]. 

 --------
 Mac Lane 的 [L]：沿每个函数到 [X] 点的子空间。
*)
Program Definition PSub_Functor :
  @Slice Sets@{o so} (G X) ⟶ @Slice PT X := {|
  fobj := fun c => (PSub X (`1 c) (`2 c); psub_incl X (`1 c) (`2 c));
  fmap := fun c d m => ({| pmap := `1 m; pcont := _ |}; _)
|}.
Next Obligation.
  intros [S h] [S' h'] [m Hm]; simpl in *.
  apply (proj2 (psub_universal X S' h' (PSub X S h) m)).
  apply (@pcont_respects (PSub X S h) X h);
    [intro s; symmetry; exact (Hm s)|].
  exact (psub_incl_cont X S h).
Qed.
Next Obligation. intros [S h] [S' h'] [m Hm] s; simpl in *. exact (Hm s). Qed.
Next Obligation. intros c d m n H s; simpl in *. exact (H s). Qed.
Next Obligation. intros c s; simpl. reflexivity. Qed.
Next Obligation. intros c d e m n s; simpl. reflexivity. Qed.

Example PSub_Functor_obj (c : @Slice Sets@{o so} (G X)) :
  `1 (PSub_Functor c) = PSub X (`1 c) (`2 c) := eq_refl.

(*
 The hom-set bijection of [G ↓ X ⊣ L]: a map over [X] into the subspace
 IS its underlying map, continuity coming from [psub_universal]. 

 --------
 [G ↓ X ⊣ L] 的同态集合双射：一个映射到子空间的 [X] 上的映射就是它的底层映射，其连续性来自 [psub_universal]。
*)
Program Definition psub_adj_iso (x : @Slice PT X)
  (y : @Slice Sets@{o so} (G X)) :
  @Isomorphism Sets
    {| carrier := @hom (@Slice Sets@{o so} (G X)) (PForget_over x) y
     ; is_setoid := @homset (@Slice Sets@{o so} (G X)) (PForget_over x) y |}
    {| carrier := @hom (@Slice PT X) x (PSub_Functor y)
     ; is_setoid := @homset (@Slice PT X) x (PSub_Functor y) |} := {|
  to   := {| morphism := fun k => ({| pmap := `1 k; pcont := _ |}; _) |};
  from := {| morphism := fun k => (pmap (`1 k); _) |}
|}.
Next Obligation.
  intros [Y g] [S h] [k Hk]; simpl in *.
  apply (proj2 (psub_universal X S h Y k)).
  apply (pcont_respects (pmap g)); [intro z; symmetry; exact (Hk z)|].
  exact (pcont g).
Qed.
Next Obligation. intros [Y g] [S h] [k Hk] z; simpl in *. exact (Hk z). Qed.
Next Obligation. intros x y k k' H z; simpl in *. exact (H z). Qed.
Next Obligation. intros [Y g] [S h] [k Hk] z; simpl in *. exact (Hk z). Qed.
Next Obligation. intros x y k k' H z; simpl in *. exact (H z). Qed.
Next Obligation. intros x y k z; simpl. reflexivity. Qed.
Next Obligation. intros x y k z; simpl. reflexivity. Qed.

(* Both transposes are the identity on underlying maps. / 两个转置在底层映射上都是恒等映射。 *)
Example psub_adj_to_map (x : @Slice PT X) (y : @Slice Sets@{o so} (G X))
  (k : PForget_over x ~{@Slice Sets@{o so} (G X)}~> y) :
  pmap (`1 (to (psub_adj_iso x y) k)) = `1 k := eq_refl.

Example psub_adj_from_map (x : @Slice PT X) (y : @Slice Sets@{o so} (G X))
  (k : x ~{@Slice PT X}~> PSub_Functor y) :
  `1 (from (psub_adj_iso x y) k) = pmap (`1 k) := eq_refl.

Definition psub_adjunction : PForget_over ⊣ PSub_Functor.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PForget_over PSub_Functor
                     psub_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(*
 [(G ↓ X) ∘ L = Id] on objects: Leibniz, after destructing the pair;
 [Defined], so that the [id_cast] below reduces. 

 --------
 [(G ↓ X) ∘ L = Id] 对象上：莱布尼茨，在破坏对之后；
 [Defined]，因此下面的 [id_cast] 简化。
*)
Lemma psub_obj (c : @Slice Sets@{o so} (G X)) :
  PForget_over (PSub_Functor c) = c.
Proof. destruct c; reflexivity. Defined.

Example psub_obj_pair (S : SetoidObject@{o o})
  (h : S ~{Sets@{o so}}~> G X) :
  PForget_over (PSub_Functor (S; h)) = (S; h) := eq_refl.

(* The counit is the identity, transported along [psub_obj]. / 余单位是沿着 [psub_obj] 传输的恒等映射。 *)
Lemma psub_counit (c : @Slice Sets@{o so} (G X)) :
  @counit _ _ _ _ psub_adjunction c ≈ id_cast (psub_obj c).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

(* Mac Lane's [M]: the quotient along each function out of the points of [X]. / Mac Lane 的 [M]：沿着 [X] 点的每个函数的商。 *)
Program Definition PQuot_Functor :
  @Coslice Sets@{o so} (G X) ⟶ @Coslice PT X := {|
  fobj := fun c => (PQuot X (`1 c) (`2 c); pquot_proj X (`1 c) (`2 c));
  fmap := fun c d m => ({| pmap := `1 m; pcont := _ |}; _)
|}.
Next Obligation.
  intros [T q] [T' q'] [m Hm]; simpl in *.
  apply (proj2 (pquot_universal X T q (PQuot X T' q') m)).
  apply (@pcont_respects X (PQuot X T' q') q'); [exact Hm|].
  exact (pquot_proj_cont X T' q').
Qed.
Next Obligation. intros [T q] [T' q'] [m Hm] x; simpl in *. exact (Hm x). Qed.
Next Obligation. intros c d m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros c t; simpl. reflexivity. Qed.
Next Obligation. intros c d e m n t; simpl. reflexivity. Qed.

Example PQuot_Functor_obj (c : @Coslice Sets@{o so} (G X)) :
  `1 (PQuot_Functor c) = PQuot X (`1 c) (`2 c) := eq_refl.

(* The hom-set bijection of [M ⊣ X ↓ G]: a map under [X] out of the quotient IS its underlying map, continuity coming from [pquot_universal]. / [M ⊣ X ↓ G] 的同态集双射：在 [X] 下的一个映射，从商映射出发本身就是它的基础映射，连续性来自 [pquot_universal] 。 *)
Program Definition pquot_adj_iso (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice PT X) (PQuot_Functor x) y
     ; is_setoid := @homset (@Coslice PT X) (PQuot_Functor x) y |}
    {| carrier := @hom (@Coslice Sets@{o so} (G X)) x (PForget_under y)
     ; is_setoid := @homset (@Coslice Sets@{o so} (G X)) x
                      (PForget_under y) |} := {|
  to   := {| morphism := fun k => (pmap (`1 k); _) |};
  from := {| morphism := fun k => ({| pmap := `1 k; pcont := _ |}; _) |}
|}.
Next Obligation. intros [T q] [Y f] [k Hk] x; simpl in *. exact (Hk x). Qed.
Next Obligation. intros x y k k' H t; simpl in *. exact (H t). Qed.
Next Obligation.
  intros [T q] [Y f] [k Hk]; simpl in *.
  apply (proj2 (pquot_universal X T q Y k)).
  apply (pcont_respects (pmap f)); [exact Hk|].
  exact (pcont f).
Qed.
Next Obligation. intros [T q] [Y f] [k Hk] x; simpl in *. exact (Hk x). Qed.
Next Obligation. intros x y k k' H t; simpl in *. exact (H t). Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.

Example pquot_adj_to_map (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X) (k : PQuot_Functor x ~{@Coslice PT X}~> y) :
  `1 (to (pquot_adj_iso x y) k) = pmap (`1 k) := eq_refl.

Example pquot_adj_from_map (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X)
  (k : x ~{@Coslice Sets@{o so} (G X)}~> PForget_under y) :
  pmap (`1 (from (pquot_adj_iso x y) k)) = `1 k := eq_refl.

Definition pquot_adjunction : PQuot_Functor ⊣ PForget_under.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PQuot_Functor PForget_under
                     pquot_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* [(X ↓ G) ∘ M = Id] on objects. / [(X ↓ G) ∘ M = Id] 在物体上。 *)
Lemma pquot_obj (c : @Coslice Sets@{o so} (G X)) :
  PForget_under (PQuot_Functor c) = c.
Proof. destruct c; reflexivity. Defined.

Example pquot_obj_pair (T : SetoidObject@{o o})
  (q : G X ~{Sets@{o so}}~> T) :
  PForget_under (PQuot_Functor (T; q)) = (T; q) := eq_refl.

(* The unit is the identity, transported along [pquot_obj]. / 该单位是单位元，沿着 [pquot_obj] 运输。 *)
Lemma pquot_unit (c : @Coslice Sets@{o so} (G X)) :
  @unit _ _ _ _ pquot_adjunction c ≈ id_cast (eq_sym (pquot_obj c)).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

(*
 The subspace construction packaged: [L] is a right-adjoint-right-inverse
 of [G ↓ X], in Structure/SlicedInverse.v's record, which is what
 Proposition 1 consumes. 

 --------
 子空间构造打包：[L] 是 [G ↓ X] 在 Structure/SlicedInverse.v 的记录中的右伴侣右逆，这正是命题 1 所使用的。
*)
Definition subspace_RARI : RightAdjointRightInverse (Sliced G X) := {|
  rari_right  := PSub_Functor;
  rari_adj    := psub_adjunction;
  rari_obj    := psub_obj;
  rari_counit := psub_counit
|}.

Example subspace_RARI_right : rari_right subspace_RARI = PSub_Functor :=
  eq_refl.

(*
 The quotient construction packaged: [M] is a left-adjoint-right-inverse
 of [X ↓ G], in Theory/Equivalence/Strict.v's record, which is what the
 dual of Proposition 1 consumes. 

 --------
 商构造打包：[M] 是 [X ↓ G] 的左伴随右逆，在 Theory/Equivalence/Strict.v 的记录中，这正是命题 1 的对偶所使用的。
*)
Definition quotient_LARI : LeftAdjointRightInverse (Cosliced G X) := {|
  lari_left := PQuot_Functor;
  lari_adj  := pquot_adjunction;
  lari_obj  := pquot_obj;
  lari_unit := pquot_unit
|}.

Example quotient_LARI_left : lari_left quotient_LARI = PQuot_Functor :=
  eq_refl.

End SliceAdjunctions.

(* * ** Equalizers and coequalizers of spaces, by Proposition 1 and its dual / * ** 空间的等化子和共同等化子，由命题1及其对偶 *)

(*
 The downstairs equalizers: Structure/Pullback/Reduction.v's
 [HasEqualizers_of_HasPullbacks_Terminal] fed Instance/Sets/Pullback.v's
 [Sets_HasPullbacks] and Instance/Sets.v's [Sets_Terminal], the term of
 Adjunction/CokernelPair.v's [SetsEqualizers], written out here because
 requiring that file costs more (see the header). 

 --------
 楼下的等化器：Structure/Pullback/Reduction.v 的
 [HasEqualizers_of_HasPullbacks_Terminal]  提供了 Instance/Sets/Pullback.v 的
 [Sets_HasPullbacks]  以及 Instance/Sets.v 的  [Sets_Terminal] ，Adjunction/CokernelPair.v 的项 [SetsEqualizers] 在这里写出，因为
 需要该文件会更耗费资源（见头部说明）。
*)
#[local] Notation SetsEq :=
  (@HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
     Sets_HasPullbacks).

(* Mac Lane's Proposition 1 at [PForget]: the equalizer of two continuous maps is the subspace on their equalizer in [Sets]. / Mac Lane 在 [PForget] 的命题 1：两个连续映射的等化子是在 [Sets] 中它们等化子的子空间。 *)
Definition PTop_HasEqualizers@{o so + | o < so +} :
  @HasEqualizers PTopCat@{o so} :=
  @equalizers_from_sliced_RARI _ _ PForget@{o so} PForget_Faithful SetsEq
    subspace_RARI.

Example PTop_equalizer_obj@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = PSub x (`1 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g))))
  := eq_refl.

Example PTop_equalizer_arrow@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@equalizer _ PTop_HasEqualizers x y f g))
    = psub_incl x
        (`1 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g))))
  := eq_refl.

(*
 The dual of Proposition 1 at [PForget], over Instance/Sets/Coequalizer.v's
 [Sets_HasCoequalizers]: the coequalizer of two continuous maps is the
 quotient topology on their coequalizer in [Sets], the quotient of the
 codomain's points by the equivalence the pair generates. 

 --------
 命题 1 在 [PForget] 上的对偶，关于 Instance/Sets/Coequalizer.v 的 [Sets_HasCoequalizers]：两个连续映射的余等化子是它们在 [Sets] 中余等化的商拓扑，即通过该对生成的等价关系对上同域的点进行商化。
*)
Definition PTop_HasCoequalizers@{o so + | o < so +} :
  @HasCoequalizers PTopCat@{o so} :=
  @coequalizers_from_sliced_LARI _ _ PForget@{o so} PForget_Faithful
    Sets_HasCoequalizers quotient_LARI.

Example PTop_coequalizer_obj@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@coeq _ PTop_HasCoequalizers x y f g)
    = PQuot y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

Example PTop_coequalizer_arrow@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@coeq _ PTop_HasCoequalizers x y f g))
    = pquot_proj y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

(* * ** Applied at concrete spaces: an equalizer and a coequalizer of two different maps / * ** 应用于具体范畴：两个不同映射的等化器与共等化器 *)

(* The two constructions at the concrete two-point space [PBool] of Instance/Top/Prop.v, which the two witnesses below consume. / 位于 Instance/Top/Prop.v 的混凝土双点空间 [PBool] 的两个构造，下面的两个证人使用它们。 *)
Definition PBool_subspace_RARI@{o so +| o < so +} :
  RightAdjointRightInverse (Sliced PForget@{o so} PBool@{o}) :=
  subspace_RARI PBool.

Definition PBool_quotient_LARI@{o so +| o < so +} :
  LeftAdjointRightInverse (Cosliced PForget@{o so} PBool@{o}) :=
  quotient_LARI PBool.

(*
 The constant map at [true] on [PBool]; it differs from the identity, at
 [false]. 

 --------
 在 [PBool] 上的 [true] 处的恒定映射；它在 [false] 处不同于恒等映射。
*)
Definition pbool_true@{o} : PMor@{o} PBool PBool :=
  pdisc_mor bool_setoid_object PBool (pconst bool_setoid_object PBool true).

Lemma pbool_maps_differ@{o so | o < so +} :
  pid PBool ≈[PTopCat@{o so}] pbool_true → False.
Proof. intro H; specialize (H false); simpl in H; discriminate H. Qed.

(*
 Proposition 1 at the pair (identity, constant [true]) on [PBool]: the
 subspace of [PBool] on the [Sets] equalizer of the underlying maps,
 which is the value of [rari_right PBool_subspace_RARI] there. 

 --------
 命题 1 关于对 (identity, constant  [true]) 在  [PBool] 上：[PBool] 在基础映射的 [Sets] 等化器上的子空间，这就是 [rari_right PBool_subspace_RARI] 在那里的取值。
*)
Definition PBool_equalizer@{o so +| o < so +} :=
  @equalizer PTopCat@{o so} PTop_HasEqualizers PBool PBool (pid PBool)
    pbool_true.

Example PBool_equalizer_obj@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = PSub PBool
        (`1 (@equalizer _ SetsEq _ _ setoid_morphism_id
               (pconst bool_setoid_object PBool true)))
        (`1 (`2 (@equalizer _ SetsEq _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true)))) := eq_refl.

Example PBool_equalizer_rari@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = `1 (rari_right PBool_subspace_RARI@{o so _ _}
            (`1 (@equalizer _ SetsEq _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true));
             `1 (`2 (@equalizer _ SetsEq _ _ setoid_morphism_id
                       (pconst bool_setoid_object PBool true))))) := eq_refl.

(*
 Which points of [PBool] lie in the equalizer: exactly [true], so the
 equalizer is a proper, nonempty subspace.  The "only if" is the fork
 equation, the "if" the universal property at the point picking
 [true]. 

 --------
 [PBool] 的哪些点位于等化器中：正好是 [true]，因此等化器是一个适当的、非空子空间。“只有当”是叉方程，“如果”是在选择点 [true] 时的普适性。
*)
Lemma PBool_equalizer_points@{o so +| o < so +} (b : bool) :
  ex (fun e : pt_carrier (`1 PBool_equalizer@{o so _ _ _ _ _}) =>
        pmap (`1 (`2 PBool_equalizer@{o so _ _ _ _ _})) e = b)
  <-> b = true.
Proof.
  split.
  - intros [e He]. pose proof (fork_eq (`2 (`2 PBool_equalizer)) e) as F.
    simpl in F. rewrite <- He. exact F.
  - intros ->.
    pose (t := pdisc_mor unit_setoid_object PBool (pconst _ PBool true)
               : PPoint ~{PTopCat@{o so}}~> PBool).
    destruct (eq_desc (`2 (`2 PBool_equalizer@{o so _ _ _ _ _})) t
                (fun _ => eq_refl)) as [u Hu _].
    exists (pmap u ttt). exact (Hu ttt).
Qed.

(* The two points of [PBool], as maps out of the one-point space; they differ. / [PBool] 的两点，作为来自单点空间的映射；它们不同。 *)
Definition ppoint_false@{o} : PMor@{o} PPoint PBool :=
  pdisc_mor unit_setoid_object PBool (pconst unit_setoid_object PBool false).

Definition ppoint_true@{o} : PMor@{o} PPoint PBool :=
  pdisc_mor unit_setoid_object PBool (pconst unit_setoid_object PBool true).

Lemma ppoint_maps_differ@{o so | o < so +} :
  ppoint_false ≈[PTopCat@{o so}] ppoint_true → False.
Proof. intro H; specialize (H ttt); simpl in H; discriminate H. Qed.

(*
 The dual of Proposition 1 at the pair ([false], [true]) out of the
 point: the quotient topology on the [Sets] coequalizer of the
 underlying maps, which is the value of [lari_left PBool_quotient_LARI]
 there. 

 --------
 命题1在对 ([false], [true]) 的对偶远离该点：底层映射的 [Sets] 协同等化子的商拓扑，这是 [lari_left PBool_quotient_LARI] 在该处的取值。
*)
Definition PBool_coequalizer@{o so +| o < so +} :=
  @coeq PTopCat@{o so} PTop_HasCoequalizers PPoint PBool ppoint_false
    ppoint_true.

Example PBool_coequalizer_obj@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = PQuot PBool
        (SetsCoeq (pconst unit_setoid_object PBool false)
                  (pconst unit_setoid_object PBool true))
        (sets_coeq_proj (pconst unit_setoid_object PBool false)
                        (pconst unit_setoid_object PBool true)) := eq_refl.

Example PBool_coequalizer_lari@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = `1 (lari_left PBool_quotient_LARI@{o so _ _}
            (SetsCoeq (pconst unit_setoid_object PBool false)
                      (pconst unit_setoid_object PBool true);
             sets_coeq_proj (pconst unit_setoid_object PBool false)
                            (pconst unit_setoid_object PBool true)))
  := eq_refl.

(* In the coequalizer every point is identified with [true], so the two points [PBool] separates ([PBool_points_distinct]) are glued: a proper quotient, to one point up to its equality. / 在共同余化子中，每个点都与 [true] 识别，因此两个由 [PBool] 分开的点 ([PBool_points_distinct]) 被粘合：一个适当的商，直到其相等为止到一个点。 *)
Lemma PBool_coequalizer_points@{o so +| o < so +} (b : bool) :
  @equiv _ (`1 PBool_coequalizer@{o so _ _ _ _ _ _}) b true.
Proof.
  destruct b.
  - apply cq_base. reflexivity.
  - exact (cq_glue (pconst unit_setoid_object PBool false)
                   (pconst unit_setoid_object PBool true) ttt).
Qed.
