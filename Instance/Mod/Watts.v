(*
   * * Watts' theorem through SAFT: Mac Lane's contravariant text form and
   Exercise 3's covariant form 

   --------
   * * 通过 SAFT 的 Watts 定理：Mac Lane 的逆变文本形式和习题 3 的协变形式
*)

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
 ed. (GTM 5), §V.8, printed pp. 131–132 (PDF pp. 140–141),
 ledger items `maclane:V.8:thm-watt` and `maclane:V.8:ex3`
 (issue #454), read from the printed page.  The text, p. 131:
 "Watt's Theorem [1960] is another example.  Any ring R is a
 generator in the category R-Mod, hence a cogenerator in
 (R-Mod)^op.  It follows that any contravariant additive
 functor T on R-Mod to Ab which takes small colimits to
 limits is representable by a group isomorphism
 T ≅ hom_R(−, C) for some R-module C."  Exercise 3, p. 132:
 "Use Exercise 2(b) and the special adjoint functor theorem
 to prove that any continuous additive functor T: R-Mod → Ab
 is representable. (Watt's theorem)."  The book spells the
 name "Watt's"; the author is Charles E. Watts.  (The in-repo
 catalogue, doc/plan/books/maclane/inventory/V.json,
 summarises both in its own words; the quotations here are
 the printed page's.)
 Papers:    C. E. Watts, "Intrinsic characterizations of some additive
 functors", Proc. Amer. Math. Soc. 11 (1960), 5–8; and
 S. Eilenberg, "Abstract description of some basic
 functors", J. Indian Math. Soc. (N.S.) 24 (1960), 231–234 —
 the two original articles, as the nLab page lists them.
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 nLab:      https://ncatlab.org/nlab/show/cogenerator
 nLab:      https://ncatlab.org/nlab/show/injective+object
 The nLab page "injective cogenerator" does not exist (HTTP
 404, measured with curl on 2026-09-24, as
 Instance/Mod/Cogenerator.v also records).

 PATH.  The issue suggests Instance/Module/Watts.v.  The tree keeps its
 module files under Instance/Mod/ (#258, #401, #449), so this file is
 Instance/Mod/Watts.v: a deviation in path only.

 THIS FILE AND THE UNCONDITIONAL THEOREM.  For the text form this file
 is strictly weaker than Instance/Mod/Watts/Unconditional.v's
 [watts_theorem_unconditional], which proves the book's contravariant
 statement with no hypothesis beyond the book's own two (and
 [Set < c]), through GAFT and an explicit solution set; that file is
 #454's headline for the text form.  This one is kept because it is
 Mac Lane's SAFT route, which the issue's Reviewer line names ("the
 representability must be derived from SAFT plus additivity"), and
 because Exercise 3, the covariant form, is delivered only here, and
 conditionally.  It imports the unconditional file, and section 6
 measures the relation in tree: [watts_theorem_via_unconditional]
 derives [watts_theorem]'s statement from [watts_theorem_unconditional],
 with [Untruncate] carried and not consumed, and
 [watts_unconditional_coext] and [watts_unconditional_coext_2a] are the
 text-form witness of section 4 without [Untruncate].  Which of this
 file's constants the unconditional theorem subsumes, and which not, is
 listed in that file's header, THE HEADLINE, AND THE SAFT ROUTE.

 ** BACKGROUND

 Watts and Eilenberg showed, independently and in the same year, that
 the functors between module categories which respect colimits are the
 tensor functors: an additive, cocontinuous F : Mod_R → Mod_S is
 naturally isomorphic to − ⊗_R N, where N is F(R) and R acts on it by F
 applied to left multiplications (the nLab page's statement and its
 first Remark).  The reason is that R generates R-Mod: every module is a
 quotient of a free one, a coproduct of copies of R, so a functor that
 respects colimits is fixed by its value at R and by the action of R's
 endomorphisms there.  The nLab page records generalisations to right
 exact functors (Nyman and Smith), to homotopical and higher algebra
 (Hovey; Lurie) and to categories enriched in a bicategory (Arkor and
 McDermott).  Mac Lane gives the result as an application of the
 special adjoint functor theorem and states the dual reading: a
 CONTRAVARIANT additive functor that turns colimits into limits is a
 hom functor hom_R(−, C).  Exercise 3 asks for the covariant analogue,
 a continuous additive T : R-Mod → Ab is hom_R(A, −), which needs a
 cogenerator of R-Mod and so Exercise 2(b).

 ** THE BOOK'S PROOF, AND THE ONE HERE

 Mac Lane's sketch: "by the special adjoint functor theorem T:
 (R-Mod)^op → Ab has a left adjoint F; since T is additive, the
 adjunction Ab(G, TA) ≅ hom_R(A, FG), G ∈ Ab, A ∈ R-Mod, is an
 isomorphism of additive groups; set G = Z to get
 TA ≅ Ab(Z, TA) ≅ hom_R(A, FZ)", so C = Fℤ.  The first step is
 [watts_theorem_adjoint] below, verbatim; the last is section 5's
 [ab_hom_Z_iso], Ab(ℤ, X) ≅ X natural in X as Ab-valued functors, with
 ℤ read as the free abelian group on one point [FreeAb SetsOne], and
 [watts_theorem_Fz], the representing object ≅ F(ℤ) in RMod R.  (The
 isomorphism Ab(ℤ, X) ≅ X is the additive upgrade at Id[Ab] of the
 representation [free_ab_adjunction] gives, and the comparison of
 representing objects does not even need it.  Still open: no
 isomorphism of the free group on one point with Instance/Ab/Free.v's
 [ab_int] is built, the comparison Instance/Ab/Generator.v records as
 left undone for [FreeAbObject unit_setoid_object]; [SetsOne] is
 Construction/Elements.v's name for the terminal object of [Sets].)
 The representation itself is obtained the way the issue's Reviewer
 line asks, "derived from SAFT plus additivity", through Yoneda:

 SAFT.  Adjunction/SAFT/Characterization/Corollaries.v's
 [continuous_Set_functor_representable] — Mac Lane's Corollary on
 book p. 130, built on #453's [SAFT_wellpowered] — represents the
 Sets-valued functor [Ab_Forget ◯ T]; its representing object is the
 left adjoint of [Ab_Forget ◯ T] at the one-point set.
 ADDITIVITY.  Functor/Representable/Additive.v's [watt_ab_repr]
 upgrades a representation of [Ab_Forget ◯ T], for T additive, to an
 isomorphism [HomAb A ≅ T] in the functor category into [Ab], with
 the SAME components.

 For the text form the SAFT is applied at C := (RMod R)^op: complete
 because RMod R is cocomplete, cogenerated by R, and well-powered because
 RMod R is co-well-powered.  For Exercise 3 it is applied at
 C := RMod R: complete, well-powered, with a cogenerator supplied.

 ** CONSUMED, NOT BUILT

 - Adjunction/SAFT/Characterization.v's [SAFT_wellpowered] and its
 satellite Corollaries.v's [continuous_Set_functor_representable]
 (#453).
 - Instance/Mod/Colimit.v's [RMod_Cocomplete_via_GAFT], read as
 completeness of (RMod R)^op by Construction/Product/Limit.v's
 [Complete_op_of_Cocomplete]; Instance/Mod/Limit.v's
 [RMod_Complete] and [RMod_Forget_Ab_creates_continuous] (#449).
 - Instance/Mod/WellPowered.v's [RModop_Cogenerator] (R as a
 generator of RMod R, read as a cogenerator of the opposite),
 [RMod_CoWellPowered_untruncate] and [RMod_WellPowered_untruncate].
 - Functor/Representable/Additive.v's [HomAb], [CoHomAb],
 [CoHomAb_continuous], [LocallyPropositional_op], [watt_ab_repr],
 [watt_ab_iso] and [wab_obj].
 - Construction/Comma/Limit.v's [PreservesImageLimit] with
 Construction/Comma/Creation.v's [PreservesImageLimit_Continuous]
 and [Continuous_PreservesImageLimit]; Structure/Limit/
 Preservation.v's [continuous_compose] and [cone_assoc_inv];
 Instance/Ab/Limit.v's [Ab_Forget_creates_continuous] and
 [Ab_Forget_reflects_limits]; Functor/Hom/Continuous.v's
 [representable_iso_ContinuousFunctor]; Instance/Fun.v's
 [iso_equiv] and [equiv_iso].
 - Instance/Mod/Cogenerator.v's [QZ_injective_cogenerator],
 [QZ_family_cogenerates], [QZ_Cogenerator] and [coext_cogenerator]
 (Exercise 2(b)); Instance/Mod/Coextension.v's [coex_adjunction] and
 [CoextObj]; Instance/Mod/HomTensor.v's [HomZL] and
 [homzl_coext_iso] (Exercise 2(a) at B := R).
 - Adjunction/Continuity.v's [right_adjoint_Continuous] with
 Adjunction/Opposite.v's [Opposite_Adjunction];
 Instance/Mod/Representable.v's [rmod_representable];
 Functor/Representable.v's [repr_induced_iso] and
 [repr_unique_iso]; Construction/Opposite.v's
 [Isomorphism_Opposite]; Instance/Sets/Classifier/OneLevel.v's
 [Untruncate].
 - For section 5: Instance/Ab/Free.v's [FreeAb] and
 [free_ab_adjunction]; Adjunction/Representability/Sets.v's
 [representable_of_left_adjoint] and [Representable_transport];
 Adjunction/Compose.v's [Adjunction_Compose];
 Construction/Elements.v's [SetsOne]; Structure/AbCategory.v's
 [Id_AdditiveFunctor].
 - For section 6: Instance/Mod/Watts/Unconditional.v's
 [watts_theorem_unconditional] and
 [RModop_continuous_representable].

 ** WHAT IS BUILT

 (1) [RMod_Forget_Ab_additive]: the forgetful functor is additive, at
 [reflexivity].  The continuity of the Ab-valued hom functors,
 [HomAb_continuous] and [CoHomAb_continuous], is not built here: its
 one definition each is in Functor/Representable/Additive.v, and both
 Watts files consume it.

 (2) The text form.  **[watts_theorem T AF contT U]**, the name the
 issue's Verification block prints: for T : (RMod R)^op ⟶ Ab additive
 ([AF], against [AbEnriched_op (RMod_AbEnriched R)] and
 [Ab_AbEnriched]) and continuous on (RMod R)^op ([contT :
 PreservesImageLimit T] — for every diagram K into (RMod R)^op, that is
 every diagram of modules read backwards, and every chosen limit of K
 there, that is every chosen COLIMIT of modules, T carries it to a
 limit of Ab), and [U : Untruncate], some module A with
 [CoHomAb (RMod_AbEnriched R) A ≅ T] in [@Fun ((RMod R)^op) Ab]: T is
 naturally isomorphic, as an Ab-valued functor, to hom_R(−, A).
 [watts_theorem_sets] is the Sets-level representation it upgrades,
 [watts_theorem_obj] reads the representing object back as that
 representation's at [eq_refl], and [watts_theorem_to_at] reads back
 the iso's components as the representation's own, at [eq_refl].
 [watts_theorem_adjoint] is the book's first step: the left adjoint of
 T itself, by [SAFT_wellpowered] at D := Ab.  The continuity
 hypothesis is stated in the form SAFT consumes; Construction/Comma/
 Creation.v converts it to and from [ContinuousFunctor] in both
 directions.

 (3) Exercise 3.  **[watts_ex3 T AF contT G U]**: for T : RMod R ⟶ Ab
 additive and continuous, a cogenerator [G] of RMod R and [U :
 Untruncate], some A with [HomAb (RMod_AbEnriched R) A ≅ T]; the
 Sets-level step is [watts_ex3_sets].  **[watts_ex3_QZ]** takes the
 cogenerator from Exercise 2(b), [snd (QZ_injective_cogenerator R HI
 HC)], so that its premises are the book's "The additive group Q/Z of
 rational numbers modulo 1 is known to be an injective cogenerator of
 Ab" (Exercise 2(b)), taken as hypotheses ([HI : Injective Ab QZ], [HC
 : QZ_family_cogenerates]), together with [U].  [watts_ex3_QZ_cogenerator]
 shows at [eq_refl] that the cogenerator used is
 [coext_cogenerator R (QZ_Cogenerator HC)]: the
 injectivity premise [HI] is carried, as the exercise states it, but
 not consumed, SAFT asking only for the cogenerating half.

 (4) The witnesses of NON-VACUITY below: [watts_ex3_forget],
 [RMod_Forget_equiv] and [watts_ex3_forget_obj]; [HomAbForget R A] (the
 functor M ↦ Hom_Ab(U M, A) on (RMod R)^op), [HomAbForget_additive],
 [HomAbForget_continuous], [watts_theorem_coext], [coext_representable],
 [watts_theorem_coext_obj] and [watts_theorem_coext_obj_2a].  And
 [watt_at_forget], the one with NO hypothesis:
 [HomAb (RMod_AbEnriched R) (Ring_RMod R) ≅ RMod_Forget_Ab R] in the
 functor category into [Ab], Functor/Representable/Additive.v's
 upgrade applied to Instance/Mod/Representable.v's [rmod_representable]
 carried along [RMod_Forget_equiv].  It is the conclusion of Exercise 3
 at T := [RMod_Forget_Ab R], reached without the special adjoint
 functor theorem, and so without [G] or [U].

 (5) Mac Lane's last step (section 5).  [ab_hom_Z_iso :
 HomAb Ab_AbEnriched (FreeAb SetsOne) ≅ Id[Ab]] in [@Fun Ab Ab] is
 Ab(ℤ, X) ≅ X, natural in X, with ℤ the free abelian group on one
 point: the upgrade at T := Id[Ab] of the representation of [Ab_Forget]
 that [free_ab_adjunction] gives, through [Ab_Forget_Id_equiv].
 [watts_theorem_Fz T AF contT U] is C ≅ F ℤ: the representing object of
 [watts_theorem] is isomorphic in RMod R to the left adjoint F of
 [watts_theorem_adjoint] at [FreeAb SetsOne] -- [repr_unique_iso]
 between the SAFT representation of [Ab_Forget ◯ T] and the one the
 composite adjunction FreeAb ⊣ Ab_Forget, F ⊣ T gives.  It carries
 [watts_theorem]'s hypotheses, [U] among them.

 (6) What the unconditional theorem subsumes (section 6).
 [watts_theorem_via_unconditional] has [watts_theorem]'s statement,
 hypotheses and universe binders (Representable's two excepted, which
 the statement does not mention), and its body is
 [watts_theorem_unconditional T AF (PreservesImageLimit_Continuous
 contT)]: [U] is carried and not consumed.
 [watts_unconditional_coext R A] is the text form at T :=
 [HomAbForget R A] with NO [Untruncate]: the module
 [watts_theorem_unconditional] returns there is ≅ [CoextObj R A] in
 RMod R, by [repr_unique_iso] between [coext_representable] and
 [RModop_continuous_representable]; [watts_unconditional_coext_2a]
 continues it to [HomZL R_R A] through [homzl_coext_iso].  These are
 the unconditional counterparts of [watts_theorem_coext_obj] and
 [watts_theorem_coext_obj_2a].

 ** THE CONDITIONS, PLAINLY

 Neither theorem of this file is unconditional, and no in-tree term
 discharges its conditions.  The text form's CONCLUSION needs neither
 condition: Instance/Mod/Watts/Unconditional.v proves it with no
 hypothesis, and section 6 derives [watts_theorem]'s statement from
 it; what is conditional here is the SAFT route.

 - [Untruncate] — "every propositionally truncated type has an
 element" — is a hypothesis of both.  The tree inhabits it nowhere
 (Adjunction/SAFT.v's header: "the tree inhabiting neither
 [Untruncate] nor [IEM]"), and Instance/Sets/Classifier/OneLevel.v
 derives it from informative excluded middle
 ([untruncate_of_IEM]).  The text form spends it exactly once, in
 [RMod_CoWellPowered_untruncate]: a quotient object of a module is
 indexed by its kernel only if a preimage under the epi can be
 produced as data, and [rmod_epic_surjective] returns it only in
 [Prop].  Exercise 3 spends it in [RMod_WellPowered_untruncate], to
 rebuild a subobject's domain from its truncated image.
 Instance/Mod/WellPowered.v quotes the refusals at the pin without
 it.  One universe up neither needs it: that file's
 [RMod_WellPoweredAt_up] and [RMod_CoWellPowered_up] (the latter
 indexing each quotient object by its codomain, map and
 [Prop]-level surjectivity) are unconditional.  But
 [SAFT_wellpowered] consumes a [WellPowered], whose index sits at
 or below the hom universe ([w <= h] in its binder), and both one-up
 families are refused where [WellPowered@{o c c o x}] (respectively
 [CoWellPowered@{o c c o x}]) is expected, "Cannot enforce <1> = c
 because c < <1>" (the same file's WHY [Untruncate], MEASURED); so
 [U] stays.
 - Everything else the text form uses is unconditional: the
 cocompleteness [RMod_Cocomplete_via_GAFT] (Prop-congruence solution
 sets, #450's template) and the cogenerator R of (RMod R)^op
 ([RModop_Cogenerator]).
 - Exercise 3 takes a cogenerator of RMod R as well, the hypothesis
 [G], which the special adjoint functor theorem consumes at RMod R.
 In [watts_ex3_QZ] that hypothesis becomes the book's premise on
 ℚ/ℤ, and Instance/Mod/Cogenerator.v shows the premise is
 classical: [QZ_cogenerates_Ab_DNE] derives ∀ P, ¬¬P → P from [HC],
 and [QZ_injective_WLEM] derives the informative ∀ P, (¬P) + (¬¬P)
 from [HI].  Those are closed theorems of the core that do not
 refute the premises; they show the premises cannot be proved
 without an axiom unless double-negation elimination can.  So
 [watts_ex3_QZ]'s hypotheses have no in-tree inhabitant, and no
 inhabitant of all of them is constructible axiom-free unless DNE
 is.  The ℚ/ℤ premise is the one condition of Exercise 3 PROVED
 classical.  Nothing in tree proves [G] or [U] NECESSARY for the
 covariant form: the SAFT route consumes both, no other route to it
 is attempted, and [RMod R] well-powered at the pin without [U] is
 neither built nor refuted (Instance/Mod/WellPowered.v).
 - The text form holds at [RingObject@{c c c}] only: the ring's
 auxiliary, carrier and proof universes coincide (UNIVERSES below).
 [watts_theorem_unconditional] keeps them apart.

 ** STRENGTHS, STRICT FIRST

 At [eq_refl]: [watts_theorem_obj] (the representing object of the text
 form IS [repr_obj] of [watts_theorem_sets], so by Corollaries.v's
 [continuous_Set_functor_representable_obj] the SAFT left adjoint of
 [Ab_Forget ◯ T] at the one-point set), [watts_theorem_to_at] (each
 component of the Ab-level isomorphism is the Sets-level
 representation's component, unchanged) and [watts_ex3_QZ_cogenerator].
 Up to ≅ in RMod R: the representing objects of the two witnesses,
 [watts_ex3_forget_obj] (≅ [Ring_RMod R]) and [watts_theorem_coext_obj]
 (≅ [CoextObj R A]) with [watts_theorem_coext_obj_2a] (≅ [HomZL R_R A],
 Exercise 2(a)'s hom_ℤ(R, A)).  The headline isomorphisms are
 isomorphisms in the functor category into [Ab], componentwise ≈ of
 group homomorphisms.  REFUSED at [eq_refl], measured by appending one
 [Example] to a copy of this whole file, in environment
 [R : RingObject], [G : Cogenerator (RMod R)], [U : Untruncate]:
 [projT1 (watts_ex3_forget R G U) = Ring_RMod R] — "The term "eq_refl"
 has type "projT1 (watts_ex3_forget R G U) = projT1 (watts_ex3_forget R
 G U)" while it is expected to have type "projT1 (watts_ex3_forget R G
 U) = Ring_RMod R" (cannot unify "projT1 (watts_ex3_forget R G U)" and
 "Ring_RMod R")": the SAFT object is an intersection of subobjects of
 a cogenerator power, and it depends on the variable [U]; the
 comparison is an isomorphism, not a conversion.

 By conversion, and so named in the statements: [watt_at_forget]'s
 representing object is [Ring_RMod R] and [ab_hom_Z_iso]'s is
 [FreeAb SetsOne].  Up to ≅ in RMod R: [watts_theorem_Fz], the
 representing object of the text form ≅ F ℤ.

 Transparency: five [Defined] and no [Qed], counted by token outside
 comments; [RMod_Forget_Ab_additive], [RMod_Forget_equiv],
 [HomAbForget_additive], [coext_representable] and
 [Ab_Forget_Id_equiv].  Every other constant is a term [Definition] or
 [Example].  FLIPS: see AXIOMS AND MEASUREMENTS.

 ** UNIVERSES, MEASURED

 By [About] under [Set Printing Universes], stdlib bounds
 ([compose.u0], [Projections.u0], [prod_rect.u0], [ID.u0],
 [Fin.case0.u0], [VectorDef.*], ...) left out, except [eq_rect_r],
 attributed below.  [RMod@{o x a p c} : RingObject@{a c p} →
 Category@{o c c}] names the ring's (auxiliary, carrier, proof)
 universes, [RMod]'s object universe o and its second universe x; the
 homs sit at the carrier c.  [Ab@{b c}] is the target, its object
 universe b (a in the text form) and its carrier the same c.
 [PreservesImageLimit@{o c b c pk c pa c}] names its sort [pk] and its
 auxiliary slot [pa]; its shape slots are c.  [Representable@{ra rt pa
 o c}] names Representable's two own universes [ra rt].

 watts_theorem@{c o x a pk pa ra rt +} :
 ∀ {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c}),
 AdditiveFunctor@{o c a} T → PreservesImageLimit@{o c a c pk c pa c}
 → Untruncate@{c} → ∃ A : obj[RMod@{o x c c c} R],
 CoHomAb@{o c a} (RMod_AbEnriched@{x o c c c} R) A ≅ T
 watts_ex3@{a c p o x b g pk pa ra rt +} :
 ∀ {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c}),
 AdditiveFunctor@{o c b} T → PreservesImageLimit@{o c b c pk c pa c}
 → Cogenerator@{g o c} (RMod@{o x a p c} R) → Untruncate@{c}
 → ∃ A, HomAb@{o c b} (RMod_AbEnriched@{x o a p c} R) A ≅ T
 watts_ex3_QZ@{r o x b pk pa ra rt +} :
 ∀ {R : RingObject@{r r r}} (T : RMod@{o x r r r} R ⟶ Ab@{b r}),
 … → Injective Ab@{o r} QZ@{r r r _}
 → QZ_family_cogenerates@{o r _ o _} → Untruncate@{r} → ∃ A, …
 (the third slot of [QZ_family_cogenerates], the index universe of
 the one-member family, is left free, bounded by the carrier r:
 SAFT's [c <= so])

 Explicit universe instances are written only on constants whose
 instance length has a precedent elsewhere in tree ([RMod], [Ab],
 [Sets], [RingObject], [AbObject], [Cogenerator], [Representable],
 [PreservesImageLimit], [Untruncate]); [ContinuousFunctor], [QZ],
 [RMod_Forget], [RMod_Forget_Ab] and this file's own extensible
 [HomAbForget] are reached through type ascriptions instead, so that a
 different instance length on another Coq version cannot refuse them.

 No constant of this file carries a universe EQUATION: searching the
 constraint blocks of the [About] output of all twenty-seven, each
 queried by its fully qualified name, for " = " finds none (run on a
 scratch file, the same search finds the equation of a definition
 taking [F : D ⟶ C] and [U : C ⟶ D] and those of [Adjunction]'s own
 [About]).  Over the whole output, " = " occurs only in the statements
 of the [eq_refl] readbacks [watts_theorem_obj], [watts_theorem_to_at]
 and [watts_ex3_QZ_cogenerator].  What each inherits, and from where:

 - [RingObject@{c c c}] in the text form and its witness.  Forced by
 [RModop_Cogenerator], whose ring is [RingObject@{c c c}] because
 [Ring_RMod R] carries R's own abelian group
 (Instance/Mod/WellPowered.v measures that).  Here:
 [watts_theorem_sets]'s body at [R : RingObject@{a c p}] with
 [c < a] declared is refused, "The term "R" has type
 "RingObject@{a c p}" while it is expected to have type
 "RingObject@{<1> <1> <1>}" (universe inconsistency: Cannot enforce
 c = a because c < a)"; the same body
 with no constraint declared is accepted and reads back [a = c],
 [a = p].  Exercise 3 keeps the ring's three universes apart;
 [watts_ex3_QZ] is at [RingObject@{r r r}] by [CoextObj]'s own
 identification (Instance/Mod/Coextension.v), and the [Ab] of its
 two ℚ/ℤ premises sits at RMod's object universe o, as in
 [QZ_injective_cogenerator]'s own readback, which under this file's
 imports prints [@Injective Ab@{a r} QZ@{r r r u0}] beside
 [Cogenerator@{c a r} (RMod@{a u r r r} R)] ([Injective] is the
 notation for [Projective] at the opposite category).
 - [Set < c]: from [RMod_WellPowered_untruncate] and
 [RMod_CoWellPowered_untruncate] (their [Prop]-valued index lives at
 [max(Set+1, c)]) and from [RMod_Cocomplete_via_GAFT] (GAFT's index
 placement).  So a ring whose carrier sits at [Set] is excluded;
 [Int_Ring] is universe polymorphic and meets it above [Set].
 - The Sets level is [pa].  [Ab_Forget@{b pa c}] lands in
 [Sets@{c pa}], the auxiliary slot of the continuity hypothesis.
 That identification is forced by the route:
 [PreservesImageLimit_Continuous] turns [pa] into the tenth slot of
 [ContinuousFunctor], [continuous_compose] shares that slot between
 T and [Ab_Forget], and [Ab_Forget_creates_continuous] has its
 tenth slot equal to its [Sets] object universe.  With a separate
 [s] for [Ab_Forget] and [pa < s] declared, [watts_theorem_sets]'s
 body is refused, expected "Representable@{ra rt s o c}
 (Ab_Forget@{a s c} ◯ T)" against the body's
 "Representable@{<1> <2> pa o c} (Ab_Forget@{a pa c} ◯ T)"
 "(universe inconsistency: Cannot enforce pa = s because pa < s)";
 the constants therefore use [pa] for that level.
 - Strict and non-strict [eq_rect_r] bounds: [c < eq_rect_r.u0] and
 [c <= eq_rect_r.u1] on every constant built on the SAFT, from
 [continuous_Set_functor_representable] and [SAFT_wellpowered]
 (whose readbacks carry [h < eq_rect_r.u0], attributed in
 Corollaries.v's header to Adjunction/SAFT/InitialObject.v's
 [complete_pullbacks]), and [x <= eq_rect_r.u0], which is those
 constants' [t <= eq_rect_r.u0] (from #452's
 [special_initial_object_wellpowered_at], per the same header) at
 [t := x], the fifth slot of [WellPowered@{o c c o x}].
 - The witnesses.  [HomAbForget]'s intermediate [Ab] sits at RMod's
 object universe o.  The continuity proof stated for the composite
 with that [Ab] at its own [m], and [o < m] declared, is refused,
 "… (cannot unify "@padd_respects _ (@abenriched_preadditive _
 (@AbEnriched_op@{m c} Ab@{m c} Ab_AbEnriched@{m <1> c})) A
 (fobj[(RMod_Forget_Ab@{x o m c c c} R)^op] (fobj[K] x0))" and
 "@padd_respects _ (@abenriched_preadditive _ (@AbEnriched_op@{o c}
 Ab@{o c} Ab_AbEnriched@{o <1> c})) A (fobj[(RMod_Forget_Ab@{x o o
 c c c} R)^op] (fobj[K] x0))")" (<1> a universe the scratch compile
 generated); the same statement with no constraint declared is
 accepted and reads back [o = m].  The cause is [coex_adjunction],
 whose left adjoint lands in an [Ab] at RMod's object universe (its
 readback: [RMod_Forget_Ab@{u3 u2 u2 u u1 u0} R ⊣
 Coextension@{u u0 u1 u2 u3} R]).  [HomAbForget_continuous]'s
 tenth slot is x: named [k6] with [x < k6] declared the proof is
 refused, and with [k6 < x] declared it is refused too, both with
 "cannot unify "Functor.Compose_obligation_1 J (RMod R)^op Ab
 (HomAbForget R A) K" and "Functor.Compose_obligation_1 J
 (RMod R)^op Ab (CoHomAb Ab_AbEnriched A ◯ (RMod_Forget_Ab R)^op)
 K"".  So the Sets level of the text form at
 that witness is x, and [coext_representable] is stated at
 [Sets@{c x}] to meet it in [repr_unique_iso].  Likewise at the
 Exercise 3 witness, [RMod_Forget_Ab_creates_continuous] has its
 tenth slot at RMod's x, and [rmod_representable] lands in
 [Sets@{c x}]; neither shows in [watts_ex3_forget_obj]'s type.
 - Two equations appeared in drafts and are NOT forced, each measured
 by appending the draft to a copy of this whole file with the
 opposite order declared: [x = s] in a draft of [watts_ex3] (with
 a [ContinuousFunctor] hypothesis, [Ab_Forget@{b s c}] ascribed once
 and [watts_ex3_sets] elaborated a second time inside [exact]),
 which is accepted with [s < x] declared; and [x = s] in a draft of
 [coext_representable] at a separate [Sets@{c s}], accepted with
 [x < s] declared.  Both came from elaboration, not from a donor;
 the landed constants route [watts_ex3_sets] through ONE ascribed
 occurrence and name the level they need.
 - The constants added with [watt_at_forget] and section 5.
 [watt_at_forget] is at [RingObject@{c c c}] because its
 representing object [Ring_RMod R] is (the collapse
 Instance/Mod/WellPowered.v measures), and reads back
 [HomAb@{o c b} (RMod_AbEnriched@{x o c c c} R) (Ring_RMod@{c c c}
 R) ≅ RMod_Forget_Ab@{x o b c c c} R].  [ab_hom_Z_iso@{a c +}]
 lands in [Ab@{a c}] at both ends; the free group's own universes
 and the one-point set's are left to inference, reached through
 [FreeAb] and [SetsOne] without instances.  [watts_theorem_Fz]
 carries [watts_theorem]'s named universes.
 - Section 6.  [watts_theorem_via_unconditional@{c o x a pk pa +}]
 carries [watts_theorem]'s named universes but [ra rt].
 [watts_unconditional_coext] and its [_2a] instantiate
 [watts_theorem_unconditional@{c c c o x b x …}]: the ring collapsed
 by [CoextObj], and that theorem's Sets level s at x, which is
 [HomAbForget_continuous]'s tenth slot, as above.  The [Ab] of
 [HomAbForget] is ascribed at [b] in both statements; left to
 inference it was set to x, and [About] read back
 [HomAbForget@{c o x x}] with the binder's b unused.

 ** NON-VACUITY

 Exercise 3 at T := [RMod_Forget_Ab R]: [watts_ex3_forget R G U], whose
 continuity is #449's creation ([RMod_Forget_Ab_creates_continuous]),
 not an adjunction, so the witness is not circular.  Its representing
 object is ≅ [Ring_RMod R] ([watts_ex3_forget_obj], at
 [RingObject@{c c c}]): [repr_induced_iso] against
 Instance/Mod/Representable.v's [rmod_representable], along the
 identity-component iso [RMod_Forget_equiv] between [RMod_Forget R] and
 [Ab_Forget ◯ RMod_Forget_Ab R].  It inherits both [G] and [U].

 The text form at T := [HomAbForget R A], M ↦ Hom_Ab(U M, A), for any
 abelian group A: [watts_theorem_coext R A U].  Additivity is
 [HomAbForget_additive]; continuity is [HomAbForget_continuous], the
 composite of [RMod_Forget_Ab R]^op — continuous because
 [RMod_Forget_Ab R] is a LEFT adjoint, [coex_adjunction], read through
 [Opposite_Adjunction] and [right_adjoint_Continuous] — with
 [CoHomAb_continuous].  Its representing object is ≅ [CoextObj R A]
 ([watts_theorem_coext_obj]): [repr_unique_iso] against
 [coext_representable], whose components are the coextension
 adjunction's own hom bijections, read in (RMod R)^op and brought back
 by [Isomorphism_Opposite]; and ≅ [HomZL R_R A], Exercise 2(a)'s
 hom_ℤ(R, A) ([watts_theorem_coext_obj_2a], through HomTensor.v's
 [homzl_coext_iso]).  Mac Lane's C is therefore identified, up to
 isomorphism, as hom_ℤ(R, A) at this T.  It inherits [U] and nothing
 else.

 Every witness of the two theorems inherits [Untruncate], which has no
 in-tree inhabitant, so neither theorem has an unconditional instance
 in tree.  The text form's witness has an unconditional counterpart
 through Instance/Mod/Watts/Unconditional.v's theorem, in this file's
 section 6: [watts_unconditional_coext] (≅ [CoextObj R A]) and
 [watts_unconditional_coext_2a] (≅ [HomZL R_R A]).  [watt_at_forget]
 is not an instance of either theorem but of the additive upgrade both
 are built on, at the forgetful functor, and it needs nothing:
 Exercise 3's conclusion at that T, without the special adjoint
 functor theorem.

 ** AXIOMS AND MEASUREMENTS

 [Print Module Category.Instance.Mod.Watts] lists twenty-seven
 constants and no [Program] obligation (the file uses no [Program]);
 each reports "Closed under the global context" under [Print
 Assumptions] by its fully qualified name.
 FLIPS: each of the five [Defined] was turned to [Qed] alone in a copy
 of the whole file; [coext_representable] is load-bearing (its
 representing object must reduce to [CoextObj R A] for
 [watts_theorem_coext_obj] to typecheck, and, measured with that
 constant and its [_2a] removed from the flipped copy, for
 [watts_unconditional_coext] too) and the other four recompile as
 [Qed]; they are kept transparent as data, like
 Functor/Representable/Additive.v's [HomAb_additive].  [make todo] is
 unchanged by this file.

 ** NOT DELIVERED

 No unconditional covariant form: Exercise 3 is delivered only over
 [Untruncate] and a cogenerator of RMod R, which no in-tree term
 supplies at a size [cogen_prod] accepts (the unconditional
 [RMod_Cogenerator_large] is large, and Instance/Mod/Cogenerator.v's
 metatheorems show the book's ℚ/ℤ one classical).  Nothing in tree
 proves either hypothesis necessary: the SAFT route here consumes both,
 no other route to the covariant form is attempted, and [RMod R]
 well-powered at the pin without [Untruncate] is neither built nor
 refuted.  The contravariant form without [Untruncate] is
 Instance/Mod/Watts/Unconditional.v's, through GAFT with an explicit
 solution set, and section 6 consumes it.  No
 isomorphism of the free abelian group on one point with
 Instance/Ab/Free.v's [ab_int], so section 5's ℤ is [FreeAb SetsOne],
 not the integers of [Int_Ring]; and [watts_theorem_Fz] compares
 objects only, with no Ab-level isomorphism CoHomAb (F ℤ) ≅ T through
 [ab_hom_Z_iso] (that would need [CoHomAb] functorial in its object).
 The text form only at [RingObject@{c c c}].  No
 uniqueness beyond Functor/Representable.v's [repr_unique_iso].  No
 Eilenberg–Watts tensor form (a cocontinuous additive
 Mod_R → Mod_S is − ⊗_R N) and no bimodule-valued version.  No
 naturality of the representing object in T.  No [Instance] is
 registered.  The refusals quoted above were measured in scratch copies
 of this whole file, and Test/ProbeWatts454.v pins them under its own
 import list: the [eq_refl] refusal of [watts_ex3_forget]'s object as
 its N16; [watts_theorem_sets]'s body at [c < a] as N17 (peeled to
 [RModop_Cogenerator] as N18); the Sets level, at [pa < s] and at
 [s < pa], as N19 and N29; [HomAbForget_continuous]'s body with the
 witness's [Ab] at m, at [o < m] and at [m < o], as N31 and N32 (at its
 first factor as N20 and N30); and that body at the tenth slot k6, at
 [x < k6] and at [k6 < x], as N33 and N34 (the constant itself as N21
 and N22).  Its controls [p454_sets_apart_free], [p454_ex3_twice],
 [p454_hafc_body_at_o] and [p454_hafc_body_at_x] restate the accepted
 forms, and its N23 pins that the representing object is not F ℤ by
 conversion while Adjunction/GAFT.v's [GAFT], at which both sides stop
 reducing, is opaque.  It does not pin the draft of
 [coext_representable] at a separate [Sets@{c s}], a whole proof. 

 --------
 书籍：      Mac Lane，《为工作中的数学家准备的范畴论》，第二版（GTM 5），§V.8，第131–132页印刷（PDF第140–141页），账目项目 `maclane:V.8:thm-watt` 和 `maclane:V.8:ex3`（第454期），从印刷页阅读。文本，第131页：
 “瓦特定理 [1960] 是另一个例子。任意环 R 是范畴 R-Mod 中的生成元，因此在 (R-Mod)^op 中是余生成元。由此可得，任意从 R-Mod 到 Ab 的逆变加性函子 T，如果将小余积映射为极限，则存在一个群同构，使得 T 可被表示为 T ≅ hom_R(−, C)，其中 C 是某个 R-模。” 练习题 3，第132:
 “使用练习 2(b) 和特殊伴随函子定理证明任意连续加法函子 T: R-Mod → Ab 是可表示的。（Watt 定理）。”书中拼写为“Watt's”；作者是 Charles E. Watts。（仓库中的目录 doc/plan/books/maclane/inventory/V.json 用自己的话总结了两篇文章；此处引用的是印刷页。）
 论文：C. E. Watts, “某些加法函子的内在特征”，Proc. Amer. Math. Soc. 11 (1960), 5–8；以及 S. Eilenberg, “某些基本函子的抽象描述”，J. Indian Math. Soc. (N.S.) 24 (1960), 231–234 — 两篇原始文章，如 nLab 页面所列。nLab:       https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem 
 nLab:       https://ncatlab.org/nlab/show/cogenerator 
 nLab:       https://ncatlab.org/nlab/show/injective+object 
 nLab页面“injective cogenerator”不存在（HTTP 404，由curl在2026-09-24测量，如Instance/Mod/Cogenerator.v中记录）。

 路径。 该问题指向Instance/Module/Watts.v。 该树将其模块文件保存在Instance/Mod/下（#258, #401, #449），所以这个文件是Instance/Mod/Watts.v：仅路径上的偏差。本文件与无条件定理。对于文本形式而言，本文件严格弱于 Instance/Mod/Watts/Unconditional.v 的 [watts_theorem_unconditional]，该文件通过 GAFT 和显式解集证明了书中对偶命题的陈述，且除了书中自身的两个假设（以及 [Set < c]）之外无需其他假设；该文件是 #454 文本形式的标题。本文件保留的原因是它采用了 Mac Lane 的 SAFT 路径，该问题的审稿人线路称之为“可表示性必须从 SAFT 加可加性推导”，并且因为练习 3，即协变形式，仅在此处提供，并且是有条件的。它导入了无条件的文件，第6节测量树中的关系：[watts_theorem_via_unconditional] 从 [watts_theorem_unconditional] 推导出 [watts_theorem] 的声明，[Untruncate] 被携带且未消耗，[watts_unconditional_coext] 和 [watts_unconditional_coext_2a] 是第4节文本形式的证据，不包括 [Untruncate]。该文件的常量中哪些被无条件定理包含，哪些不被包含，都列在该文件的头部、标题和 SAFT 路径中。

 ** 背景瓦茨（Watts）和艾伦伯格（Eilenberg）在同一年独立地证明了，在模范畴之间尊重余极限的函子就是张量函子：一个加法性、余连续的 F : Mod_R → Mod_S 自然同构于 − ⊗_R N，其中 N 是 F(R)，且 R 通过对左乘作用应用 F 在 N 上作用（这是 nLab 页面上的说法及其第一个备注）。原因是 R 生成 R-Mod：每个模都是自由模的商，即 R 的副本的余积，因此一个尊重余极限的函子由其在 R 上的取值以及 R 的自同构在那个取值上的作用所确定。nLab 页面记录了对右正合函子（Nyman 和 Smith）、对同调和更高代数（Hovey；Lurie）、以及对在双范畴中增强的范畴（Arkor 和 McDermott）的推广。麦克莱恩将这个结果作为特殊伴随函子定理的一个应用，并给出了对偶的表述：一个将余极限变为极限的逆变加法函子是同函子 hom_R(−, C)。练习3要求求协变的类似情况，一个连续加法函子 T : R-Mod → Ab 是 hom_R(A, −)，这需要 R-Mod 的余生成元，因此需要练习 2(b)。

 ** 书中的证明，以及这里的证明Mac Lane 的概要：“根据特殊伴随函子定理 T: (R-Mod)^op → Ab 有一个左伴随 F；由于 T 是加法的，伴随关系 Ab(G, TA) ≅ hom_R(A, FG)，G ∈ Ab, A ∈ R-Mod，是加法群的同构；设 G = Z 得到 TA ≅ Ab(Z, TA) ≅ hom_R(A, FZ”，因此 C = Fℤ。第一步是下面的 [watts_theorem_adjoint]，逐字；最后一步是第 5 节的 [ab_hom_Z_iso]，Ab(ℤ, X) ≅ X，对 X 作为取值在 Ab 的函子是自然的，其中 ℤ 被读作一个点的自由阿贝尔群 [FreeAb SetsOne]，和 [watts_theorem_Fz]，在 R-Mod R 中的表示对象 ≅ F(ℤ)。（同构 Ab(ℤ, X) ≅ X 是表示 [free_ab_adjunction] 在 Id [Ab] 上的加法升级，并且表示对象的比较甚至不需要它。）仍然未解决：自由群在一点上的同构与 Instance/Ab/Free.v 的 [ab_int] 尚未建立，比较 Instance/Ab/Generator.v 将 [FreeAbObject unit_setoid_object] 记录为未完成；[SetsOne] 是 Construction/Elements.v 中 [Sets] 终对象的名称。) 该表示本身是按照问题审阅者行所要求的方式获得的，“由 SAFT 加可加性导出”，通过 Yoneda：SAFT。附加/SAFT/表征/推论.v 的  
 [continuous_Set_functor_representable] — Mac Lane 在书第 130 页上的推论，建立在 #453 的 [SAFT_wellpowered] 基础上 — 表示集合值函子 [Ab_Forget ◯ T]；其表示对象是在单点集合处 [Ab_Forget ◯ T] 的左伴随。  
 可加性。函子/可表示/可加.v 的 [watt_ab_repr] 将 [Ab_Forget ◯ T]（对于可加的 T）的表征升级为在函子范畴中进到 [Ab] 的同构 [HomAb A ≅ T]，并且组件相同。  

 对于文本形式，SAFT 应用于 C := (RMod R)^op：是完备的，因为 RMod R 是余完备的，由 R 生成，并且是良构的，因为 RMod R 是余良构的。对于练习 3，它应用于 C := RMod R：完备、良构，并提供了一个余生成元。  

 ** 已消耗，未构建- Adjunction/SAFT/Characterization.v 的 [SAFT_wellpowered] 及其附属推论 Corollaries.v 的 [continuous_Set_functor_representable] (#453)。- Instance/Mod/Colimit.v 的 [RMod_Cocomplete_via_GAFT]，解读为 (RMod R)^op 的完备性，通过 Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete]；Instance/Mod/Limit.v 的 [RMod_Complete] 和 [RMod_Forget_Ab_creates_continuous] (#449)。- Instance/Mod/WellPowered.v 的 [RModop_Cogenerator]（R 作为 RMod R 的生成元，解读为对偶的余生成元），[RMod_CoWellPowered_untruncate] 和 [RMod_WellPowered_untruncate]。- Functor/Representable/Additive.v 的 [HomAb]、[CoHomAb]、[CoHomAb_continuous]、[LocallyPropositional_op]、[watt_ab_repr]、[watt_ab_iso] 和 [wab_obj]。- Construction/Comma/Limit.v 的 [PreservesImageLimit] 与 Construction/Comma/Creation.v 的 [PreservesImageLimit_Continuous] 和 [Continuous_PreservesImageLimit]；Structure/Limit/Preservation.v 的 [continuous_compose] 和 [cone_assoc_inv]；Instance/Ab/Limit.v 的 [Ab_Forget_creates_continuous] 和 [Ab_Forget_reflects_limits]；Functor/Hom/Continuous.v 的 [representable_iso_ContinuousFunctor]；Instance/Fun.v 的 [iso_equiv] 和 [equiv_iso]。- Instance/Mod/Cogenerator.v 的 [QZ_injective_cogenerator]、[QZ_family_cogenerates]、[QZ_Cogenerator] 和 [coext_cogenerator]（练习 2(b)）；Instance/Mod/Coextension.v 的 [coex_adjunction] 和 [CoextObj]；Instance/Mod/HomTensor.v 的 [HomZL] 和 [homzl_coext_iso]（在 B := R 时的练习 2(a)）。- Adjunction/Continuity.v 的 [right_adjoint_Continuous] 与 Adjunction/Opposite.v 的 [Opposite_Adjunction]；
 Instance/Mod/Representable.v 的 [rmod_representable]；
 Functor/Representable.v 的 [repr_induced_iso] 和 [repr_unique_iso]；
 Construction/Opposite.v 的 [Isomorphism_Opposite]；
 Instance/Sets/Classifier/OneLevel.v 的 [Untruncate]。 - 对于第5节：Instance/Ab/Free.v 的 [FreeAb] 和 [free_ab_adjunction]；
 Adjunction/Representability/Sets.v 的 [representable_of_left_adjoint] 和 [Representable_transport]；
 Adjunction/Compose.v 的 [Adjunction_Compose]；
 Construction/Elements.v 的 [SetsOne]；
 Structure/AbCategory.v 的 [Id_AdditiveFunctor]。 - 对于第6节：Instance/Mod/Watts/Unconditional.v 的 [watts_theorem_unconditional] 和 [RModop_continuous_representable]。

 ** 已构建内容(1) [RMod_Forget_Ab_additive]：遗忘函子是加性的，在 [reflexivity]。值为 Ab 的 Hom 函子的连续性，[HomAb_continuous] 和 [CoHomAb_continuous]，在这里没有构建：它们各自的定义在 Functor/Representable/Additive.v 中，两个 Watts 文件都使用了它。(2) 文本形式。** [watts_theorem T AF contT U] **，问题的验证块打印的名称：对于 T : (RMod R)^op ⟶ Ab 加性
 ([AF], 对抗 [AbEnriched_op (RMod_AbEnriched R)] 和 [Ab_AbEnriched]) 并且在 (RMod R)^op 上连续 ([contT : 保持图像极限 T] — 对于每个进入 (RMod R)^op 的图 K，也就是每个模块图逆读，每个在那里的选定极限，也就是每个模块的选定余极限，T 将其映射为 Ab 的极限)，以及 [U : Untruncate]，一些模块 A，其在 [@Fun ((RMod R)^op) Ab] 中的 [CoHomAb (RMod_AbEnriched R) A ≅ T] ：T 作为 Ab 值函子自然同构于 hom_R(−, A)。[watts_theorem_sets] 是它升级的集合级表示，[watts_theorem_obj] 将表示对象读回作为该表示在 [eq_refl] 处的表现，而 [watts_theorem_to_at] 将同构的分量读回为表示自身在 [eq_refl] 处的分量。[watts_theorem_adjoint] 是这本书的第一步：T 本身的左伴随，由 [SAFT_wellpowered] 在 D := Ab。连续性假设以 SAFT 消耗的形式给出；Construction/Comma/Creation.v 在两个方向上将其与 [ContinuousFunctor] 相互转换。(3) 练习 3. **[watts_ex3 T AF contT G U]**：对于 T : RMod R ⟶ Ab，加性且连续，RMod R 的一个余生成子 [G] 和 [U : Untruncate]，某个具有 [HomAb (RMod_AbEnriched R) A ≅ T] 的 A；集合层级的步骤是 [watts_ex3_sets]。**[watts_ex3_QZ]** 取自练习 2(b) 的余生成子，[snd (QZ_injective_cogenerator R HI HC)]，其前提是书中的“有理数模 1 的加法群 Q/Z 被公认为 Ab 的一个可注入余生成子”（练习 2(b)），作为假设 ([HI : Injective Ab QZ]，[HC : QZ_family_cogenerates])，以及 [U]。[watts_ex3_QZ_cogenerator] 在 [eq_refl] 处显示所使用的余生成子是 [coext_cogenerator R (QZ_Cogenerator HC)]：注入性前提 [HI] 被携带，如练习所述，但未被使用，SAFT 仅要求余生成的一半。(4) 以下的非空见证者：[watts_ex3_forget]、[RMod_Forget_equiv] 和 [watts_ex3_forget_obj]；[HomAbForget R A]（函子 M ↦ Hom_Ab(U M, A) 在 (RMod R)^op 上），[HomAbForget_additive]、[HomAbForget_continuous]、[watts_theorem_coext]、[coext_representable]、[watts_theorem_coext_obj] 和 [watts_theorem_coext_obj_2a]。同时 [watt_at_forget]，是没有假设的那一个：[HomAb (RMod_AbEnriched R) (Ring_RMod R) ≅ RMod_Forget_Ab R] 在函子范畴进入 [Ab]，Functor/Representable/Additive.v 的升级应用于 Instance/Mod/Representable.v 的 [rmod_representable] 并携带 [RMod_Forget_equiv]。它是演习 3 在 T := [RMod_Forget_Ab R] 上的结论，在没有特殊伴随函子定理的情况下得出，因此没有 [G] 或 [U]。(5) Mac Lane 的最后一步（第 5 节）。[ab_hom_Z_iso: HomAb Ab_AbEnriched (FreeAb SetsOne) ≅ Id [Ab]] 在 [@Fun Ab Ab] 中是 Ab(ℤ, X) ≅ X，在 X 上是自然的，其中 ℤ 是一个点的自由阿贝尔群：在 T := Id [Ab] 处的升级是 [Ab_Forget] 的表示，ZWZ133WZZ 通过 [Ab_Forget_Id_equiv] 给出。ZWZ135WZZ 是 C ≅ F ℤ：ZWZ136WZZ 的表示对象在 RMod R 中同构于 [watts_theorem_adjoint] 在 [FreeAb SetsOne] 处的左伴随 F -- [repr_unique_iso] 在 [Ab_Forget ◯ T] 的 SAFT 表示与复合伴随 FreeAb ⊣ Ab_Forget、F ⊣ T 给出的表示之间。它携带 [watts_theorem] 的假设，其中包括 [U]。(6) 无条件定理所包含的内容（第6节）。
 [watts_theorem_via_unconditional] 具有  [watts_theorem] 的陈述、假设和宇宙绑定（除了 Representable 的两个，因为陈述中未提及），其主体是 [watts_theorem_unconditional T AF (PreservesImageLimit_Continuous contT)]：[U] 被携带且未被消耗。
 [watts_unconditional_coext R A] 是在 T := [HomAbForget R A] 的文本形式，没有 [Untruncate]：模块 [watts_theorem_unconditional] 返回在 RMod R 中有 ≅ [CoextObj R A]，通过 [repr_unique_iso] 在 [coext_representable] 和 [RModop_continuous_representable] 之间；[watts_unconditional_coext_2a] 通过 [homzl_coext_iso] 将其继续到 [HomZL R_R A]。这些是 [watts_theorem_coext_obj] 和 [watts_theorem_coext_obj_2a] 的无条件对应物。

 ** 条件，简明这个文件中的两个定理都不是无条件的，并且没有任何树内项满足其条件。文本形式的结论不需要任何条件：Instance/Mod/Watts/Unconditional.v 在没有假设的情况下证明了它，第6节从中推导出了 [watts_theorem] 的陈述；这里有条件的只是 SAFT 路径。- [Untruncate] — “每个命题截断类型都有一个元素” — 是两者的假设。该树在任何地方都没有它的实例（Adjunction/SAFT.v 的标题：“该树既不包含 [Untruncate] 也不包含 [IEM]”），而 Instance/Sets/Classifier/OneLevel.v 则从信息排中律（[untruncate_of_IEM]）推导出它。文本形式正好使用它一次，在 [RMod_CoWellPowered_untruncate] 中：一个模的商对象只有在可以将其在满射下的原像作为数据生成时，才由其核索引，而 [rmod_epic_surjective] 仅在 [Prop] 中返回它。练习 3 在 [RMod_WellPowered_untruncate] 中使用它，以从截断的像重建子对象的定义域。Instance/Mod/WellPowered.v 在针脚处引用拒绝时没有它。一个上层宇宙也不需要它：该文件的 [RMod_WellPoweredAt_up] 和 [RMod_CoWellPowered_up]（后者通过其余域、映射和 [Prop] 级别满射对每个商对象进行索引）是无条件的。但 [SAFT_wellpowered] 消耗了一个 [WellPowered]，其索引位于同源宇宙之上或以下（[w <= h] 在其绑定器中），并且在期望 [WellPowered@{o c c o x}]（分别 [CoWellPowered@{o c c o x}]）的情况下，两个上层族都被拒绝，“无法强制 <1> = c 因为 c < <1>”（同一文件的 WHY [Untruncate]，经测量）；因此 [U] 保留。——文本形式使用的其他一切都是无条件的：余完备性 [RMod_Cocomplete_via_GAFT]（命题同余解集，#450 的模板）以及 (RMod R)^op 的協生成器 R（[RModop_Cogenerator]）。- 练习 3 同样采用了 RMod R 的一个余生成器，该假设 [G] 被特殊伴随函子定理在 RMod R 中使用。在 [watts_ex3_QZ] 中，该假设变成了书中关于 ℚ/ℤ 的前提，而 Instance/Mod/Cogenerator.v 显示这个前提是经典的：[QZ_cogenerates_Ab_DNE] 从 [HC] 推导出 ∀ P, ¬¬P → P，[QZ_injective_WLEM] 从 [HI] 推导出信息性陈述 ∀ P, (¬P) + (¬¬P)。这些是核心的封闭定理，并不反驳这些前提；它们表明这些前提在没有公理的情况下无法被证明，除非双重否定律可以证明。因此，[watts_ex3_QZ] 的假设在树内没有任何元素，除非 DNE 可以构造，否则没有办法在没有公理的情况下构造全部假设的元素。ℚ/ℤ 的前提是练习 3 的唯一已被证明为经典的条件。在树中没有任何内容证明 [G] 或 [U] 对协变形式是必要的：SAFT 路径同时使用了两者，没有尝试其他路径，而在没有 [U] 的情况下，[RMod R] 在引脚上的充分能力既没有建立也没有被反驳（Instance/Mod/WellPowered.v）。- 文本形式仅在 [RingObject@{c c c}] 处成立：环的辅助、承载和证明宇宙一致（见下方的 UNIVERSES）。[watts_theorem_unconditional] 将它们分开。

 ** 强度，严格第一在 [eq_refl] : [watts_theorem_obj]（文本形式的表示对象是 [repr_obj] 的 [watts_theorem_sets]，因此根据 Corollaries.v 的 [continuous_Set_functor_representable_obj]，是 [Ab_Forget ◯ T] 在单点集上的 SAFT 左伴随），[watts_theorem_to_at]（Ab 级同构的每个分量都是 Sets 级表示的分量，未改变）以及 [watts_ex3_QZ_cogenerator]。至于 RMod R 中的 ≅：两个证人的表示对象，[watts_ex3_forget_obj]（≅ [Ring_RMod R]）和 [watts_theorem_coext_obj]（≅ [CoextObj R A]）以及 [watts_theorem_coext_obj_2a]（≅ [HomZL R_R A]，习题 2(a) 的 hom_ℤ(R, A)）。主要同构是在函子范畴到 [Ab] 的同构，按分量分别是群同态的 ≈。在 [eq_refl] 被拒绝，通过将一个 [Example] 添加到此整个文件的副本中测量，在环境 [R : RingObject]、[G : Cogenerator (RMod R)]、[U : Untruncate] 中：
 [projT1 (watts_ex3_forget R G U) = Ring_RMod R] — “术语 'eq_refl' 的类型为 'projT1 (watts_ex3_forget R G U) = projT1 (watts_ex3_forget R G U)'，但预期类型为 'projT1 (watts_ex3_forget R G U) = Ring_RMod R'（无法统一 'projT1 (watts_ex3_forget R G U)' 和 'Ring_RMod R'）：SAFT 对象是一个余生成幂次子对象的交集，并且它依赖于变量 [U]；比较的是同构，而不是转换。

 通过转换，并在语句中如此命名：[watt_at_forget] 的表示对象是 [Ring_RMod R]，而 [ab_hom_Z_iso] 的表示对象是 [FreeAb SetsOne]。至多在 RMod R 中 ≅：[watts_theorem_Fz]，是文本形式 ≅ F ℤ 的表示对象。透明度：五个 [Defined]，没有 [Qed]，按注释外的标记计数；[RMod_Forget_Ab_additive]、[RMod_Forget_equiv]、[HomAbForget_additive]、[coext_representable] 和 [Ab_Forget_Id_equiv]。每个其他常数都是项 [Definition] 或 [Example]。翻转：参见公理和测量。

 ** 宇宙，已测量由 [About] 在 [Set Printing Universes] 下，stdlib 范围（[compose.u0]、[Projections.u0]、[prod_rect.u0]、[ID.u0]、[Fin.case0.u0]、[VectorDef.*]，……）被省略，除了 [eq_rect_r]，如下归属。[RMod@{o x a p c} : RingObject@{a c p} → Category@{o c c}] 命名环的（辅助、承载、证明）宇宙，[RMod] 的对象宇宙 o 及其第二宇宙 x；同态位于承载 c。[Ab@{b c}] 是目标，其对象宇宙 b（文本形式中为 a）及其承载相同 c。[PreservesImageLimit@{o c b c pk c pa c}] 命名其范畴 [pk] 及其辅助槽 [pa]；其形状槽为 c。[Representable@{ra rt pa o c}] 命名 Representable 的两个自身宇宙 [ra rt]。watts_theorem@{c o x a pk pa ra rt +} :
 ∀ {R : 环对象@{c c c}} (T : (R模@{o x c c c} R)^op ⟶ 阿贝尔群@{a c}),
 加性函子@{o c a} T → 保持像极限@{o c a c pk c pa c}
 → 非截断@{c} → ∃ A : 对象 [RMod@{o x c c c} R] ,
 余同构阿贝尔群@{o c a} (R模_阿贝尔群增强@{x o c c c} R) A ≅ T
 watts_ex3@{a c p o x b g pk pa ra rt +} :
 ∀ {R : 环对象@{a c p}} (T : R模@{o x a p c} R ⟶ 阿贝尔群@{b c}),
 加性函子@{o c b} T → 保持像极限@{o c b c pk c pa c}
 → 余生成器@{g o c} (R模@{o x a p c} R) → 非截断@{c}
 → ∃ A, 同态阿贝尔群@{o c b} (R模_阿贝尔群增强@{x o a p c} R) A ≅ T
 watts_ex3_QZ@{r o x b pk pa ra rt +} :
 ∀ {R : 环对象@{r r r}} (T : R模@{o x r r r} R ⟶ 阿贝尔群@{b r}),
 … → 注入阿贝尔群@{o r} QZ@{r r r _}
 → QZ_族_余生成@{o r _ o _} → 非截断@{r}→ ∃ A, …
 （[QZ_family_cogenerates] 的第三个槽位，即单元素族的索引宇宙，被保留空位，由载体 r 限定：SAFT 的 [c <= so]）显式宇宙实例只写在常量上，这些常量的实例长度在树的其他地方已有先例（[RMod]、[Ab]、[Sets]、[RingObject]、[AbObject]、[Cogenerator]、[Representable]、[PreservesImageLimit]、[Untruncate]）；[ContinuousFunctor]、[QZ]、[RMod_Forget]、[RMod_Forget_Ab]以及这个文件自身的可扩展[HomAbForget]则通过类型说明来访问，以便在另一个 Coq 版本上不同的实例长度也不会拒绝它们。此文件中没有常量包含宇宙方程：在 [About] 的输出中搜索所有二十七个约束块，每一个都通过其完全限定名进行查询，寻找“ = ”时没有找到（在一个临时文件上运行时，同样的搜索找到了一个定义的方程，该定义使用了 [F : D ⟶ C] 和 [U : C ⟶ D]，以及 [Adjunction] 自身的 [About]）。在整个输出中，“ = ”仅出现在 [eq_refl] 的读取回写语句 [watts_theorem_obj]、[watts_theorem_to_at] 和 [watts_ex3_QZ_cogenerator] 中。每个继承了什么，以及从哪里继承的：- 文本形式中的 [RingObject@{c c c}] 及其证明。受 [RModop_Cogenerator] 强制，其环是 [RingObject@{c c c}]，因为 [Ring_RMod R] 携带 R 自身的交换群（Instance/Mod/WellPowered.v 已对此进行测量）。这里：[watts_theorem_sets] 在 [R : RingObject@{a c p}] 处的主体，声明了 [c < a]，被拒绝，提示“术语 'R' 的类型为 'RingObject@{a c p}'，而期望类型为 'RingObject@{<1> <1> <1>}'（宇宙不一致：无法强制 c = a，因为 c < a）”；相同主体在未声明约束的情况下被接受，并读回 [a = c]，[a = p]。练习 3 保持了环的三个宇宙分离；
 [watts_ex3_QZ] 位于 [RingObject@{r r r}]，由 [CoextObj] 自身识别（Instance/Mod/Coextension.v），而它的两个 ℚ/ℤ 前提的 [Ab] 位于 RMod 的对象宇宙 o，如 [QZ_injective_cogenerator] 自身的回读所示，在本文件的导入下打印 [@Injective Ab@{a r} QZ@{r r r u0}] 在 [Cogenerator@{c a r} (RMod@{a u r r r} R)] 旁边（[Injective] 是 [Projective] 在对偶范畴的符号）。 - [Set < c]：来自 [RMod_WellPowered_untruncate] 和 [RMod_CoWellPowered_untruncate]（它们的 [Prop] 值索引位于 [max(Set+1, c)]）以及来自 [RMod_Cocomplete_via_GAFT]（GAFT 的索引位置）。因此，载体位于 [Set] 的环被排除；[Int_Ring] 是宇宙多态的，并且在 [Set] 之上满足它。 - 集合级别是 [pa]。[Ab_Forget@{b pa c}] 落在 [Sets@{c pa}] 上，即连续性假设的辅助槽。该识别是由路径强制的： [PreservesImageLimit_Continuous] 将 [pa] 转换为 [ContinuousFunctor] 的第十槽，[continuous_compose] 在 T 和 [Ab_Forget] 之间共享该槽，而 [Ab_Forget_creates_continuous] 的第十槽等于其 [Sets] 对象宇宙。对于 [Ab_Forget] 和 [pa < s] 声明了一个单独的 [s] 后，[watts_theorem_sets] 的主体被拒绝，期望 "Representable@{ra rt s o c} (Ab_Forget@{a s c} ◯ T)" 对比主体的 "Representable@{<1> <2> pa o c} (Ab_Forget@{a pa c} ◯ T)" （宇宙不一致：无法强制 pa = s 因为 pa < s）；因此常量在该层级使用 [pa]。- 严格和非严格的 [eq_rect_r] 边界：在每个基于 SAFT 的常量上，[c < eq_rect_r.u0] 和 [c <= eq_rect_r.u1]，从 [continuous_Set_functor_representable] 和 [SAFT_wellpowered]（其回读带有 [h < eq_rect_r.u0]，根据 Corollaries.v 的头部归因于 Adjunction/SAFT/InitialObject.v 的 [complete_pullbacks]），以及 [x <= eq_rect_r.u0]，即那些常量的 [t <= eq_rect_r.u0]（来自 #452 的 [special_initial_object_wellpowered_at]，根据同一头部）在 [t := x]，即 [WellPowered@{o c c o x}] 的第五个槽。- 见证人。[HomAbForget] 的中间 [Ab] 位于 RMod 的对象宇宙 o。针对组合的连续性证明在其自身的 [m] 上与 [Ab] 声明的 [o < m] 被拒绝，
 “…（无法统一 "@padd_respects _ (@abenriched_preadditive _ (@AbEnriched_op@{m c} Ab@{m c} Ab_AbEnriched@{m <1> c})) A (fobj [(RMod_Forget_Ab@{x o m c c c} R)^op]  (fobj [K]  x0))" 与 "@padd_respects _ (@abenriched_preadditive _ (@AbEnriched_op@{o c} Ab@{o c} Ab_AbEnriched@{o <1> c})) A (fobj[(RMod_Forget_Ab@{x o o c c c} R)^op] (fobj [K]  x0))")”（<1> 是草稿编译生成的一个宇宙）；没有声明约束的相同语句被接受，并回读为 [o = m]。原因是 [coex_adjunction]，其左伴随在 RMod 的对象宇宙中落入 [Ab]（它的回读：[RMod_Forget_Ab@{u3 u2 u2 u u1 u0} R ⊣ Coextension@{u u0 u1 u2 u3} R]）。[HomAbForget_continuous] 的第十个槽是 x：命名为 [k6]，并且 [x < k6] 声明证明被拒绝，同时 [k6 < x] 也声明它被拒绝，均带有“无法统一 Functor.Compose_obligation_1 J (RMod R)^op Ab (HomAbForget R A) K”和“Functor.Compose_obligation_1 J (RMod R)^op Ab (CoHomAb Ab_AbEnriched A ◯ (RMod_Forget_Ab R)^op) K”。因此，在该见证处，文本形式的 Sets 层级是 x，并且 [coext_representable] 在 [Sets@{c x}] 上述为在 [repr_unique_iso] 中满足它。同样在练习3的证人中，[RMod_Forget_Ab_creates_continuous] 的第十个插槽位于 RMod 的 x，而 [rmod_representable] 落在 [Sets@{c x}] 中；两者都未显示在 [watts_ex3_forget_obj] 的类型中。- 有两个方程出现在草稿中，但不是强制的，每个方程通过将草稿附加到整个文件的副本中测量，并且声明了相反的顺序：[x = s] 出现在 [watts_ex3] 的草稿中（带有 [ContinuousFunctor] 假设，[Ab_Forget@{b s c}] 被赋值一次，并且在 [exact] 中第二次阐述 [watts_ex3_sets]），在声明 [s < x] 后被接受；以及 [x = s] 出现在 [coext_representable] 的另一个 [Sets@{c s}] 草稿中，在声明 [x < s] 后被接受。两者都来自阐述，而不是来自供体；已落定的常数通过一次赋值出现 [watts_ex3_sets]，并命名它们所需的级别。- 常数通过 [watt_at_forget] 添加，并在第 5 节 [watt_at_forget] 位于 [RingObject@{c c c}]，因为其表示对象 [Ring_RMod R] 是（崩溃实例/模块/WellPowered.v 测度），并且回读 [HomAb@{o c b} (RMod_AbEnriched@{x o c c c} R) (Ring_RMod@{c c c} R) ≅ RMod_Forget_Ab@{x o b c c c} R]。[ab_hom_Z_iso@{a c +}] 在两端都落入 [Ab@{a c}]；自由群自身的宇宙和单点集的宇宙保留推理，通过 [FreeAb] 和 [SetsOne] 无需实例即可达成。[watts_theorem_Fz] 承载 [watts_theorem] 的命名宇宙。- 第 6 节 [watts_theorem_via_unconditional@{c o x a pk pa +}] 承载 [watts_theorem] 的命名宇宙，但 [ra rt]。[watts_unconditional_coext] 及其  [_2a] 实例化了 [watts_theorem_unconditional@{c c c o x b x …}]：环被 [CoextObj] 崩溃，并且该定理在 x 处的集合级别为 [HomAbForget_continuous] 的第十个槽，如上所述。[Ab] 的 [HomAbForget] 在 [b] 的两个语句中都被注明；留给推理它被设置为 x，并且 [About] 回读 [HomAbForget@{c o x x}]，绑定器的 b 未使用。

 ** 非空性练习 3 在 T :=  [RMod_Forget_Ab R] : [watts_ex3_forget R G U]，其连续性是 #449 的创建 ([RMod_Forget_Ab_creates_continuous])，不是一个伴随，因此见证不是循环的。它的表示对象是 ≅ [Ring_RMod R] ([watts_ex3_forget_obj]，在 [RingObject@{c c c}])：[repr_induced_iso] 对应 Instance/Mod/Representable.v 的 [rmod_representable]，沿着 [RMod_Forget R] 和 [Ab_Forget ◯ RMod_Forget_Ab R] 之间的恒等分量同构 [RMod_Forget_equiv]。它继承了 [G] 和 [U]。在 T := [HomAbForget R A] 处的文本形式为 M ↦ Hom_Ab(U M, A)，对于任意阿贝尔群 A：[watts_theorem_coext R A U]。可加性为 [HomAbForget_additive]；连续性为 [HomAbForget_continuous]，由 [RMod_Forget_Ab R] ^op 的复合而成——连续是因为 [RMod_Forget_Ab R] 是一个左伴随，[coex_adjunction]，通过 [Opposite_Adjunction] 和 [right_adjoint_Continuous] 读取——具有 [CoHomAb_continuous]。它的表示对象是 ≅ [CoextObj R A] ([watts_theorem_coext_obj])：[repr_unique_iso] 对 [coext_representable]，其分量是共扩展伴随本身的 Hom 双射，在 (RMod R)^op 中读取并通过 [Isomorphism_Opposite] 带回；并且 ≅ [HomZL R_R A]，即练习 2(a) 的 hom_ℤ(R, A) ([watts_theorem_coext_obj_2a]，通过 HomTensor.v 的 [homzl_coext_iso])。因此，Mac Lane 的 C 在该 T 处可以被识别为 hom_ℤ(R, A)（同构意义下）。它继承了 [U]，并且没有其他内容。这两个定理的每一个证人都继承了 [Untruncate]，它没有树中的居民，因此两个定理在树中都没有无条件实例。文本形式的证人通过 Instance/Mod/Watts/Unconditional.v 的定理在本文件的第 6 节中有一个无条件对应：[watts_unconditional_coext]（≅ [CoextObj R A]）和 [watts_unconditional_coext_2a]（≅ [HomZL R_R A]）。[watt_at_forget] 既不是任一定理的实例，而是它们所基于的加法升级的实例，在遗忘函子处，并且它不需要任何东西：在该 T 点上的练习 3 结论，无需特殊伴随函子定理。

 ** 公理与测量[Print Module Category.Instance.Mod.Watts] 列出了二十七个常量，没有 [Program] 义务（该文件未使用 [Program]）；每个在其全限定名称下的 [打印假设] 中报告“在全局上下文下关闭”。
 FLIPS：将五个 [Defined] 中的每一个在整个文件的副本中单独转换为 [Qed]；[coext_representable] 是承重的（其代表对象必须减少为 [CoextObj R A] 才能让 [watts_theorem_coext_obj] 类型检查，并且使用该常量及其在翻转副本中移除的 [_2a] 测量时，对 [watts_unconditional_coext] 也是如此），其他四个重新编译为 [Qed]；它们像 Functor/Representable/Additive.v 的 [HomAb_additive] 一样保持数据透明。[make todo] 在此文件中未更改。

 ** 未交付没有无条件协变形式：练习 3 仅在 [Untruncate] 上交付，以及 RMod R 的一个余生成元，而树中没有项在大小 [cogen_prod] 下提供（无条件 [RMod_Cogenerator_large] 很大，并且 Instance/Mod/Cogenerator.v 的元定理显示了书中的 ℚ/ℤ 是经典的）。树中没有任何内容证明任一必要假设：这里的 SAFT 路径消耗了两者，没有尝试其他通向协变形式的路径，并且在没有 [Untruncate] 的情况下，[RMod R] 在 pin 上的良好有势性既未构建也未被反驳。没有 [Untruncate] 的逆变形式是 Instance/Mod/Watts/Unconditional.v 的，通过 GAFT 具有显式解集，并且第 6 节使用了它。没有自由阿贝尔群在一点上的同构与 Instance/Ab/Free.v 中的 [ab_int] 对应，所以第 5 节的 ℤ 是 [FreeAb SetsOne]，而不是 [Int_Ring] 的整数；并且 [watts_theorem_Fz] 仅比较对象，没有通过 [ab_hom_Z_iso] 的 Ab 级同构 CoHomAb (F ℤ) ≅ T（这将需要 [CoHomAb] 对其对象保持函子性）。文本形式仅在 [RingObject@{c c c}] 处。没有 Functor/Representable.v 中的 [repr_unique_iso] 之外的唯一性。没有 Eilenberg–Watts 张量形式（一个余连续加法模 R → 模 S 的函子是 − ⊗_R N）并且没有双模值版本。代表对象在 T 中没有自然性。没有注册 [Instance]。上述引用的拒绝是在该整个文件的草稿副本中测量的，而 Test/ProbeWatts454.v 将它们归入其自己的导入列表：[eq_refl] 对 [watts_ex3_forget] 的对象的拒绝作为其 N16；[watts_theorem_sets] 的主体在 [c < a] 作为 N17（剥离至 [RModop_Cogenerator] 作为 N18）；Sets 层级，在 [pa < s] 和 [s < pa]，作为 N19 和 N29；[HomAbForget_continuous] 的主体与证人的 [Ab] 在 m，在 [o < m] 和 [m < o]，作为 N31 和 N32（其第一个因子作为 N20 和 N30）；以及该主体在第十槽 k6，在 [x < k6] 和 [k6 < x]，作为 N33 和 N34（常数本身作为 N21 和 N22）。它的控制 [p454_sets_apart_free]、[p454_ex3_twice]、[p454_hafc_body_at_o] 和 [p454_hafc_body_at_x] 重申了被接受的形式，而其 N23 引脚通过转换表示对象不是 F ℤ，同时 Adjunction/GAFT.v 的 [GAFT]，在两边停止归约时，是不透明的。它没有在单独的 [Sets@{c s}] 上固定 [coext_representable] 的草稿，这是一个完整的证明。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Projective.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Character.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Instance.Mod.HomTensor.
Require Import Category.Instance.Mod.Cogenerator.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mod.Watts.Unconditional.

Generalizable All Variables.

(* * ** 1. The forgetful functor is additive / * ** 1. 忘记函子是加性的 *)

Definition RMod_Forget_Ab_additive@{a c p o x b +} (R : RingObject@{a c p}) :
  @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c} (RMod_AbEnriched R)
    Ab_AbEnriched (RMod_Forget_Ab R).
Proof. constructor. intros x y f g m; simpl; reflexivity. Defined.

(* * ** 2. Watts' theorem, the book's text form / * ** 2. 瓦特定理，书中的文字形式 *)

(*
 SAFT at (RMod R)^op: complete because RMod R is cocomplete, cogenerated
 by R, well-powered because RMod R is co-well-powered under [U].  The
 continuity of [Ab_Forget ◯ T] is T's composed with [Ab_Forget]'s; the
 Sets level [pa] is forced (the header's UNIVERSES). 

 --------
 在 (RMod R)^op 上的 SAFT：因为 RMod R 是余完备且以 R 共生成而完备，且因为在 [U] 下 RMod R 是余良有幂的，所以是有幂的。[Ab_Forget ◯ T] 的连续性是 T 与 [Ab_Forget] 的复合；Sets 级别的 [pa] 是强制的（标题的 UNIVERSES）。
*)
Definition watts_theorem_sets@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* The book's first step, verbatim: T itself has a left adjoint. / 书的第一步，逐字：T 本身有一个左伴随。 *)
Definition watts_theorem_adjoint@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { F : Ab@{a c} ⟶ (RMod@{o x c c c} R)^op & F ⊣ T } :=
  SAFT_wellpowered T (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    contT (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(*
 The theorem: T ≅ hom_R(−, A) as Ab-valued functors.  The representation
 enters ONCE, ascribed, so that no second elaboration of it adds a
 universe equation (the header's UNIVERSES). 

 --------
 定理：T ≅ hom_R(−, A) 作为 Ab 值函子。表示只出现一次，被赋予，因此没有第二次阐述会增加宇宙方程（标题的 UNIVERSES）。
*)
Definition watts_theorem@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  @watt_ab_repr ((RMod R)^op)
    (LocallyPropositional_op (RMod_LocallyPropositional R))
    (AbEnriched_op (RMod_AbEnriched R)) T AF
    (watts_theorem_sets T contT U
       : Representable@{ra rt pa o c} (Ab_Forget ◯ T)).

(* The representing object IS the SAFT representation's. / 表示对象就是SAFT表示的对象。 *)
Example watts_theorem_obj@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = @repr_obj _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)) :=
  eq_refl.

(*
 ...and each component of the Ab-level isomorphism is the Sets-level
 representation's component, unchanged: additivity adds proofs, not
 data. 

 --------
 ...并且 Ab 级同构的每个组成部分都是集合级表示的组成部分，未发生变化：可加性增加的是证明，而不是数据。
*)
Example watts_theorem_to_at@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) (M : RMod@{o x c c c} R)
  (f : M ~{RMod@{o x c c c} R}~> projT1 (watts_theorem T AF contT U)) :
  cmon_map (transform[to (projT2 (watts_theorem T AF contT U))] M) f
    = transform[to (@represented _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)))] M f :=
  eq_refl.

(* * ** 3. Exercise 3, the covariant form / * ** 3. 练习 3，共变形式 *)

(* SAFT at RMod R: complete, well-powered under [U], cogenerated by [G]. / RMod R 上的 SAFT：在 [U] 下完全且功率充足，由 [G] 共生成。 *)
Definition watts_ex3_sets@{a c p o x b g pk pa ra rt +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T) (RMod_Complete R)
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    G (RMod_WellPowered_untruncate U).

Definition watts_ex3@{a c p o x b g pk pa ra rt +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) T } :=
  watt_ab_repr (RMod_AbEnriched R) T AF
    (watts_ex3_sets T contT G U
       : Representable@{ra rt pa o c} (Ab_Forget ◯ T)).

(*
 Exercise 3 as the book words it: "Use Exercise 2(b)".  The premises
 [HI] and [HC] are Exercise 2(b)'s "Q/Z ... is known to be an injective
 cogenerator of Ab", taken as hypotheses (Instance/Mod/Cogenerator.v). 

 --------
 练习 3 按书中的说法：“使用练习 2(b)”。前提 [HI] 和 [HC] 是练习 2(b) 中的“已知 Q/Z ... 是 Ab 的单射余生成元”，作为假设（Instance/Mod/Cogenerator.v）。
*)
Definition watts_ex3_QZ@{r o x b pk pa ra rt +}
  {R : RingObject@{r r r}} (T : RMod@{o x r r r} R ⟶ Ab@{b r})
  (AF : @AdditiveFunctor (RMod@{o x r r r} R) Ab@{b r}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o r b r pk r pa r}
             (RMod@{o x r r r} R) Ab@{b r} T)
  (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates)
  (U : Untruncate@{r}) :
  { A : RMod@{o x r r r} R &
    @Isomorphism (@Fun (RMod@{o x r r r} R) Ab@{b r})
      (HomAb (RMod_AbEnriched R) A) T } :=
  watts_ex3 T AF contT
    (snd (QZ_injective_cogenerator R HI HC)) U.

(* Only the cogenerating half of Exercise 2(b) is consumed: the cogenerator does not mention [HI]. / 只有练习 2(b) 的共生发电部分被消耗：共生发电器没有提到 [HI]。 *)
Example watts_ex3_QZ_cogenerator@{r o x +}
  {R : RingObject@{r r r}} (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates) :
  snd (QZ_injective_cogenerator R HI HC)
    = coext_cogenerator R (QZ_Cogenerator HC) := eq_refl.

(** ** 4. Witnesses / ** 4. 证人 *)

(* Exercise 3 at the forgetful functor, continuous by #449's creation. / 第3练习在遗忘函子上，由 #449 的创造连续。 *)
Definition watts_ex3_forget@{a c p o x b g +}
  (R : RingObject@{a c p}) (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) } :=
  watts_ex3 (RMod_Forget_Ab R) (RMod_Forget_Ab_additive R)
    (Continuous_PreservesImageLimit (RMod_Forget_Ab_creates_continuous R)) G U.

(*
 Instance/Mod.v builds [RMod_Forget R] directly rather than as the
 composite; the two agree up to identity components. 

 --------
 Instance/Mod.v 直接构建 [RMod_Forget R]，而不是作为复合体；两者在恒等分量上是一致的。
*)
Definition RMod_Forget_equiv@{a c p o x b +} (R : RingObject@{a c p}) :
  (RMod_Forget R : RMod@{o x a p c} R ⟶ Sets@{c x})
    ≈ (@Compose _ Ab@{b c} _ Ab_Forget (RMod_Forget_Ab R)
         : RMod@{o x a p c} R ⟶ Sets@{c x}).
Proof.
  exists (fun M => iso_id).
  intros M N f m; simpl. reflexivity.
Defined.

(*
 The additive upgrade with NO hypothesis: [rmod_representable], R
 representing the forgetful functor to sets, carried along
 [RMod_Forget_equiv] to a representation of [Ab_Forget ◯ RMod_Forget_Ab
 R], and upgraded.  The representing object is [Ring_RMod R] by
 conversion, so the statement names it. 

 --------
 没有假设的加性升级：[rmod_representable]，R表示到集合的遗忘函子，伴随将[RMod_Forget_equiv]携带到[Ab_Forget ◯ RMod_Forget_Ab R]的表示，并进行了升级。通过转换，表示对象是[Ring_RMod R]，所以语句给它命名。
*)
Definition watt_at_forget@{c o x b +} (R : RingObject@{c c c}) :
  @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
    (HomAb (RMod_AbEnriched R) (Ring_RMod R)) (RMod_Forget_Ab R) :=
  watt_ab_iso (RMod_AbEnriched R) (RMod_Forget_Ab R)
    (RMod_Forget_Ab_additive R)
    (Representable_transport (equiv_iso (RMod_Forget_equiv R))
       (rmod_representable R)).

(*
 The representing object is R itself, up to isomorphism: two
 representations of isomorphic functors. 

 --------
 表示对象就是 R 本身，到同构为止：两个同构函子的表示。
*)
Definition watts_ex3_forget_obj@{c o x b g +}
  (R : RingObject@{c c c}) (G : Cogenerator@{g o c} (RMod@{o x c c c} R))
  (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    ≅[RMod@{o x c c c} R] Ring_RMod R :=
  repr_induced_iso (rmod_representable R)
    (watts_ex3_sets (RMod_Forget_Ab R)
       (Continuous_PreservesImageLimit
          (RMod_Forget_Ab_creates_continuous R)) G U)
    (equiv_iso (RMod_Forget_equiv R)).

(*
 The text form's witness: M ↦ Hom_Ab(U M, A), contravariant in M.  The
 intermediate [Ab] is at RMod's object universe, where
 [coex_adjunction]'s left adjoint lands. 

 --------
 文本形式的见证：M ↦ Hom_Ab(U M, A)，在 M 中是逆变的。中间的 [Ab] 位于 RMod 的对象宇宙中，而 [coex_adjunction] 的左伴随落在此处。
*)
Definition HomAbForget@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) : (RMod@{o x c c c} R)^op ⟶ Ab@{b c} :=
  @CoHomAb Ab@{o c} _ Ab_AbEnriched A ◯ Opposite_Functor (RMod_Forget_Ab R).

Definition HomAbForget_additive@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{b c}
    (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}).
Proof.
  constructor. intros x y f g h m; simpl.
  apply (cmon_map_plus h).
Defined.

(*
 [RMod_Forget_Ab R] is a left adjoint, so its opposite is a right
 adjoint and continuous; [CoHomAb A] is continuous by
 Functor/Representable/Additive.v's [CoHomAb_continuous]. 

 --------
 [RMod_Forget_Ab R] 是左伴随，因此它的对偶是右伴随且连续的；[CoHomAb A] 通过 Functor/Representable/Additive.v 的 [CoHomAb_continuous] 是连续的。
*)
Definition HomAbForget_continuous@{c o x b +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Definition watts_theorem_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  { A' : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
      (CoHomAb (RMod_AbEnriched R) A')
      (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) } :=
  watts_theorem (HomAbForget R A) (HomAbForget_additive R A)
    (Continuous_PreservesImageLimit (HomAbForget_continuous R A)) U.

(*
 The coextension adjunction represents the witness directly: its hom
 bijection Hom_R(M, CoextObj R A) ≅ Hom_Ab(U M, A), natural in M.  The
 naturality square, evaluated at a ∈ N and r ∈ R, is R-linearity of f
 and g together with 1 · r ≈ r. 

 --------
 共延伸伴随直接表示证据：其同构 Hom_R(M, CoextObj R A) ≅ Hom_Ab(U M, A)，在 M 中是自然的。自然性平方，在 a ∈ N 和 r ∈ R 处的取值，是 f 和 g 的 R-线性，以及 1 · r ≈ r。
*)
Definition coext_representable@{c o x b ra rt +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  Representable@{ra rt x o c}
    (@Compose _ Ab@{b c} _ Ab_Forget
       (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})).
Proof.
  unshelve econstructor.
  - exact (CoextObj R A).
  - apply equiv_iso.
    exists (fun M => iso_sym (@adj _ _ _ _ (coex_adjunction R) M A)).
    intros M N f g; simpl.
    intros a r.
    pose proof (rm_map_smul f r a) as H1.
    assert (H2 : cmon_map (rm_hom g) (cmon_map (rm_hom f) (rm_smul N r a))
                 ≈ cmon_map (rm_hom g) (rm_smul M r (cmon_map (rm_hom f) a)))
      by (apply proper_morphism; exact H1).
    specialize (H2 (rig_one (ring_rig R))).
    pose proof (rm_map_smul g r (cmon_map (rm_hom f) a) (rig_one (ring_rig R)))
      as H3.
    simpl in H2, H3.
    symmetry.
    etransitivity; [exact H2|].
    etransitivity; [exact H3|].
    apply proper_morphism. apply rig_mul_one_l.
Defined.

(*
 SAFT's representing object at the witness is the coextension, up to
 isomorphism in RMod R... 

 --------
 SAFT 在见证者上的表示对象是共延拓，直到 RMod R 中的同构...
*)
Definition watts_theorem_coext_obj@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  projT1 (watts_theorem_coext R A U
           : { A' : RMod@{o x c c c} R &
               @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
                 (CoHomAb (RMod_AbEnriched R) A')
                 (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) })
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (repr_unique_iso (coext_representable R A)
       (watts_theorem_sets (HomAbForget R A)
          (Continuous_PreservesImageLimit (HomAbForget_continuous R A)) U)).

(* ...and so Exercise 2(a)'s hom_ℤ(R, A), the module [HomZL R_R A]. / ...因此练习 2(a) 的 hom_ℤ(R, A)，模 [HomZL R_R A] 。 *)
Definition watts_theorem_coext_obj_2a@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  projT1 (watts_theorem_coext R A U
           : { A' : RMod@{o x c c c} R &
               @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
                 (CoHomAb (RMod_AbEnriched R) A')
                 (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) })
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  iso_compose (iso_sym (homzl_coext_iso A)) (watts_theorem_coext_obj R A U).

(* * ** 5. Mac Lane's last step: the representing object is F ℤ / * ** 5. 麦克莱恩的最后一步：表示对象是 F ℤ *)

(*
 ℤ is read as the free abelian group on one point, [FreeAb SetsOne]
 (Instance/Ab/Free.v).  [Ab_Forget] and [Ab_Forget ◯ Id[Ab]] agree up to
 identity components. 

 --------
 ℤ 被读作一个点上的自由阿贝尔群，[FreeAb SetsOne]（Instance/Ab/Free.v）。[Ab_Forget] 和 [Ab_Forget ◯ Id[Ab] 在恒等分量上是一致的。
*)
Definition Ab_Forget_Id_equiv@{a c x +} :
  (Ab_Forget : Ab@{a c} ⟶ Sets@{c x})
    ≈ (@Compose _ Ab@{a c} _ Ab_Forget Id[Ab@{a c}]
         : Ab@{a c} ⟶ Sets@{c x}).
Proof.
  exists (fun M => iso_id).
  intros M N f m; simpl. reflexivity.
Defined.

(*
 Ab(ℤ, X) ≅ X, natural in X, as an isomorphism of Ab-valued functors:
 the additive upgrade at T := Id[Ab], fed the representation of
 [Ab_Forget] by the free group on one point that
 Adjunction/Representability/Sets.v reads off [free_ab_adjunction]. 

 --------
 Ab(ℤ, X) ≅ X，自然于 X，作为 Ab 值函子的一种同构：
 在 T := Id [Ab] 处的加法升级，提供了
 由一个点上的自由群表示 [Ab_Forget] 的表示，
 Adjunction/Representability/Sets.v 从 [free_ab_adjunction] 读取。
*)
Definition ab_hom_Z_iso@{a c +} :
  @Isomorphism (@Fun Ab@{a c} Ab@{a c})
    (HomAb Ab_AbEnriched (FreeAb SetsOne)) Id[Ab@{a c}] :=
  watt_ab_iso Ab_AbEnriched Id[Ab] Id_AdditiveFunctor
    (Representable_transport (equiv_iso Ab_Forget_Id_equiv)
       (representable_of_left_adjoint Ab_Forget free_ab_adjunction)).

(*
 C = F ℤ, up to isomorphism in RMod R, F being the left adjoint of
 [watts_theorem_adjoint]: FreeAb ⊣ Ab_Forget composed with F ⊣ T
 represents [Ab_Forget ◯ T] by F (FreeAb SetsOne), and two
 representations of one functor have isomorphic representing objects. 

 --------
 C = F ℤ，在 RMod R 中按同构算，其中 F 是左伴随于 [watts_theorem_adjoint] : FreeAb ⊣ Ab_Forget 与 F ⊣ T 的组合，表示 [Ab_Forget ◯ T] 由 F (FreeAb SetsOne) 表示，并且同一函子有两个表示时，它们的表示对象是同构的。
*)
Definition watts_theorem_Fz@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    ≅[RMod@{o x c c c} R]
  fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (@repr_unique_iso ((RMod R)^op) (Ab_Forget ◯ T)
       (representable_of_left_adjoint (Ab_Forget ◯ T)
          (Adjunction_Compose free_ab_adjunction
             (projT2 (watts_theorem_adjoint T contT U))))
       (watts_theorem_sets T contT U
          : Representable@{ra rt pa o c} (Ab_Forget ◯ T))).

(* * ** 6. What the unconditional theorem subsumes / * ** 6. 无条件定理所包含的内容 *)

(*
 [watts_theorem]'s statement, derived from Instance/Mod/Watts/
 Unconditional.v's [watts_theorem_unconditional] without the special
 adjoint functor theorem: the continuity hypothesis converted by
 [PreservesImageLimit_Continuous], and [U] carried but not consumed. 

 --------
 [watts_theorem] 的陈述，源自 Instance/Mod/Watts/Unconditional.v 的 [watts_theorem_unconditional] ，没有使用特殊伴随函子定理：由 [PreservesImageLimit_Continuous] 转换的连续性假设，以及 [U] 已携带但未消耗。
*)
Definition watts_theorem_via_unconditional@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  watts_theorem_unconditional T AF (PreservesImageLimit_Continuous contT).

(*
 The text form's witness M ↦ Hom_Ab(U M, A) with NO [Untruncate]: the
 module the unconditional theorem returns is the coextension, up to
 isomorphism in RMod R ([repr_unique_iso] against
 [coext_representable]). 

 --------
 文本形式的证人 M ↦ Hom_Ab(U M, A) 与 NO [Untruncate] ：该模无条件定理返回的是余扩展，最多在 RMod R 中同构（[repr_unique_iso] 与 [coext_representable] 对应）。
*)
Definition watts_unconditional_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (repr_unique_iso (coext_representable R A)
       (RModop_continuous_representable _
          (continuous_compose (HomAbForget_continuous R A)
             Ab_Forget_creates_continuous))).

(* ...and so Exercise 2(a)'s hom_ℤ(R, A), the module [HomZL R_R A]. / ...因此练习 2(a) 的 hom_ℤ(R, A)，模 [HomZL R_R A] 。 *)
Definition watts_unconditional_coext_2a@{c o x b +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  iso_compose (iso_sym (homzl_coext_iso A)) (watts_unconditional_coext R A).
