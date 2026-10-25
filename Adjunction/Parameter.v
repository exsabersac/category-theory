Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Construction.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Right.

Generalizable All Variables.

(*
Adjunction/Natural/Transformation.v is REQUIRED but deliberately NOT
   IMPORTED: importing it would shadow Theory/Adjunction.v's [unit] and
   [counit] (measured — with it imported, [Check @unit] returns the
   Id ⟹ U ◯ F transformation, so §C's and §E's existing [@counit ...] uses
   would silently change meaning).  The unit/counit-presentation class of §G
   is therefore reached through this alias, whose short name is swept and
   free tree-wide.  The cost is the [∹] notation, which does not export
   without the Import; the class is written [PAT.Adjunction_Transform]. 

--------
Adjunction/Natural/Transformation.v 是必需的，但故意不这样做
 导入：导入它会影响 Theory/Adjunction.v 的 [unit] 和
 [counit]（测量 - 导入后，[Check @unit] 返回
 Id ⟹ U ◯ F 变换，因此 §C 和 §E 现有的 [@counit ...] 使用
 会默默地改变意义）。 §G 的单位/单位表示类别
 因此，通过这个别名到达，其短名被扫除并且
 全树免费。 成本是 [∹] 表示法，不导出
 无需进口； 该类被编写为[PAT.Adjunction_Transform]。 
*)

Module PAT := Category.Adjunction.Natural.Transformation.

(** * Adjunctions with a parameter  / * 带参数的附加词*)

(* nLab: https://ncatlab.org/nlab/show/parametrized+adjoint
   nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
     book pp. 101-102: Theorem 3 and its proof.
   Riehl, "Category Theory in Context", 2nd ed., §4.3, p. 148, and §4.4
     Proposition 4.4.6: the same construction in the language of mates.

   Mac Lane's Theorem 3, quoted from the printed page (book p. 102):

     THEOREM 3 (Adjunctions with a parameter).  Given a bifunctor
     F : X × P → A, assume for each object p ∈ P that F(−, p) : X → A has a
     right adjoint G(p, −) : A → X, via an adjunction

         hom(F(x, p), a) ≅ hom(x, G(p, a)),                        (10)

     natural in x and a.  There is then a unique way to assign to each arrow
     h : p → p' of P and each object a ∈ A an arrow
     G(h, a) : G(p', a) → G(p, a) of X so that G becomes a bifunctor
     P^op × A → X for which the bijection of the adjunction (10) is natural
     in all three variables x, p, and a.  This assignment of arrows G(h, a)
     to ⟨h, a⟩ may also be described as the unique way to make G(h, −) a
     natural transformation conjugate to F(−, h).

   Mac Lane's proof runs through naturality in p, which is the commutativity
   of the square

       hom(F(x,p), a)  ≅  hom(x, G(p,a))
             ↑ F(x,h)*          ↑ G(h,a)_*
       hom(F(x,p'), a) ≅  hom(x, G(p',a))

   and he then says in terms: "This commutativity (for all a) states
   precisely that G(h,−) must be chosen as the conjugate to F(−,h).  By the
   previous theorem there exists a unique choice ...  For a second arrow
   h' : p' → p'', the uniqueness of the choice of conjugates shows for h'h
   that G(h'h, −) = G(h,−) ∘ G(h',−), so that G(−,a) is a functor and G a
   bifunctor, as required."

   WHAT IS DELIVERED HERE.  The hypothesis of the theorem is the record
   [ParametrizedAdjunction F], a family of right adjoints to the partial
   functors F(−,p) = [Partial_l F p].  [param_transform] is Mac Lane's
   F(−,h) : F(−,p) ⟹ F(−,p'), the transformation of left adjoints induced by
   an arrow of the parameter category; its component at x is the OTHER
   partial functor's action, fmap[Partial_r F x] h, and the interchange law
   of a bifunctor is exactly its naturality.  [pa_param_mate] is Mac Lane's
   G(h,−), defined as the CONJUGATE of F(−,h) and nothing else, so that the
   theorem's closing sentence ("may also be described as the unique way to
   make G(h,−) a natural transformation conjugate to F(−,h)") holds by
   construction rather than as a further comparison.

   [parametrized_right_adjoint_bifunctor] is Mac Lane's G : P^op × A → X.
   ITS TWO FUNCTOR LAWS ARE NOT RE-DERIVED.  Mac Lane's own argument is that
   the uniqueness of conjugates forces G(h'h,−) = G(h,−) ∘ G(h',−), and that
   argument is already discharged by name in Adjunction/Conjugate.v as
   [conj_mate_id] and [conj_mate_compose] (both of which are proved there by
   [conj_mate_uniq], i.e. by exactly the uniqueness Mac Lane appeals to).
   This file consumes those two corollaries; the only content added on top of
   them is the interaction with the second variable, which is naturality of
   the mate.

   NATURALITY IN ALL THREE VARIABLES is stated as three separate facts and
   then assembled.  Naturality in x and in a is nothing new — those are the
   [Adjunction] fields [to_adj_nat_l] and [to_adj_nat_r] at a fixed p, and
   they are re-exposed here under the names [pa_natural_x] and [pa_natural_a]
   so that a consumer sees all three in one place; the file does not claim
   them as new.  Naturality in p is the new one, and it is DEFINITIONALLY the
   conjugacy condition: [pa_square_is_Conjugate] records by [eq_refl] that
   the elementary square [pa_square] and Adjunction/Conjugate.v's [Conjugate]
   are the same type, so no comparison map appears anywhere.

   UNIQUENESS is the theorem's actual content, and it is stated over the
   ASSIGNMENT rather than over a type of bifunctors, which is what Mac Lane
   states ("There is then a unique way to assign to each arrow h ... and each
   object a ... an arrow G(h,a)").  [pa_assignment_unique] takes an arbitrary
   family G' of arrows, natural in a, whose square commutes, and concludes
   that every one of its values agrees with [pa_param_mate].  Its proof is
   [conj_mate_uniq] and nothing else.

   THE DUAL (§D) is Mac Lane's own next sentence, and it is NOT Theorem 3
   read backwards.  He writes: "Dually, given a bifunctor G : P^op × A → X
   where each G(p, −) has a right adjoint F(−, p), there is a unique way to
   make F a bifunctor X × P → A."  The hypothesis there is G(p,−) ⊣ F(−,p),
   so the PARTIAL FUNCTORS OF G ARE THE LEFT ADJOINTS, where in Theorem 3
   they were the right adjoints' partners, and the conclusion is COVARIANT in
   the parameter where Theorem 3's was contravariant.  The direction was
   confirmed by typechecking before any proof was written, and NO OPPOSITE
   CATEGORY IS NEEDED on the conclusion side: for h : p ~> p' in P the arrow
   h read in P^op runs p' ~> p, so [param_transform_r] supplies exactly the
   transformation of left adjoints G(p',−) ⟹ G(p,−) that [conj_mate]
   consumes, and it returns F(−,p) ⟹ F(−,p').  The alternative route through
   [Swap] is BUILT rather than argued about ([copa_swap_route]) and measured
   to cost strictly more: it needs a field-copy transport per parameter,
   because Partial_l (G ◯ Swap) p and Partial_r G p agree in both DATA fields
   on the nose and not as records, and the bifunctor it then produces has
   type P ∏ X ⟶ A — the two arguments in the OPPOSITE ORDER to the book's
   X × P → A.  The direct route needs neither.  The one genuinely new piece
   is [param_transform_r], the mirror of [param_transform] moving a
   bifunctor's FIRST argument instead of its second; the two relate different
   partial-functor families, so this is a construction and not an
   instantiation, and every §D result below mirrors a §C result line for
   line.

   §E IS THE CURRYING INSTANCE, and the reason it is here rather than in
   Structure/Cartesian/Closed.v is that that file's [Closed] class carries NO
   NATURALITY FIELD IN ANY VARIABLE — its fields are [exponent_obj],
   [exp_iso], the three derived transposes and the beta law — so naturality
   of currying in the parameter cannot even be phrased against the class.
   Theorem 3 supplies it: the family (− × p) ⊣ (−)^p is a
   [ParametrizedAdjunction] for ×(C), and the theorem then FORCES the arrow
   action of the exponential in the parameter to be the internal-hom action
   ([curry_param_mate_is_ihom], [curry_param_mate_is_internal_hom]).  The
   payoff is delivered as a STANDALONE equation in plain [Closed] vocabulary
   ([curry_natural_param], with its inverse-transpose mirror
   [uncurry_natural_param]), consumable without any record of this file; its
   right-hand side was READ OFF the mate rather than guessed, and
   [curry_natural_param_from_mate] obtains the very same statement by
   instantiating [pa_natural_p], so that derivation is machine-checked.
   Assembling the theorem's bifunctor at this instance recovers
   Functor/Hom/Internal.v's [InternalHomFunctor] — on objects at [eq_refl],
   on arrows up to ≈ ([curry_bifunctor_obj], [curry_bifunctor_fmap]).

   §F ANSWERS MAC LANE'S EXERCISE 2 AS A THEOREM.  The property of the unit
   corresponding to naturality of (10) in the parameter is DINATURALITY —
   the wedge condition — and it is delivered twice: elementarily as
   [pa_unit_dinatural], and packaged in Structure/Wedge.v's own class as
   [pa_unit_Wedge PA x : Wedge (UnitIntegrand PA x)], apex x and legs the
   units.  Its proof is a [symmetry] and then one application of
   Adjunction/Conjugate.v's
   [conjugate_to_unit] at §C's conjugate pair, so Exercise 2's answer is
   exactly the [ConjugateUnit] characterisation of conjugacy, which #394
   already carries by name; the counit's mirror is [pa_counit_extranatural],
   the [ConjugateCounit] characterisation at the same pair.
   Theory/Dinatural.v's [Dinatural] is NOT used and NOT required, for three
   measured reasons set out at the head of §F.

   §G IS THE UNIT/COUNIT PRESENTATION, and it is careful about what is new.
   The two triangle identities at a FIXED parameter are not new — they are
   Theory/Adjunction.v's [counit_fmap_unit] and [fmap_counit_unit], re-exposed
   with the parameter written out as [pa_triangle_left]/[pa_triangle_right],
   both proved by a bare [exact].  What is new is the parametrized record
   [ParametrizedAdjunctionTransform] and its equivalence with §A,
   [parametrized_adjunction_iff_transform], which applies
   Adjunction/Natural/Transformation/Universal.v's two passages pointwise in
   p.  Strengths are measured strict-first: the family of right adjoints and
   the unit and counit COMPONENTS survive at [eq_refl]; the whole record and
   the transposes do not, and what holds for the latter is [pa_pat_round_to]
   / [pa_pat_round_from] at ≈, each a bare [exact] of [to_adj_unit] /
   [from_adj_counit].

   §H IS RIEHL §4.4 PROPOSITION 4.4.6(iii), as an inhabitant of
   Adjunction/Right.v's own [AdjointOnTheRight] class and not a
   lookalike: [mutually_right_adjoint] is a RECORD LITERAL whose five fields
   are [mr_iso] and the four naturality lemmas above it, applied, with no
   tactic anywhere in it.  Riehl's Exercise 4.4.ii IS that
   proposition, so it is NOT separate work and nothing further is built for
   it.  The mirror hypothesis needs NO new record — [Partial_l (F ◯ Swap) x]
   and [Partial_r F x] agree in both DATA fields at [eq_refl], measured — and
   [mirror_family] packages a family stated in the natural [Partial_r F x ⊣
   H x] form, so the HYPOTHESIS a consumer supplies mentions no [Swap] —
   though the record's type still does.  Only TWO of the
   four naturality fields are proved directly; the other two are obtained by
   conjugating them with the isomorphism.

   §I, THE MODULE TENSOR-HOM (Mac Lane's own second motivating example,
   Mod_K(A ⊗_K B, C) ≅ Mod_K(A, Hom_K(B, C)) with parameter B), IS A FUTURE
   INSTANCE AND NOT A MISSING CATEGORY.  Measured, at this commit:
     - [ModTensor : RMod R ∏ RMod R ⟶ RMod R] EXISTS
       (Instance/Mod/Monoidal.v) and takes NO commutativity hypothesis,
       so [Partial_l ModTensor W] is already the endofunctor (− ⊗ W).
     - [HomMod] (Instance/Mod/Closed.v) is OBJECT-LEVEL — its type is
       ∀ R, (R commutative) → RModObject R → RModObject R → RModObject R —
       and its two arrow actions [ihom_post] and [ihom_pre]
       exist SEPARATELY.  That they are not assembled into a bifunctor is
       the donor's own disclosure; that NO FUNCTOR LAW is proved
       for either is a separate measurement of mine — the two names occur in
       exactly five non-comment places in that file, the four naturality
       lemmas [cur_natural_W]/[cur_natural_X]/[unc_natural_W]/[unc_natural_X]
       and one [Check], and no statement of the shape [ihom_post id ≈ id] or
       [ihom_post (k' ∘ k) ≈ ihom_post k' ∘ ihom_post k] exists.  So what is
       genuinely absent is the endofunctor (−)^W — [HomMod R Rcomm W] with
       [ihom_post] as its [fmap] — and the adjunction record on top of it.
     - That endofunctor is FIVE LINES AND RAISES ZERO OBLIGATIONS, and the
       adjunction is then a [:=] with no tactic:
       [Build_Adjunction' exp_iso_Mod cur_natural_V
       cur_natural_X].  Both were compiled out of tree, together with
       the resulting [ParametrizedAdjunction ModTensor] and Theorem 3's
       bifunctor at it, so this paragraph is a measurement and not a claim.
       Note also that [cur_natural_W] IS Mac Lane's naturality square
       in the parameter, with [ihom_pre j] already in the mate position.
     - THE ONLY REASON TO DEFER IS CLOSURE COST: requiring
       Instance/Mod/Closed.v and Instance/Mod/Monoidal.v takes this file's
       transitive in-project closure from 68 modules to 94, measured over
       .Makefile.coq.d.  An Adjunction/-level file should not pay 26 modules
       for one witness; the instance belongs beside the module categories.

   PRIOR ART, NARROWED — the catalogue issue's claim that "searches for
   parametrised, parameterised or two-variable adjunctions return nothing" is
   true of DECLARED CONSTANTS and false of the bare words, and the criterion
   is what settles it.  A case-insensitive sweep for
   parametri[sz]ed|parameteri[sz]ed|two.variable over *.v returns 39 files,
   every hit prose (e.g. Theory/DoubleCategory.v "parametrized spectra",
   Theory/Coq/Traversable.v "a parameterised comonad",
   Instance/EnsV.v "this file is parameterized by"); the same sweep
   restricted to declaration heads returns zero.  So no CONSTANT of this
   shape existed, which is the claim this file makes new.

   UNIVERSES, measured off BOTH the binder and the constraint block, because
   they disagree here.  Every constant binds X : Category@{u u0 u0},
   P : Category@{u1 u2 u2} and A : Category@{u3 u4 u4} — hom identified with
   proof in all three, expressed by REUSING the level variable in the BINDER,
   with no such equation in any block — while the blocks carry the equation
   u0 = u4, identifying X's and A's hom-and-proof levels.  All THREE object
   universes stay free (they occur in bounds only), and no constant carries a
   word-bounded Set.  Both identifications are INHERITED and neither is
   claimed unavoidable.  Attribution was probed with controls accepted at the
   very same levels: hom = proof has TWO independent donors, the PRODUCT of
   categories and [Adjunction], each rejected alone under Constraint ch < cp
   while @Functor Cu Cu is ACCEPTED there, so [Functor] is NOT a donor for
   it.  [Partial_l] is NOT a third and cannot be tested as one: its type is
   (B ∏ C) ⟶ D → obj[C] → B ⟶ D, so any application must form the product
   first and elaboration is refused there, never reaching [Partial_l] — the
   trap Test/ProbeParameter396.v's negative 15 exists to record.  And
   u0 = u4 needs no adjunction at all — the mere presence of functors in BOTH
   directions forces it, Xu ⟶ Au being accepted under Constraint xh < ah
   where Au ⟶ Xu is rejected.  Since [ParametrizedAdjunction] carries
   Partial_l F p : X ⟶ A and pa_right p : A ⟶ X, that second identification
   is forced by the record's own shape.

   §D's constants repeat that pattern exactly, with the letters permuted:
   P : Category@{u u0 u0}, A : Category@{u1 u2 u2}, X : Category@{u3 u4 u4}
   in the binder, and the block equation u2 = u4 identifying A's and X's
   hom-and-proof levels — again forced by functors running in both
   directions, since [CoParametrizedAdjunction] carries Partial_r G p : A ⟶ X
   and pa_left p : X ⟶ A.  §E's constants live over a SINGLE category and so
   carry no cross-category identification at all; the two standalone lemmas
   are the freest constants in the file — curry_natural_param@{u u0 u1} and
   uncurry_natural_param@{u u0 u1} have NO universe equation whatever in
   their blocks, only [Closed]'s own u0 < u1 and stdlib bounds.  Measured
   across fourteen [About] dumps spanning §B, §C, §D and §E, no constant in
   this file carries a word-bounded Set.

   §F, §G AND §H SPLIT IN TWO, and the split is worth knowing before writing
   against this file.  Everything is over the §C binder X : Category@{u u0
   u0}, P : Category@{u1 u2 u2}, A : Category@{u3 u4 u4}, so u0, u2 and u4
   are the three hom-and-proof levels.  The ELEMENTARY constants of §F and
   ALL of §G carry only the file's inherited u0 = u4 and leave P's level u2
   FREE — [pa_unit], [pa_counit], [pa_unit_dinatural],
   [pa_counit_extranatural], [ParametrizedAdjunctionTransform], [pat_of_pa],
   [pa_of_pat], [parametrized_adjunction_iff_transform] and both triangles.
   [UnitIntegrand] and [pa_unit_Wedge] carry u0 = u2 as well, so at them all
   three collapse to one; and the attribution is measured with a control
   accepted at the very same levels — under Constraint ph < xh the type
   (Pu^op ∏ Pu) ⟶ Xu IS ACCEPTED, while @Wedge Pu Xu H and the [Compose] of
   two functors through Pu^op ∏ Au are each REJECTED, so there are TWO
   INDEPENDENT DONORS and, in particular, THE WEDGE PACKAGING COSTS NOTHING
   EXTRA: merely forming the integrand already pays it.  §H collapses all
   three too, and there the cause is NOT [AdjointOnTheRight]: a probe aimed
   at that class never reaches it, stopping one line earlier at the SECOND
   functor direction — under Constraint ph < xh, Pu^op ⟶ Xu is accepted and
   Xu^op ⟶ Pu is rejected — so the collapse is forced by having functors in
   both directions between P and X before any class is formed, exactly as
   u0 = u4 is forced above.  [mirror_transport] and [mirror_family] are the
   exception on the other axis: they carry u2 = u4 and NOT u0 = u4, X's
   level staying free, since they mention Partial_r F x : P ⟶ A and
   U : A ⟶ P and no functor out of X.  No constant of §F, §G or §H carries
   a word-bounded Set (measured over twenty [About] dumps), and none of
   these identifications is claimed unavoidable.

   NOT DELIVERED, and the list is exhaustive as against the plan this file
   was built to:
     - THE REFUTATIONS ARE GUARDED, and not in this file: every strict
       form this header records as measured and REFUTED is pinned in
       Test/ProbeParameter396.v, which carries one instrument check and
       twenty negatives — twelve CONVERSION, two TYPING and six
       FORMABILITY, each classified by reading its whole error after
       stripping it and compiling it alone — with passing controls beside
       each.  This library file itself declares no refutation command, so
       every negative lives in the probe; renaming any of the twelve
       library constants a negative names breaks the probe at a control
       line, which was simulated twelve times over.
     - NO [Cowedge] INSTANCE for the counit.  [pa_counit_extranatural] is
       delivered elementarily only.  Structure/Wedge.v defines
       [Cowedge F := @Wedge (C^op) (D^op) (F^op)], so packaging it needs the
       opposite of the integrand and of A, and the wedge-side universe
       collapse would be paid again; neither was attempted.
     - NO END OR COEND.  Nothing says either wedge is universal, so no
       relation to Structure/End.v or Structure/Coend.v is claimed.
     - NO [Dinatural] READING of the unit (see §F for the three measured
       reasons), and no relation between [Wedge] and [Dinatural] is shipped.
     - NO NATURALITY IN c of §H's isomorphism, and no functor
       A ⟶ (whatever a two-variable adjunction would live in): [c] is a
       section parameter, fixed.
     - NO CONVERSE to §H — nothing says that a mutually-right-adjoint pair
       of bifunctors arises from a bifunctor F with both pointwise families.
     - NO [AdjointOnTheLeft] reading, and no relation to Adjunction/Right.v's
       [MutuallyRightAdjoint] record.
     - NO CONCRETE INSTANCE of §F, §G or §H at a named category.  §E's
       currying instance is the file's only concrete witness and it is not
       run through these three sections; the module tensor-hom of §I is
       measured to be reachable but is deliberately not shipped.
     - NO WHOLE-RECORD round trip for §G, and no setoid on either
       parametrized record, so [parametrized_adjunction_iff_transform] is a
       biconditional and NOT an isomorphism of types.
     - NOTHING IS REGISTERED AS AN [Instance].

   DIVERGENCES from the names pinned in the catalogue issue's Verification
   block: NONE.  [ParametrizedAdjunction] (§A) and
   [parametrized_right_adjoint_bifunctor] (§C) are delivered under exactly
   those names.  Every other name in this file is its own. *)

(** ** A. The hypothesis: a family of right adjoints to the partial functors  / ** A. 假设：偏函子的右伴随族*)

Section ParametrizedAdjunction.

Context {X P A : Category}.

(*
Mac Lane's hypothesis, packaged.  [pa_right p] is his G(p,−) : A → X and
   [pa_adj p] is the adjunction (10) at the parameter p; naturality of (10)
   in x and in a is carried by the [Adjunction] record itself.  Note that
   [pa_right] is a bare FUNCTION of objects of P: the whole point of the
   theorem is that its action on ARROWS of P is then forced, so it must not
   be assumed here. 

--------
麦克莱恩的假设，已打包。 [pa_right p] 是他的 G(p,−) : A → X 且
 [pa_adj p] 是参数 p 处的与 (10) 相加； (10) 的自然性
 in x 和 in a 由 [Adjunction] 记录本身携带。 请注意
 [pa_right] 是 P 对象的一个裸函数：整个点
 定理是它对 P 的箭头的作用是被迫的，所以它不能
 此处假设。 
*)

Record ParametrizedAdjunction (F : X ∏ P ⟶ A) := {
  pa_right : P → (A ⟶ X);
  pa_adj (p : P) : Partial_l F p ⊣ pa_right p
}.

End ParametrizedAdjunction.

Arguments ParametrizedAdjunction {X P A} F.
Arguments pa_right {X P A F} _ _.
Arguments pa_adj {X P A F} _ _.

(** ** B. The transformation of left adjoints induced by a parameter arrow  / ** B. 参数箭头引发的左伴随变换*)

Section ParamTransform.

Context {X P A : Category}.
Context (F : X ∏ P ⟶ A).

(*
Mac Lane's F(−,h).  Its component at x is the action of the OTHER partial
   functor F(x,−) on h, so the two partial-functor families of one bifunctor
   supply each other's data; naturality is the interchange law, both sides
   normalising to bimap f h. 

--------
麦克莱恩的 F(−,h)。 它在 x 处的分量是 OTHER 部分的作用
 h 上的函子 F(x,−)，因此一个双函子的两个部分函子族
 互相提供数据； 自然性是交换法则，双方
 归一化为 bimap f h。 
*)

Program Definition param_transform {p p' : P} (h : p ~> p') :
  Partial_l F p ⟹ Partial_l F p' := {|
  transform := fun x => fmap[Partial_r F x] h
|}.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.

(* The component identification, at Leibniz equality, in both spellings.  / 两种拼写中莱布尼茨等式下的组件标识。*)

Example param_transform_component {p p' : P} (h : p ~> p') (x : X) :
  transform[param_transform h] x = fmap[Partial_r F x] h := eq_refl.

Example param_transform_component_bimap {p p' : P} (h : p ~> p') (x : X) :
  transform[param_transform h] x = @bimap X P A F x x p p' id h := eq_refl.

Lemma param_transform_respects {p p' : P} (h h' : p ~> p') :
  h ≈ h' → param_transform h ≈ param_transform h'.
Proof. intros E x; simpl; now rewrite E. Qed.

(*
At the identity of the parameter the component is already the identity
   transformation's, on the nose: both sides are the literal term
   bimap[F] id id, so nothing is being rewritten away here. 

--------
在参数的身份处，组件已经是身份
 变换，在鼻子上：两边都是字面意思
 bimap[F] id id，因此这里没有任何内容被重写。 
*)

Example param_transform_id_component {p : P} (x : X) :
  transform[param_transform (id[p])] x
    = transform[@nat_id X A (Partial_l F p)] x := eq_refl.

Lemma param_transform_id {p : P} : param_transform (id[p]) ≈ nat_id.
Proof. intro x; simpl; reflexivity. Qed.

Lemma param_transform_comp {p p' p'' : P}
      (h : p ~> p') (h' : p' ~> p'') :
  param_transform (h' ∘ h) ≈ param_transform h' ∙ param_transform h.
Proof. intro x; simpl; apply bimap_comp_id_left. Qed.

End ParamTransform.

Arguments param_transform {X P A} F {p p'} h.

(** ** C. Theorem 3  / ** C、定理3*)

Section Theorem3.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).

Notation "'G'" := (pa_right PA) (only parsing).

(*
The transpose of the adjunction (10) at the parameter p, written out.  The
   [Adjunction] record's [adj] field takes its two functors implicitly and
   they cannot be recovered from an argument of type F (x, p) ~> a — that is
   a higher-order unification — so every transpose below names them. 

--------
附词 (10) 在参数 p 处的转置，写出。 的
 [Adjunction] 记录的 [adj] 字段隐式地采用其两个函子并且
 它们无法从 F (x, p) ~> a 类型的参数中恢复 - 也就是说
 高阶统一——所以下面的每个转置都会命名它们。 
*)

Definition pa_to (p : P) (x : X) (a : A) (k : F (x, p) ~> a) : x ~> G p a :=
  to (@adj A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) x a) k.

Definition pa_from (p : P) (x : X) (a : A) (g : x ~> G p a) : F (x, p) ~> a :=
  from (@adj A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) x a) g.

(* --- Mac Lane's G(h,−), as the conjugate of F(−,h) and nothing else ---  / --- Mac Lane 的 G(h,−)，作为 F(−,h) 的共轭，没有其他 ---*)

(*
[conj_mate A A' σ] takes σ : F' ⟹ F and returns U ⟹ U'.  With
   σ := param_transform F h for h : p' ~> p we have F' = Partial_l F p' and
   F = Partial_l F p, hence A := pa_adj PA p and A' := pa_adj PA p', and the
   result runs G p ⟹ G p' — CONTRAVARIANT in the parameter, which is the
   variance Mac Lane's G : P^op × A → X asks for. 

--------
[conj_mate A A' σ] 采用 σ : F' ⟹ F 并返回 U ⟹ U'。 与
 σ := param_transform F h for h : p' ~> p 我们有 F' = Partial_l F p' 并且
 F = Partial_l F p，因此 A := pa_adj PA p 和 A' := pa_adj PA p'，并且
 结果运行 G p ⟹ G p' — 参数中的逆变，即
 Mac Lane 的方差 G : P^op × A → X 要求。 
*)

Definition pa_param_mate {p p' : P} (h : p' ~> p) : G p ⟹ G p' :=
  conj_mate (pa_adj PA p) (pa_adj PA p') (param_transform F h).

(*
Mac Lane's closing sentence — "this assignment ... may also be described
   as the unique way to make G(h,−) a natural transformation conjugate to
   F(−,h)" — holds here by construction, not as a comparison. 

--------
麦克莱恩的结束语——“这个作业……也可以描述
 作为使 G(h,−) 成为自然变换共轭的独特方法
 F(−,h)”——此处通过构造成立，而不是作为比较。 
*)

Example pa_param_mate_is_conj_mate {p p' : P} (h : p' ~> p) :
  pa_param_mate h
    = conj_mate (pa_adj PA p) (pa_adj PA p') (param_transform F h)
  := eq_refl.

(* --- naturality in each of the three variables ---  / --- 三个变量各自的自然性 ---*)

(*
In x and in a there is nothing new: these ARE the [Adjunction] fields at a
   fixed parameter, re-exposed so that a consumer of this file sees all three
   naturality statements together. 

--------
在 x 和 a 中没有什么新内容：这些是 a 处的 [Adjunction] 字段
 固定参数，重新公开，以便该文件的使用者看到所有三个
 自然性陈述在一起。 
*)

Lemma pa_natural_x (p : P) {x y : X} {a : A}
      (k : F (y, p) ~> a) (g : x ~> y) :
  pa_to p x a (k ∘ fmap[Partial_l F p] g) ≈ pa_to p y a k ∘ g.
Proof. exact (to_adj_nat_l (Adjunction:=pa_adj PA p) k g). Qed.

Lemma pa_natural_a (p : P) {x : X} {a b : A}
      (f : a ~> b) (k : F (x, p) ~> a) :
  pa_to p x b (f ∘ k) ≈ fmap[G p] f ∘ pa_to p x a k.
Proof. exact (to_adj_nat_r (Adjunction:=pa_adj PA p) f k). Qed.

(*
Naturality in p is Mac Lane's square.  Stated elementarily first, so a
   reader sees the equation without unfolding any class. 

--------
p 中的自然性是麦克莱恩平方。 首先基本说明，所以
 读者无需展开任何类即可看到方程式。 
*)

Definition pa_square {p p' : P} (h : p' ~> p)
           (tau : G p ⟹ G p') : Type :=
  ∀ (x : X) (a : A) (k : F (x, p) ~> a),
    pa_to p' x a (k ∘ fmap[Partial_r F x] h) ≈ tau a ∘ pa_to p x a k.

(* And that elementary square IS the conjugacy condition, on the nose.  / 那个基本正方形就是鼻子上的共轭条件。*)

Example pa_square_is_Conjugate {p p' : P} (h : p' ~> p)
        (tau : G p ⟹ G p') :
  pa_square h tau
    = Conjugate (pa_adj PA p) (pa_adj PA p') (param_transform F h) tau
  := eq_refl.

Theorem pa_natural_p {p p' : P} (h : p' ~> p) :
  pa_square h (pa_param_mate h).
Proof.
  exact (conjugate_conj_mate (pa_adj PA p) (pa_adj PA p')
           (param_transform F h)).
Qed.

(*
The same square read through the INVERSE transposes.  Mac Lane draws (10)
   as a bijection, so both readings are his; Adjunction/Conjugate.v's
   [conjugate_iff_from] shows they agree, and here too that is a delta step
   away from [ConjugateFrom] rather than a new equivalence. 

--------
同一个方块读取逆转置。 麦克莱恩抽签 (10)
 作为双射，所以两个读数都是他的； 附加/共轭.v's
 [conjugate_iff_from] 表明他们同意，这也是一个增量步骤
 远离 [ConjugateFrom] 而不是新的等效项。 
*)

Definition pa_square_from {p p' : P} (h : p' ~> p)
           (tau : G p ⟹ G p') : Type :=
  ∀ (x : X) (a : A) (g : x ~> G p a),
    pa_from p' x a (tau a ∘ g)
      ≈ pa_from p x a g ∘ fmap[Partial_r F x] h.

Example pa_square_from_is_ConjugateFrom {p p' : P} (h : p' ~> p)
        (tau : G p ⟹ G p') :
  pa_square_from h tau
    = ConjugateFrom (pa_adj PA p) (pa_adj PA p') (param_transform F h) tau
  := eq_refl.

Theorem pa_square_iff_from {p p' : P} (h : p' ~> p) (tau : G p ⟹ G p') :
  pa_square h tau ↔ pa_square_from h tau.
Proof.
  exact (conjugate_iff_from (pa_adj PA p) (pa_adj PA p')
           (param_transform F h) tau).
Defined.

(* --- the two functor laws of G(−,a), by uniqueness of conjugates ---  / --- G(−,a) 的两个函子定律，通过共轭的唯一性 ---*)

(*
Mac Lane: "the uniqueness of the choice of conjugates shows for h'h that
   G(h'h,−) = G(h,−) ∘ G(h',−)".  That argument is Adjunction/Conjugate.v's
   [conj_mate_id] and [conj_mate_compose], both proved there by
   [conj_mate_uniq]; nothing is recomputed here. 

--------
Mac Lane：“结合物选择的独特性表明 h'h
 G(h'h,−) = G(h,−) ∘ G(h',−)”。 该参数是 Adjunction/Conjugate.v 的
 [conj_mate_id] 和 [conj_mate_compose]，均由以下证明：
 [conj_mate_uniq]； 这里没有重新计算任何内容。 
*)

Lemma pa_param_mate_respects {p p' : P} (h h' : p' ~> p) :
  h ≈ h' → pa_param_mate h ≈ pa_param_mate h'.
Proof.
  intro E; unfold pa_param_mate.
  apply conj_mate_respects, param_transform_respects, E.
Qed.

Lemma pa_param_mate_id {p : P} : pa_param_mate (id[p]) ≈ nat_id.
Proof.
  unfold pa_param_mate.
  rewrite (conj_mate_respects (pa_adj PA p) (pa_adj PA p) _ nat_id
             (param_transform_id F)).
  apply conj_mate_id.
Qed.

Lemma pa_param_mate_comp {p p' p'' : P} (h : p' ~> p) (h' : p'' ~> p') :
  pa_param_mate (h ∘ h') ≈ pa_param_mate h' ∙ pa_param_mate h.
Proof.
  unfold pa_param_mate.
  rewrite (conj_mate_respects (pa_adj PA p) (pa_adj PA p'') _ _
             (param_transform_comp F h' h)).
  apply (conj_mate_compose (pa_adj PA p) (pa_adj PA p') (pa_adj PA p'')).
Qed.

(*
the componentwise readings, which is the form the bifunctor's obligations
   consume 

--------
组件读数，这是双函子义务的形式
 消费 
*)

Lemma pa_param_mate_id_at {p : P} (a : A) : pa_param_mate (id[p]) a ≈ id.
Proof.
  transitivity (transform[@nat_id A X (G p)] a).
  - exact (pa_param_mate_id a).
  - apply fmap_id.
Qed.

Lemma pa_param_mate_comp_at {p p' p'' : P}
      (h : p' ~> p) (h' : p'' ~> p') (a : A) :
  pa_param_mate (h ∘ h') a ≈ pa_param_mate h' a ∘ pa_param_mate h a.
Proof. exact (pa_param_mate_comp h h' a). Qed.

(* --- Mac Lane's G : P^op × A → X ---  / --- Mac Lane 的 G : P^op × A → X ---*)

#[local] Obligation Tactic := idtac.

Program Definition parametrized_right_adjoint_bifunctor : P^op ∏ A ⟶ X := {|
  fobj := fun q => G (fst q) (snd q);
  fmap := fun q q' hk =>
            fmap[G (fst q')] (snd hk)
              ∘ pa_param_mate (unop (fst hk)) (snd q)
|}.
Next Obligation.
  intros [p a] [p' a'] [h k] [h' k'] [Eh Ek]; simpl in Eh, Ek.
  apply compose_respects.
  - now apply fmap_respects.
  - exact (pa_param_mate_respects (unop h) (unop h') Eh a).
Qed.
Next Obligation.
  intros [p a].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (pa_param_mate_id_at a) ]. }
  simpl.
  rewrite !fmap_id.
  now rewrite id_left.
Qed.
Next Obligation.
  intros [p a] [p' a'] [p'' a''] [h k] [h' k'].
  etransitivity.
  { apply compose_respects.
    - apply fmap_comp.
    - exact (pa_param_mate_comp_at (unop h') (unop h) a). }
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (naturality (pa_param_mate (unop h)) _ _ k').
Qed.

#[local] Obligation Tactic := program_simpl.

(* The bifunctor's two actions, read back at Leibniz equality.  / 双函子的两个动作，回读莱布尼茨等式。*)

Example pa_bifunctor_obj (p : P) (a : A) :
  fobj[parametrized_right_adjoint_bifunctor] (p, a) = G p a := eq_refl.

Example pa_bifunctor_fmap {p p' : P} {a a' : A}
        (h : p ~{P^op}~> p') (k : a ~> a') :
  fmap[parametrized_right_adjoint_bifunctor] ((h, k) :
        (p, a) ~{P^op ∏ A}~> (p', a'))
    = fmap[G p'] k ∘ pa_param_mate (unop h) a := eq_refl.

(*
In the parameter alone the action is the mate, up to the residue
   fmap[G p'] id that [fmap] leaves behind — [eq_refl] first, then the
   equation with the residue cleared.  Dropping the residue is NOT a
   conversion: [fmap_id] is a law field, so the strict form
     fmap[...] (h, id) = pa_param_mate (unop h) a
   is measured and REFUTED (a CONVERSION rejection, "cannot unify"), and
   only the ≈ form below holds.  That refutation is pinned in
   Test/ProbeParameter396.v as [p396_fmap_param_strict], with this file's
   own ≈ form beside it as the passing control. 

--------
仅在参数中，动作是配合，直到残差
 [fmap] 留下的 fmap[G p'] id — 首先是 [eq_refl]，然后是
 方程中残留物被清除。 丢弃残留物不是
 转换：[fmap_id]是一个法域，所以严格形式
 fmap[...] (h, id) = pa_param_mate (unop h) a
 被测量并被拒绝（转换拒绝，“无法统一”），并且
 只有下面的 ≈ 形式成立。 这个反驳被固定在
 Test/ProbeParameter396.v 为 [p396_fmap_param_strict]，此文件的
 自己的 ≈ 形式在旁边作为传球控制。 
*)

Example pa_bifunctor_fmap_param {p p' : P} (h : p ~{P^op}~> p') (a : A) :
  fmap[parametrized_right_adjoint_bifunctor]
      ((h, id[a]) : (p, a) ~{P^op ∏ A}~> (p', a))
    = fmap[G p'] (id[a]) ∘ pa_param_mate (unop h) a := eq_refl.

Lemma pa_bifunctor_fmap_is_mate {p p' : P} (h : p ~{P^op}~> p') (a : A) :
  fmap[parametrized_right_adjoint_bifunctor]
      ((h, id[a]) : (p, a) ~{P^op ∏ A}~> (p', a))
    ≈ pa_param_mate (unop h) a.
Proof. simpl; rewrite fmap_id; now rewrite id_left. Qed.

(*
Its two partial functors: in the second variable it IS the given family,
   on the nose in both actions — but only on the two DATA fields; the whole
   functor records are not equal, the three law fields of [Partial_r] being
   rebuilt Program obligations. 

--------
它的两个部分函子：在第二个变量中，它是给定的族，
 在两个动作中都在鼻子上——但仅在两个数据字段上； 整体
 函子记录不相等，[Partial_r] 的三个定律字段为
 重建计划义务。 
*)

Example pa_bifunctor_partial_r_obj (p : P) (a : A) :
  fobj[Partial_r parametrized_right_adjoint_bifunctor p] a = G p a := eq_refl.

Example pa_bifunctor_partial_r_fmap_unfold (p : P) {a a' : A} (k : a ~> a') :
  fmap[Partial_r parametrized_right_adjoint_bifunctor p] k
    = fmap[G p] k ∘ pa_param_mate (id[p]) a := eq_refl.

Lemma pa_bifunctor_partial_r_fmap (p : P) {a a' : A} (k : a ~> a') :
  fmap[Partial_r parametrized_right_adjoint_bifunctor p] k ≈ fmap[G p] k.
Proof.
  transitivity (fmap[G p] k ∘ pa_param_mate (id[p]) a); [ reflexivity |].
  rewrite (pa_param_mate_id_at a).
  now rewrite id_right.
Qed.

(* --- UNIQUENESS: the content of Theorem 3 ---  / ---唯一性：定理3的内容---*)

(*
Mac Lane states the uniqueness of the ASSIGNMENT h ↦ G(h,a), not of a
   bifunctor, so that is what is stated here: any family of arrows, natural
   in a and making the square commute, agrees with [pa_param_mate] at every
   argument.  The proof is [conj_mate_uniq]. 

--------
Mac Lane 陈述了赋值 h ↦ G(h,a) 的唯一性，而不是 a
 bifunctor，所以这就是这里所说的：任何箭头家族，自然
 在 a 中进行方形通勤，每次都与 [pa_param_mate] 一致
 论点。 证明是 [conj_mate_uniq]。 
*)

Theorem pa_param_mate_uniq {p p' : P} (h : p' ~> p)
        (tau : G p ⟹ G p') :
  pa_square h tau → ∀ a : A, tau a ≈ pa_param_mate h a.
Proof.
  intros H a.
  exact (conj_mate_uniq (pa_adj PA p) (pa_adj PA p')
           (param_transform F h) tau H a).
Qed.

Theorem pa_assignment_unique
        (Gh : ∀ (p p' : P) (h : p' ~> p), G p ⟹ G p')
        (Hsq : ∀ (p p' : P) (h : p' ~> p), pa_square h (Gh p p' h)) :
  ∀ (p p' : P) (h : p' ~> p) (a : A),
    Gh p p' h a ≈ pa_param_mate h a.
Proof.
  intros p p' h a.
  exact (pa_param_mate_uniq h (Gh p p' h) (Hsq p p' h) a).
Qed.

(* Existence and uniqueness in one statement, over the transformation.  / 存在性和唯一性在一个陈述中，在转变中。*)

Theorem pa_param_mate_universal {p p' : P} (h : p' ~> p) :
  ∃! tau : G p ⟹ G p', pa_square h tau.
Proof.
  exact (conjugate_unique_right (pa_adj PA p) (pa_adj PA p')
           (param_transform F h)).
Defined.

(*
And the bifunctor's arrow action is thereby determined: any assignment
   satisfying the square gives back exactly [fmap] of the bifunctor. 

--------
由此确定双函子的箭头动作：任何赋值
 满足平方正好返回双函子的 [fmap]。 
*)

Corollary pa_bifunctor_fmap_determined
        (Gh : ∀ (p p' : P) (h : p' ~> p), G p ⟹ G p')
        (Hsq : ∀ (p p' : P) (h : p' ~> p), pa_square h (Gh p p' h))
        (q q' : P^op ∏ A) (hk : q ~> q') :
  fmap[parametrized_right_adjoint_bifunctor] hk
    ≈ fmap[G (fst q')] (snd hk)
        ∘ Gh (fst q) (fst q') (unop (fst hk)) (snd q).
Proof.
  destruct q as [p a], q' as [p' a'], hk as [h k]; simpl.
  apply compose_respects; [ reflexivity |].
  symmetry.
  exact (pa_assignment_unique Gh Hsq p p' (unop h) a).
Qed.

End Theorem3.

Arguments pa_param_mate {X P A F} PA {p p'} h.
Arguments pa_square {X P A F} PA {p p'} h tau.
Arguments parametrized_right_adjoint_bifunctor {X P A F} PA.

(** ** D. The dual: a bifunctor whose partial functors are LEFT adjoints  / ** D. 对偶：一个双函子，其部分函子是 LEFT 伴随物*)

(* Mac Lane's dual sentence, quoted from the same page: "Dually, given a
   bifunctor G : P^op × A → X where each G(p, −) has a right adjoint F(−, p),
   there is a unique way to make F a bifunctor X × P → A."

   Read that sentence exactly.  The hypothesis is G(p,−) ⊣ F(−,p), so the
   PARTIAL FUNCTORS OF G ARE THE LEFT ADJOINTS here, where in Theorem 3 they
   were the right adjoints' partners; and the conclusion is COVARIANT in the
   parameter, where Theorem 3's was contravariant.  This is therefore not
   Theorem 3 read backwards.

   NO OPPOSITE CATEGORY IS NEEDED, and that is visible in the type of
   [parametrized_left_adjoint_bifunctor], which is X ∏ P ⟶ A with no [op] in
   it.  The mechanism: for h : p ~> p' in P the SAME arrow read in P^op runs
   p' ~{P^op}~> p, so [param_transform_r G h] is a transformation of LEFT
   adjoints G(p',−) ⟹ G(p,−) — which is what [conj_mate] consumes — and at
   the two adjunctions G(p,−) ⊣ F(−,p) and G(p',−) ⊣ F(−,p') it returns
   F(−,p) ⟹ F(−,p'), covariant.  That direction was confirmed by
   typechecking before any proof below was written.  The alternative route
   through [Swap] is built rather than argued about and is measured to cost
   more; see [copa_swap_route] and the comment above it. *)

(**
*** D.1 The mirror parameter transformation

    [param_transform] moves the SECOND argument of a bifunctor and so relates
    the [Partial_l] family; the dual needs the FIRST argument moved, relating
    the [Partial_r] family.  The two are genuinely different families of
    functors, not one family read twice, so this is a construction and not an
    instantiation; its component, its naturality proof and its three laws
    mirror §B line for line, with [bimap_comp_id_right] in place of
    [bimap_comp_id_left]. 

--------
*** D.1 镜像参数变换

 [param_transform] 移动双函子的第二个参数，因此关联
 [Partial_l] 系列； 第一个论点的双重需要，涉及
 [Partial_r] 系列。 两人是真正不同的家庭
 函子，没有一个家庭会读两次，所以这是一个构造而不是一个
 实例化； 它的组成部分、自然性证明和三大定律
 镜像 §B 线换线，用 [bimap_comp_id_right] 代替
 [bimap_comp_id_left]。 
*)

Section CoParamTransform.

Context {B C D : Category}.
Context (F : B ∏ C ⟶ D).

Program Definition param_transform_r {b b' : B} (m : b ~> b') :
  Partial_r F b ⟹ Partial_r F b' := {|
  transform := fun c => fmap[Partial_l F c] m
|}.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.
Next Obligation. now rewrite bimap_id_left_right, bimap_id_right_left. Qed.

Example param_transform_r_component {b b' : B} (m : b ~> b') (c : C) :
  transform[param_transform_r m] c = fmap[Partial_l F c] m := eq_refl.

Example param_transform_r_component_bimap {b b' : B} (m : b ~> b') (c : C) :
  transform[param_transform_r m] c = @bimap B C D F b b' c c m id := eq_refl.

Lemma param_transform_r_respects {b b' : B} (m m' : b ~> b') :
  m ≈ m' → param_transform_r m ≈ param_transform_r m'.
Proof. intros E c; simpl; now rewrite E. Qed.

Example param_transform_r_id_component {b : B} (c : C) :
  transform[param_transform_r (id[b])] c
    = transform[@nat_id C D (Partial_r F b)] c := eq_refl.

Lemma param_transform_r_id {b : B} : param_transform_r (id[b]) ≈ nat_id.
Proof. intro c; simpl; reflexivity. Qed.

Lemma param_transform_r_comp {b b' b'' : B}
      (m : b ~> b') (m' : b' ~> b'') :
  param_transform_r (m' ∘ m)
    ≈ param_transform_r m' ∙ param_transform_r m.
Proof. intro c; simpl; apply bimap_comp_id_right. Qed.

End CoParamTransform.

Arguments param_transform_r {B C D} F {b b'} m.

(** *** D.2 The dual hypothesis  / *** D.2 对偶假设*)

Section CoParametrizedAdjunction.

Context {P A X : Category}.

(*
[pa_left p] is Mac Lane's F(−,p) : X → A and [pa_coadj p] is the adjunction
   G(p,−) ⊣ F(−,p).  As in §A, [pa_left] is a bare function of objects: its
   action on arrows of P is what the theorem forces.  Note the partial functor
   is [Partial_r G p], not [Partial_l G p] — for G : P^op ∏ A ⟶ X it is the
   SECOND argument that is left free, so G(p,−) is the [Partial_r] family. 

--------
[pa_left p] 是 Mac Lane 的 F(−,p) : X → A，[pa_coadj p] 是附加
 G(p,−) ⊣ F(−,p)。 与 §A 中一样，[pa_left] 是对象的一个简单函数：它的
 P 箭头上的作用就是定理的力。 注意部分函子
 是 [Partial_r G p]，而不是 [Partial_l G p] — 对于 G : P^op ∏ A ⟶ X 它是
 第二个参数是自由的，所以 G(p,−) 是 [Partial_r] 系列。 
*)

Record CoParametrizedAdjunction (G : P^op ∏ A ⟶ X) := {
  pa_left : P → (X ⟶ A);
  pa_coadj (p : P) : Partial_r G p ⊣ pa_left p
}.

End CoParametrizedAdjunction.

Arguments CoParametrizedAdjunction {P A X} G.
Arguments pa_left {P A X G} _ _.
Arguments pa_coadj {P A X G} _ _.

(** *** D.3 The dual of Theorem 3  / *** D.3 定理3的对偶*)

Section DualTheorem3.

Context {P A X : Category}.
Context {G : P^op ∏ A ⟶ X}.
Context (CA : CoParametrizedAdjunction G).

Notation "'L'" := (pa_left CA) (only parsing).

(*
As in §C, every transpose names its two functors: they are implicit in the
   [adj] field and cannot be recovered from an argument of type
   G (p, a) ~> x by higher-order unification. 

--------
正如在§C中一样，每个转置都会命名它的两个函子：它们隐含在
 [adj] 字段，无法从类型的参数中恢复
 G (p, a) ~> x 通过高阶统一。 
*)

Definition copa_to (p : P) (a : A) (x : X) (k : G (p, a) ~> x) : a ~> L p x :=
  to (@adj X A (Partial_r G p) (pa_left CA p) (pa_coadj CA p) a x) k.

Definition copa_from (p : P) (a : A) (x : X) (g : a ~> L p x)
  : G (p, a) ~> x :=
  from (@adj X A (Partial_r G p) (pa_left CA p) (pa_coadj CA p) a x) g.

(*
--- F(−,h), as the conjugate of G(h,−) and nothing else ---

   For h : p ~> p' in P, the arrow h read in P^op runs p' ~{P^op}~> p, so
   [param_transform_r G h] runs G(p',−) ⟹ G(p,−) — a transformation of LEFT
   adjoints, which is what [conj_mate] consumes.  With F' := G(p',−) and
   F := G(p,−) it takes A := pa_coadj p and A' := pa_coadj p' and returns
   L p ⟹ L p', COVARIANT in the parameter.  The variance was confirmed by
   typechecking before any proof below was written. 

--------
--- F(−,h)，作为 G(h,−) 的共轭，没有其他 ---

 对于 P 中的 h : p ~> p'，P^op 中读取的箭头 h 运行 p' ~{P^op}~> p，因此
 [param_transform_r G h] 运行 G(p',−) ⟹ G(p,−) — LEFT 的变换
 伴随，这是 [conj_mate] 所消耗的。 其中 F' := G(p',−) 且
 F := G(p,−) 需要 A := pa_coadj p 和 A' := pa_coadj p' 并返回
 L p ⟹ L p'，参数中的 COVARIANT。 差异由以下方式确认
 在编写以下任何证明之前进行类型检查。 
*)

Definition copa_param_mate {p p' : P} (h : p ~> p') : L p ⟹ L p' :=
  conj_mate (pa_coadj CA p) (pa_coadj CA p') (param_transform_r G h).

Example copa_param_mate_is_conj_mate {p p' : P} (h : p ~> p') :
  copa_param_mate h
    = conj_mate (pa_coadj CA p) (pa_coadj CA p') (param_transform_r G h)
  := eq_refl.

(* --- naturality in each of the three variables ---  / --- 三个变量各自的自然性 ---*)

(*
In a and in x there is nothing new, exactly as in §C: these ARE the
   [Adjunction] fields at a fixed parameter. 

--------
在 a 和 x 中没有什么新内容，就像§C 中一样：这些是
 [Adjunction] 字段具有固定参数。 
*)

Lemma copa_natural_a (p : P) {a b : A} {x : X}
      (k : G (p, b) ~> x) (g : a ~> b) :
  copa_to p a x (k ∘ fmap[Partial_r G p] g) ≈ copa_to p b x k ∘ g.
Proof. exact (to_adj_nat_l (Adjunction:=pa_coadj CA p) k g). Qed.

Lemma copa_natural_x (p : P) {a : A} {x y : X}
      (f : x ~> y) (k : G (p, a) ~> x) :
  copa_to p a y (f ∘ k) ≈ fmap[L p] f ∘ copa_to p a x k.
Proof. exact (to_adj_nat_r (Adjunction:=pa_coadj CA p) f k). Qed.

(* Naturality in p, elementarily first.  / p 中的自然性，基本上是第一位的。*)

Definition copa_square {p p' : P} (h : p ~> p')
           (sig : L p ⟹ L p') : Type :=
  ∀ (a : A) (x : X) (k : G (p, a) ~> x),
    copa_to p' a x (k ∘ fmap[Partial_l G a] h) ≈ sig x ∘ copa_to p a x k.

Example copa_square_is_Conjugate {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square h sig
    = Conjugate (pa_coadj CA p) (pa_coadj CA p')
        (param_transform_r G h) sig
  := eq_refl.

Theorem copa_natural_p {p p' : P} (h : p ~> p') :
  copa_square h (copa_param_mate h).
Proof.
  exact (conjugate_conj_mate (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h)).
Qed.

Definition copa_square_from {p p' : P} (h : p ~> p')
           (sig : L p ⟹ L p') : Type :=
  ∀ (a : A) (x : X) (g : a ~> L p x),
    copa_from p' a x (sig x ∘ g)
      ≈ copa_from p a x g ∘ fmap[Partial_l G a] h.

Example copa_square_from_is_ConjugateFrom {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square_from h sig
    = ConjugateFrom (pa_coadj CA p) (pa_coadj CA p')
        (param_transform_r G h) sig
  := eq_refl.

Theorem copa_square_iff_from {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square h sig ↔ copa_square_from h sig.
Proof.
  exact (conjugate_iff_from (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h) sig).
Defined.

(*
--- the two functor laws of F(−,a), by uniqueness of conjugates ---

   As in §C these are [conj_mate_id] and [conj_mate_compose], consumed by
   name.  Unlike §C, the composition law comes out COVARIANT: the mate of a
   composite is the composite of the mates in the SAME order. 

--------
--- F(−,a) 的两个函子定律，通过共轭的唯一性 ---

 如§C 中所示，这些是 [conj_mate_id] 和 [conj_mate_compose]，由
 名字。 与 §C 不同，复合法则来自 COVARIANT：a 的配偶
 复合材料是按相同顺序的配合的复合材料。 
*)

Lemma copa_param_mate_respects {p p' : P} (h h' : p ~> p') :
  h ≈ h' → copa_param_mate h ≈ copa_param_mate h'.
Proof.
  intro E; unfold copa_param_mate.
  apply conj_mate_respects, param_transform_r_respects, E.
Qed.

Lemma copa_param_mate_id {p : P} : copa_param_mate (id[p]) ≈ nat_id.
Proof.
  unfold copa_param_mate.
  rewrite (conj_mate_respects (pa_coadj CA p) (pa_coadj CA p) _ nat_id
             (param_transform_r_id G)).
  apply conj_mate_id.
Qed.

Lemma copa_param_mate_comp {p p' p'' : P} (h : p ~> p') (h' : p' ~> p'') :
  copa_param_mate (h' ∘ h) ≈ copa_param_mate h' ∙ copa_param_mate h.
Proof.
  unfold copa_param_mate.
  rewrite (conj_mate_respects (pa_coadj CA p) (pa_coadj CA p'') _ _
             (param_transform_r_comp G h' h)).
  apply (conj_mate_compose (pa_coadj CA p) (pa_coadj CA p')
           (pa_coadj CA p'')).
Qed.

Lemma copa_param_mate_id_at {p : P} (x : X) :
  copa_param_mate (id[p]) x ≈ id.
Proof.
  transitivity (transform[@nat_id X A (L p)] x).
  - exact (copa_param_mate_id x).
  - apply fmap_id.
Qed.

Lemma copa_param_mate_comp_at {p p' p'' : P}
      (h : p ~> p') (h' : p' ~> p'') (x : X) :
  copa_param_mate (h' ∘ h) x
    ≈ copa_param_mate h' x ∘ copa_param_mate h x.
Proof. exact (copa_param_mate_comp h h' x). Qed.

(* --- Mac Lane's F : X × P → A.  No [op] occurs in its type. ---  / --- Mac Lane 的 F : X × P → A。其类型中没有 [op] 出现。 ---*)

#[local] Obligation Tactic := idtac.

Program Definition parametrized_left_adjoint_bifunctor : X ∏ P ⟶ A := {|
  fobj := fun q => L (snd q) (fst q);
  fmap := fun q q' fh =>
            fmap[L (snd q')] (fst fh)
              ∘ copa_param_mate (snd fh) (fst q)
|}.
Next Obligation.
  intros [x p] [x' p'] [f h] [f' h'] [Ef Eh]; simpl in Ef, Eh.
  apply compose_respects.
  - now apply fmap_respects.
  - exact (copa_param_mate_respects h h' Eh x).
Qed.
Next Obligation.
  intros [x p].
  etransitivity.
  { apply compose_respects; [ reflexivity |].
    exact (copa_param_mate_id_at x). }
  simpl.
  rewrite fmap_id.
  now rewrite id_left.
Qed.
Next Obligation.
  intros [x p] [x' p'] [x'' p''] [f h] [f' h'].
  etransitivity.
  { apply compose_respects.
    - apply fmap_comp.
    - exact (copa_param_mate_comp_at h' h x). }
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity ].
  exact (naturality (copa_param_mate h) _ _ f').
Qed.

#[local] Obligation Tactic := program_simpl.

Example copa_bifunctor_obj (x : X) (p : P) :
  fobj[parametrized_left_adjoint_bifunctor] (x, p) = L p x := eq_refl.

Example copa_bifunctor_fmap {x x' : X} {p p' : P}
        (f : x ~> x') (h : p ~> p') :
  fmap[parametrized_left_adjoint_bifunctor] ((f, h) :
        (x, p) ~{X ∏ P}~> (x', p'))
    = fmap[L p'] f ∘ copa_param_mate h x := eq_refl.

(*
In the parameter alone the action is the mate, up to the residue
   fmap[L p'] id that [fmap] leaves behind.  As in §C the strict form
     fmap[...] (id, h) = copa_param_mate h x
   is measured and REFUTED — a CONVERSION rejection ("cannot unify"),
   since [fmap_id] is a law field — so only the ≈ form below holds.  That
   refutation is pinned in Test/ProbeParameter396.v as
   [p396_copa_fmap_param_strict]. 

--------
仅在参数中，动作是配合，直到残差
 [fmap] 留下的 fmap[L p'] id。 正如 §C 中的严格形式
 fmap[...] (id, h) = copa_param_mate h x
 被测量并被拒绝——转换拒绝（“无法统一”），
 因为 [fmap_id] 是一个定律场，所以只有下面的 ≈ 形式成立。 那
 反驳固定在 Test/ProbeParameter396.v 中：
 [p396_copa_fmap_param_strict]。 
*)

Example copa_bifunctor_fmap_param {x : X} {p p' : P} (h : p ~> p') :
  fmap[parametrized_left_adjoint_bifunctor] ((id[x], h) :
        (x, p) ~{X ∏ P}~> (x, p'))
    = fmap[L p'] (id[x]) ∘ copa_param_mate h x := eq_refl.

Lemma copa_bifunctor_fmap_is_mate {x : X} {p p' : P} (h : p ~> p') :
  fmap[parametrized_left_adjoint_bifunctor] ((id[x], h) :
        (x, p) ~{X ∏ P}~> (x, p'))
    ≈ copa_param_mate h x.
Proof. simpl; rewrite fmap_id; now rewrite id_left. Qed.

(*
Its partial functor in the FIRST variable is the given family, on the nose
   in both data fields; as in §C the whole functor records are not equal, the
   three law fields of [Partial_l] being rebuilt Program obligations. 

--------
它在 FIRST 变量中的部分函子是给定的族，在鼻子上
 在两个数据字段中； 如§C 所示，整个函子记录不相等，
 [Partial_l] 的三个法律领域正在重建计划义务。 
*)

Example copa_bifunctor_partial_l_obj (p : P) (x : X) :
  fobj[Partial_l parametrized_left_adjoint_bifunctor p] x = L p x := eq_refl.

Example copa_bifunctor_partial_l_fmap_unfold (p : P) {x x' : X} (f : x ~> x') :
  fmap[Partial_l parametrized_left_adjoint_bifunctor p] f
    = fmap[L p] f ∘ copa_param_mate (id[p]) x := eq_refl.

Lemma copa_bifunctor_partial_l_fmap (p : P) {x x' : X} (f : x ~> x') :
  fmap[Partial_l parametrized_left_adjoint_bifunctor p] f ≈ fmap[L p] f.
Proof.
  transitivity (fmap[L p] f ∘ copa_param_mate (id[p]) x); [ reflexivity |].
  rewrite (copa_param_mate_id_at x).
  now rewrite id_right.
Qed.

(* --- UNIQUENESS, over the assignment, exactly as in §C ---  / --- 唯一性，在分配上，与§C 完全相同 ---*)

Theorem copa_param_mate_uniq {p p' : P} (h : p ~> p')
        (sig : L p ⟹ L p') :
  copa_square h sig → ∀ x : X, sig x ≈ copa_param_mate h x.
Proof.
  intros H x.
  exact (conj_mate_uniq (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h) sig H x).
Qed.

Theorem copa_assignment_unique
        (Fh : ∀ (p p' : P) (h : p ~> p'), L p ⟹ L p')
        (Hsq : ∀ (p p' : P) (h : p ~> p'), copa_square h (Fh p p' h)) :
  ∀ (p p' : P) (h : p ~> p') (x : X),
    Fh p p' h x ≈ copa_param_mate h x.
Proof.
  intros p p' h x.
  exact (copa_param_mate_uniq h (Fh p p' h) (Hsq p p' h) x).
Qed.

Theorem copa_param_mate_universal {p p' : P} (h : p ~> p') :
  ∃! sig : L p ⟹ L p', copa_square h sig.
Proof.
  exact (conjugate_unique_right (pa_coadj CA p) (pa_coadj CA p')
           (param_transform_r G h)).
Defined.

Corollary copa_bifunctor_fmap_determined
        (Fh : ∀ (p p' : P) (h : p ~> p'), L p ⟹ L p')
        (Hsq : ∀ (p p' : P) (h : p ~> p'), copa_square h (Fh p p' h))
        (q q' : X ∏ P) (fh : q ~> q') :
  fmap[parametrized_left_adjoint_bifunctor] fh
    ≈ fmap[L (snd q')] (fst fh) ∘ Fh (snd q) (snd q') (snd fh) (fst q).
Proof.
  destruct q as [x p], q' as [x' p'], fh as [f h]; simpl.
  apply compose_respects; [ reflexivity |].
  symmetry.
  exact (copa_assignment_unique Fh Hsq p p' h x).
Qed.

(*
--- the [Swap] route, measured rather than argued ---

   The alternative is to read the dual hypothesis as a §A hypothesis for
   G ◯ Swap : A ∏ P^op ⟶ X.  It is available, and it is not free.  The two
   partial functors agree in BOTH data fields on the nose ([copa_swap_obj],
   [copa_swap_fmap]) but not as records — Partial_l (G ◯ Swap) p =
   Partial_r G p is measured and REFUTED, a CONVERSION rejection, since
   [Partial_l] and [Partial_r] rebuild their three law fields as separate
   Program obligations.  Consequently [pa_coadj CA p] does not ascribe at
   Partial_l (G ◯ Swap) p ⊣ pa_left CA p either — that rejection is measured
   too, and is a TYPING one, a plain "has type ... while it is expected to
   have type" with no "cannot unify" and no universe clause, where the
   functor comparison above is a CONVERSION one — so a field-copy transport
   is needed ([copa_swap_transport]); it works only because every
   [Adjunction] field mentions its left adjoint solely through F x and
   fmap[F] g, both of which convert.  Both refutations are pinned in
   Test/ProbeParameter396.v, as [p396_swap_strict] and
   [p396_swap_ascribe].  What that route then produces is
   [copa_swap_route_bifunctor], of type P ∏ X ⟶ A — the two arguments in the
   OPPOSITE ORDER to the book's X × P → A, so a further [Swap] would be
   needed at the conclusion.  The direct route above needs neither transport
   nor swap, and is the one taken. 

--------
--- [Swap] 路线，经过测量而不是争论 ---

另一种方法是将对偶假设解读为 §A 假设
 G ◯ 交换：A ∏ P^op ⟶ X。它是可用的，而且不是免费的。 两人
 部分函子在鼻子上的两个数据字段中一致（[copa_swap_obj]，
 [copa_swap_fmap]) 但不作为记录 — Partial_l (G ◯ 交换) p =
 Partial_r G p 被测量并被拒绝，转换拒绝，因为
 [Partial_l] 和 [Partial_r] 将其三个定律场重建为独立的
 计划义务。 因此 [pa_coadj CA p] 并不归因于
 Partial_l (G ◯ Swap) p ⊣ pa_left CA p 任一 — 测量拒绝
 也是，而且是打字的，一个简单的“有类型......
虽然预计
 有类型”，没有“不能统一”，也没有 Universe 子句，其中
 上面的函子比较是一个 CONVERSION 比较——所以是一个字段复制传输
 需要（[copa_swap_transport]）； 它有效只是因为每个
 [Adjunction] 字段仅通过 F x 提及其左伴随
 fmap[F] g，两者都进行转换。 两种反驳都固定在
 Test/ProbeParameter396.v，如 [p396_swap_strict] 和
 [p396_swap_ascribe]。 该路线随后产生的是
 [copa_swap_route_bifunctor]，类型为 P ∏ X ⟶ A — 中的两个参数
 与书中的 X × P → A 的顺序相反，因此进一步的 [Swap] 将是
 结论时需要。 上述直达路线无需任何交通工具
 也不交换，并且是所采取的。 
*)

Example copa_swap_obj (p : P) (a : A) :
  fobj[Partial_l (G ◯ @Swap A (P^op)) p] a = fobj[Partial_r G p] a := eq_refl.

Example copa_swap_fmap (p : P) {a a' : A} (k : a ~> a') :
  fmap[Partial_l (G ◯ @Swap A (P^op)) p] k = fmap[Partial_r G p] k := eq_refl.

Definition copa_swap_transport (p : P)
  (Adj : Partial_r G p ⊣ pa_left CA p) :
  Partial_l (G ◯ @Swap A (P^op)) p ⊣ pa_left CA p :=
  @Build_Adjunction X A (Partial_l (G ◯ @Swap A (P^op)) p) (pa_left CA p)
    (@adj            _ _ _ _ Adj)
    (@to_adj_nat_l   _ _ _ _ Adj)
    (@to_adj_nat_r   _ _ _ _ Adj)
    (@from_adj_nat_l _ _ _ _ Adj)
    (@from_adj_nat_r _ _ _ _ Adj).

Definition copa_swap_route : ParametrizedAdjunction (G ◯ @Swap A (P^op)) :=
  @Build_ParametrizedAdjunction A (P^op) X (G ◯ @Swap A (P^op))
    (pa_left CA) (fun p => copa_swap_transport p (pa_coadj CA p)).

(*
The ascription is the measurement: this elaborates only because
   (P^op)^op is P, so the Swap route's bifunctor takes its arguments in the
   order P then X. 

--------
归因就是测量：这只是因为
 (P^op)^op 是 P，因此交换路由的双函子在
 先订购 P，然后订购 X。 
*)

Example copa_swap_route_bifunctor : P ∏ X ⟶ A :=
  parametrized_right_adjoint_bifunctor copa_swap_route.

End DualTheorem3.

Arguments copa_param_mate {P A X G} CA {p p'} h.
Arguments copa_square {P A X G} CA {p p'} h sig.
Arguments parametrized_left_adjoint_bifunctor {P A X G} CA.

(** ** E. The currying instance, and naturality in the parameter  / ** E. 柯里化实例和参数的自然性*)

(*
Mac Lane's motivating remark (book p. 101) is the currying bijection
   hom(S × T, R) ≅ hom(S, hom(T, R)) with T the parameter.  In a cartesian
   closed category that is the adjunction (− × p) ⊣ (−)^p, so the family of
   those adjunctions is a [ParametrizedAdjunction] for the internal product
   bifunctor ×(C), and Theorem 3 then FORCES the arrow action of (−)^(−) in
   the parameter.  That forced action is the internal-hom action, which is
   the content of [curry_param_mate_is_ihom] below.

   WHY THE ADJUNCTION IS BUILT AND NOT TRANSPORTED.  The tree already has
   Curry_Adjunction : Prod_Functor p ⊣ Exp_Functor p
   (Structure/Cartesian/Closed/Adjunction.v), but its left adjoint is
   [Prod_Functor p], whose arrow action is [first f] = (f ∘ exl) △ exr, while
   §A needs [Partial_l ×(C) p], whose arrow action is
   bimap f id = (f ∘ exl) △ (id ∘ exr).  The two agree on OBJECTS on the nose
   ([curry_prod_functor_obj]) and differ on ARROWS by exactly one [id_left]
   ([curry_prod_functor_fmap]); the strict form is measured and REFUTED (a
   CONVERSION rejection, "cannot unify"), and pinned in
   Test/ProbeParameter396.v as [p396_prod_functor_fmap_strict].  A field-copy
   transport is therefore unavailable, and that too is MEASURED rather than
   argued: feeding Curry_Adjunction's five projections to @Build_Adjunction
   at [Partial_l ×(C) p] is rejected, and it is rejected precisely at
   [to_adj_nat_l], the first field whose type mentions fmap[F] g, with an
   error naming the two spellings.  Elaboration reaches that field at all
   only because [adj] itself was ACCEPTED — it mentions fobj alone, which
   does convert — which is why [curry_pa_adj] is built with
   [Build_Adjunction'] from that one field; its two naturality clauses are
   Curry_Adjunction's own, reached through one [id_left] under the
   transpose.

   WHAT THIS SECTION IS FOR.  Structure/Cartesian/Closed.v's [Closed] class
   carries NO naturality field in any variable — its fields are
   [exponent_obj], [exp_iso], the three derived transposes, and the beta law
   — so the naturality of currying in the parameter cannot be phrased against
   that class at all.  [curry_natural_param] supplies it as a standalone
   equation in plain [Closed] vocabulary ([curry], [second], [eval]), so a
   consumer needs none of this file's records to use it. 

--------
Mac Lane 的激励性言论（本书第 101 页）是柯里化双射
 hom(S × T, R) ≅ hom(S, hom(T, R))，其中 T 为参数。 在笛卡尔坐标系中
 闭范畴即附加 (− × p) ⊣ (−)^p，因此族
 这些附件是内部产品的 [ParametrizedAdjunction]
 双函子 ×(C) 和定理 3 则强制 (−)^(−) 的箭头作用
 参数。 这种强制动作就是内冲动作，即
 [curry_param_mate_is_ihom] 的内容如下。

为什么要建造辅助设施而不是运输辅助设施。 树上已经有了
 Curry_Adjunction : Prod_Functor p ⊣ Exp_Functor p
 (Structure/Cartesian/Closed/Adjunction.v)，但它的左伴随是
 [Prod_Functor p]，其箭头作用为 [first f] = (f ∘ exl) △ exr，而
 §A需要[Partial_l ×(C) p]，其箭头动作为
 bimap f id = (f ∘ exl) △ (id ∘ exr)。 两人对鼻子上的物体达成一致
 ([curry_prod_functor_obj]) 与 ARROWS 上相差 1 个 [id_left]
 （[curry_prod_functor_fmap]）； 严格的形式被测量和驳斥（a
 CONVERSION 拒绝，“无法统一”），并固定在
 测试/ProbeParameter396.v 作为 [p396_prod_functor_fmap_strict]。
现场副本
 因此运输不可用，这也是测量的而不是
 争论：将 Curry_Adjunction 的五个预测提供给 @Build_Adjunction
 [Partial_l ×(C) p] 被拒绝，并且恰好在
 [to_adj_nat_l]，第一个类型提到 fmap[F] g 的字段，带有
 命名两个拼写时出错。 详细阐述完全达到了该领域
 只是因为 [adj] 本身被接受了——它单独提到了 fobj，这
 确实会转换——这就是 [curry_pa_adj] 构建的原因
 [Build_Adjunction'] 来自这一领域； 它的两个自然性子句是
 Curry_Adjunction 自己的，通过下一个 [id_left] 达到
 转置。

本节的用途。 Structure/Cartesian/Closed.v 的 [Closed] 类
 任何变量中都没有自然场——它的场是
 [exponent_obj]、[exp_iso]、三个派生转置和 beta 定律
 ——所以参数中柯里化的自然性不能被反对
 那堂课根本就没有。 [curry_natural_param] 将其作为独立的
 简单 [Closed] 词汇表中的方程（[curry]、[second]、[eval]），因此
 消费者不需要该文件的任何记录即可使用它。 
*)

Section Currying.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** *** E.1 The instance  / *** E.1 实例*)

Example curry_prod_functor_obj (p x : C) :
  fobj[Partial_l ×(C) p] x = fobj[Prod_Functor p] x := eq_refl.

Lemma curry_prod_functor_fmap (p : C) {x y : C} (f : x ~> y) :
  fmap[Partial_l ×(C) p] f ≈ fmap[Prod_Functor p] f.
Proof. simpl; unfold first; now rewrite id_left. Qed.

Program Definition curry_pa_adj (p : C) : Partial_l ×(C) p ⊣ Exp_Functor p :=
  Build_Adjunction'
    (F:=Partial_l ×(C) p) (U:=Exp_Functor p)
    (fun x y => @adj C C (Prod_Functor p) (Exp_Functor p)
                     (Curry_Adjunction p) x y) _ _.
Next Obligation.
  simpl.
  transitivity (curry (f ∘ first g)).
  - apply proper_morphism; simpl; unfold first; now rewrite id_left.
  - symmetry; apply curry_comp_l.
Qed.
Next Obligation. simpl; apply curry_comp. Qed.

Definition curry_ParametrizedAdjunction : ParametrizedAdjunction ×(C) := {|
  pa_right := Exp_Functor;
  pa_adj := curry_pa_adj
|}.

Notation "'CPA'" := curry_ParametrizedAdjunction (only parsing).

(*
Everything §C names, read back at Leibniz equality at this instance: the
   family of right adjoints, the counit, and both transposes. 

--------
§C 的一切名称，在本例中回读莱布尼茨等式：
 右伴随族、counit 以及两者的转置。 
*)

Example curry_pa_right (p : C) : pa_right CPA p = Exp_Functor p := eq_refl.

Example curry_pa_counit_is_eval (p a : C) :
  @counit C C (Partial_l ×(C) p) (Exp_Functor p) (curry_pa_adj p) a
    = @eval C _ _ p a := eq_refl.

Example curry_pa_to_is_curry (p x a : C) (k : x × p ~> a) :
  pa_to CPA p x a k = curry k := eq_refl.

Example curry_pa_from_is_uncurry (p x a : C) (g : x ~> a ^ p) :
  pa_from CPA p x a g = uncurry g := eq_refl.

(*
Mac Lane's square, unfolded at this instance.  This is where the shape of
   the standalone lemma below is READ OFF rather than guessed: the left-hand
   side is curry of a precomposition by the parameter arrow, and the
   right-hand side is postcomposition by the mate. 

--------
麦克莱恩广场此时展开。 这就是形状的地方
 下面的独立引理是读出而不是猜测：左边
 side 是通过参数 arrow 进行预组合的柯里化，并且
 右侧是队友的后期合成。 
*)

Example curry_pa_square_unfold {p p' : C} (h : p' ~> p)
        (tau : Exp_Functor p ⟹ Exp_Functor p') :
  pa_square CPA h tau
    = (∀ (x a : C) (k : x × p ~> a),
         curry (k ∘ ((id[x] ∘ exl) △ (h ∘ exr))) ≈ tau a ∘ curry k)
  := eq_refl.

(** *** E.2 The mate is the internal-hom action  / *** E.2 配合是内部 hom 动作*)

(*
The bridge between [ihom]'s spelling and plain [Closed] vocabulary: they
   differ by one [id_left] under the transpose. 

--------
[ihom] 的拼写和普通 [Closed] 词汇之间的桥梁：它们
 转置下相差 1 [id_left]。 
*)

Lemma ihom_id_action {p p' a : C} (h : p' ~> p) :
  ihom h (id[a]) ≈ curry (eval ∘ second h).
Proof. unfold ihom; apply proper_morphism; now rewrite id_left. Qed.

(*
The forced action, identified.  Strict equality is measured and REFUTED
   against BOTH spellings, and the RESIDUE that blocks it is exhibited at
   Leibniz equality rather than described: the mate is literally
     curry (eval ∘ ((id ∘ exl) △ (h ∘ exr)))
   ([curry_param_mate_residue], eq_refl), while [second h] is
   exl △ (h ∘ exr), so clearing the [id ∘ exl] needs [id_left], a law field.
   Both refutations are CONVERSION rejections ("cannot unify", no universe
   clause), pinned in Test/ProbeParameter396.v as
   [p396_curry_mate_closed_strict] and [p396_curry_mate_ihom_strict]. 

--------
强制行动，已确定。 严格平等受到衡量和驳斥
 反对这两种拼写，并且阻止它的 RESIDUE 展示在
 莱布尼茨平等而不是描述：伴侣是字面上的
 咖喱 (eval ∘ ((id ∘ exl) △ (h ∘ exr)))
 ([curry_param_mate_residue], eq_refl)，而 [second h] 是
 exl △(h ∘ exr)，所以清除[id ∘ exl]需要[id_left]，一个法则场。 
两种反驳都是 CONVERSION 拒绝（“无法统一”，没有宇宙
 子句），在 Test/ProbeParameter396.v 中固定为
 [p396_curry_mate_closed_strict] 和 [p396_curry_mate_ihom_strict]。 
*)

Example curry_param_mate_unfold {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a
    = curry (@counit C C (Partial_l ×(C) p) (Exp_Functor p)
               (curry_pa_adj p) a
             ∘ transform[param_transform ×(C) h] (a ^ p))
  := eq_refl.

Example curry_param_mate_residue {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a
    = curry (eval ∘ ((id[a ^ p] ∘ exl) △ (h ∘ exr))) := eq_refl.

Lemma curry_param_mate_is_closed_action {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a ≈ curry (eval ∘ second h).
Proof.
  simpl.
  apply proper_morphism, compose_respects; [ reflexivity |].
  unfold second; now rewrite id_left.
Qed.

Lemma curry_param_mate_is_ihom {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a ≈ ihom h (id[a]).
Proof.
  rewrite curry_param_mate_is_closed_action.
  symmetry; apply ihom_id_action.
Qed.

(*
[ihom] IS the arrow action of [InternalHomFunctor] at Leibniz equality
   (Structure/Cartesian/Closed/Natural.v's [ihom_is_InternalHomFunctor_fmap]),
   so the identification the catalogue issue asks for — "postcomposition with
   a map of the parameter and the induced map of internal homs are conjugate"
   — comes out of the previous lemma with no further work.  Note [op] is the
   identity (Construction/Opposite.v), so no re-reading occurs. 

--------
[ihom] 是 [InternalHomFunctor] 在莱布尼茨等式上的箭头动作
 （结构/笛卡尔/闭合/自然.v 的 [ihom_is_InternalHomFunctor_fmap]），
 所以目录问题所要求的识别——“后期合成
 参数图与内部homs诱导图共轭"
 - 从之前的引理中得出，无需进一步的工作。 注意 [op] 是
 身份（Construction/Opposite.v），因此不会发生重读。 
*)

Lemma curry_param_mate_is_internal_hom {p p' : C} (h : p' ~> p) (a : C) :
  pa_param_mate CPA h a
    ≈ @fmap _ _ (InternalHomFunctor C) (p, a) (p', a) (h, id[a]).
Proof. apply curry_param_mate_is_ihom. Qed.

Example curry_internal_hom_fmap_unfold {p p' : C} (h : p' ~> p) (a : C) :
  @fmap _ _ (InternalHomFunctor C) (p, a) (p', a) (h, id[a])
    = curry (id[a] ∘ eval ∘ second h) := eq_refl.

(** *** E.3 Naturality of currying in the parameter — the standalone lemma  / *** E.3 参数中柯里化的自然性——独立引理*)

(*
THE PAYOFF, stated so that Structure/Cartesian/Closed.v's users can consume
   it without any record of this file: for h : p' ~> p and f : x × p ~> a,

       curry (f ∘ second h) ≈ curry (eval ∘ second h) ∘ curry f.

   The right-hand side was DERIVED from the mate — it is
   [curry_param_mate_is_closed_action] applied to the square unfolded in
   [curry_pa_square_unfold] — and [curry_natural_param_from_mate] below
   obtains the very same statement by instantiating [pa_natural_p], so the
   derivation is machine-checked rather than described.

   PRIOR ART, disclosed and CONSUMED rather than reproved:
   Structure/Cartesian/Closed/Natural.v's [ihom_curry] is this fact in
   [ihom] vocabulary, and it is NOT a literal instance of the statement below
   (it reads ihom f h ∘ curry m ≈ curry (h ∘ m ∘ second f), which at h := id
   differs from the form here by two [id_left]s and by the [ihom] spelling),
   so the statement is restated in plain [Closed] vocabulary while its proof
   is that donor plus [ihom_id_action].  Requiring that donor costs FOUR
   modules on this file's transitive in-project closure — 29 without it
   against 33 with it, measured by dropping the single [Require] and
   recomputing. 

--------
回报，以便 Structure/Cartesian/Closed.v 的用户可以消费
 它没有此文件的任何记录：对于 h : p' ~> p 和 f : x × p ~> a，

柯里 (f ∘ 第二个 h) ≈ 柯里 (eval ∘ 第二个 h) ∘ 柯里 f。

右侧是从配偶中派生出来的——它是
 [curry_param_mate_is_closed_action] 应用于展开的正方形
 [curry_pa_square_unfold] — 和下面的 [curry_natural_param_from_mate]
 通过实例化 [pa_natural_p] 获得完全相同的语句，因此
 推导是机器检查的而不是描述的。

现有技术，已公开并已使用，而非已被谴责：
 Structure/Cartesian/Closed/Natural.v 的 [ihom_curry] 就是这个事实
 [ihom] 词汇表，它不是下面语句的字面实例
 （它读作 ihom f h ∘ curry m ≈ curry (h ∘ m ∘ secondary f)，在 h := id
 与此处的形式不同，有两个 [id_left] 和 [ihom] 拼写），
 因此该陈述以简单的 [Closed] 词汇重述，而其证明
 是那个捐赠者加上[ihom_id_action]。 要求捐赠者花费四
 该文件的传递性项目内闭包的模块 — 29 个没有它
 与 33 相比，通过掉落单个 [Require] 和
 重新计算。 
*)

Lemma curry_natural_param {x p p' a : C} (h : p' ~> p) (f : x × p ~> a) :
  curry (f ∘ second h) ≈ curry (eval ∘ second h) ∘ curry f.
Proof.
  rewrite <- ihom_id_action.
  rewrite (ihom_curry h (id[a]) f).
  apply proper_morphism.
  now rewrite id_left.
Qed.

(*
The same statement, obtained from Theorem 3's square instead: this is what
   shows the right-hand side above was read off the mate. 

--------
同样的说法，从定理 3 的平方得到：这就是
 显示上面的右侧是从配偶处读出的。 
*)

Lemma curry_natural_param_from_mate
      {x p p' a : C} (h : p' ~> p) (f : x × p ~> a) :
  curry (f ∘ second h) ≈ curry (eval ∘ second h) ∘ curry f.
Proof.
  transitivity (curry (f ∘ ((id[x] ∘ exl) △ (h ∘ exr)))).
  { apply proper_morphism, compose_respects; [ reflexivity |].
    unfold second; now rewrite id_left. }
  transitivity (pa_param_mate CPA h a ∘ curry f).
  { exact (pa_natural_p CPA h x a f). }
  apply compose_respects; [| reflexivity ].
  apply curry_param_mate_is_closed_action.
Qed.

(*
That the two routes really do prove ONE statement is machine-checked and
   not left to the reader's eye: the equation below is well formed only if
   the two constants have the same type. 

--------
这两条路线确实证明了一个语句是经过机器检查的并且
 不留给读者的眼睛：只有当以下方程成立时
 这两个常量具有相同的类型。 
*)

Example curry_natural_param_routes_agree : Prop :=
  @curry_natural_param = @curry_natural_param_from_mate.

(*
The inverse-transpose reading of the same square, which §C's
   [pa_square_iff_from] says is equivalent.  No [ihom] donor exists for this
   direction (measured: Structure/Cartesian/Closed/Natural.v has no
   [ihom_uncurry] or any lemma of that shape), so it is proved directly. 

--------
同一个正方形的转置读数，其中 §C 的
 [pa_square_iff_from] 说是等效的。 不存在为此目的的 [ihom] 供体
 方向（测量：Structure/Cartesian/Closed/Natural.v 没有
 [ihom_uncurry] 或该形状的任何引理），因此可以直接证明。 
*)

Lemma uncurry_natural_param {x p p' a : C} (h : p' ~> p) (g : x ~> a ^ p) :
  uncurry (curry (eval ∘ second h) ∘ g) ≈ uncurry g ∘ second h.
Proof.
  rewrite uncurry_comp, uncurry_curry.
  rewrite <- comp_assoc.
  rewrite <- first_second.
  rewrite comp_assoc.
  now rewrite eval_first.
Qed.

(** *** E.4 The assembled bifunctor is the internal hom  / *** E.4 组装好的双函数是内部宏*)

(* Theorem 3 applied at this instance produces a bifunctor C^op ∏ C ⟶ C whose
   object action is the exponential on the nose and whose arrow action agrees
   with Functor/Hom/Internal.v's [InternalHomFunctor] up to ≈.  What is
   measured and REFUTED is the ARROW ACTION at [eq_refl] — a CONVERSION
   rejection, pinned in Test/ProbeParameter396.v as
   [p396_curry_bifunctor_fmap_strict] — from which the whole functor records
   differ a fortiori; no separate record-level comparison is claimed.  The
   cause is that [InternalHomFunctor] transposes ONCE where the assembled
   bifunctor transposes TWICE, postcomposition in the base and
   precomposition in the exponent being applied separately here, so the two
   differ by one [curry_comp], one [id_left] and associativity.

   DISPLAY HAZARD, measured: [fmap]'s functor argument is implicit and is
   suppressed, so under the default settings the two sides of
   [curry_bifunctor_fmap] PRINT IDENTICALLY, as if the lemma were an instance
   of reflexivity.  It is not — [Set Printing Implicit] separates them, and
   [reflexivity] does not close the goal (both measured). *)

Example curry_bifunctor_obj (p a : C) :
  fobj[parametrized_right_adjoint_bifunctor CPA] (p, a)
    = fobj[InternalHomFunctor C] (p, a) := eq_refl.

Lemma curry_bifunctor_fmap {p p' a a' : C}
      (h : p ~{C^op}~> p') (k : a ~> a') :
  fmap[parametrized_right_adjoint_bifunctor CPA]
      ((h, k) : (p, a) ~{C^op ∏ C}~> (p', a'))
    ≈ fmap[InternalHomFunctor C] ((h, k) : (p, a) ~{C^op ∏ C}~> (p', a')).
Proof.
  simpl.
  rewrite <- curry_comp.
  apply proper_morphism.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity |].
  apply compose_respects; [ reflexivity |].
  unfold second; now rewrite id_left.
Qed.

End Currying.

Arguments curry_natural_param {C _ _ x p p' a} h f.
Arguments uncurry_natural_param {C _ _ x p p' a} h g.

(** ** F. Exercise 2: the unit is a WEDGE in the parameter  / ** F.练习2：参数中的单位是WEDGE*)

(*
Mac Lane's Exercise 2, quoted from the same page (book p. 102):

     2.  Let η_x : x → G(p, F(x,p)) be the unit of an adjunction with
     parameter.  It is natural in x, but what property of η corresponds to
     the naturality of the adjunction (10) in p?

   THE ANSWER IS DINATURALITY IN THE PARAMETER — the wedge condition.  The
   unit at the parameter p is a family of arrows OUT OF ONE OBJECT x into the
   DIAGONAL of the bifunctor (p, q) ↦ G(p, F(x,q)), and a family of that
   shape satisfying the naturality-in-p square IS a wedge.

   WHY [Theory/Dinatural.v]'s [Dinatural] IS NOT THE VEHICLE, measured rather
   than asserted.  [Dinatural F G] relates TWO bifunctors C^op ∏ C ⟶ D by a
   family on their diagonals; here the source would have to be the CONSTANT
   bifunctor at x, and three facts make that the wrong packaging.  (i) The
   source is constant, which is exactly the case [Structure/Wedge.v]'s own
   header says a wedge is for.  (ii) The named constant-functor constant is
   [Constant_Functor] (Instance/Fun/Terminal.v), and requiring that
   module costs 28 modules on this file's transitive in-project closure (68
   without it, 96 with it, measured by adding it to the seed set and
   recomputing over .Makefile.coq.d) — though read that as a remark about a
   route not taken rather than an obstacle, since [Diagonal]
   (Functor/Diagonal.v) has the constant functor as its OBJECT ACTION and
   its module is ALREADY in the closure at marginal cost 0; it is not a
   drop-in, being a [Program Instance] whose [fobj] need not reduce.  (iii)
   Even given a
   constant bifunctor — one is five lines and raises ZERO obligations, so
   this was compiled out of tree rather than argued — the dinaturality
   hexagon is NOT the wedge condition definitionally: it carries two
   [fmap[Const] _] residues, each an [∘ id], and its two sides are swapped.
   The identification of the two conditions was measured and REFUTED at
   [eq_refl] with a CONVERSION error ("cannot unify", no universe clause),
   and the two are interderivable, each direction by [rewrite !id_right]
   followed by [symmetry].  So [Theory/Dinatural.v] is NOT required by this
   file and the wedge is the shape delivered.

   THE ELEMENTARY FORM COMES FIRST.  [pa_unit_dinatural] states the equation
   with no class wrapper, so a reader sees it without unfolding [Wedge]; and
   it is the constant that is FREE of the universe identification the wedge
   packaging carries (see the universes paragraph in the header).  Its proof
   is a [symmetry] and then one application of Adjunction/Conjugate.v's
   [conjugate_to_unit] at the
   conjugate pair of §C — that is, Exercise 2's answer is the [ConjugateUnit]
   characterisation of conjugacy, which #394 already carries by name.

   THE COUNIT'S MIRROR is [pa_counit_extranatural], the [ConjugateCounit]
   characterisation read at the same pair; it is the extranaturality/cowedge
   condition.  It is delivered ELEMENTARILY ONLY — no [Cowedge] instance is
   built (see the header's NOT-DELIVERED list for the reason). 

--------
Mac Lane 的练习 2，引自同一页（书第 102 页）：

2. 设 η_x : x → G(p, F(x,p)) 为与
 参数。 x 中是自然的，但是 η 对应什么性质
 p 中附加词 (10) 的自然性？

答案是参数的特殊性——楔形条件。 的
 参数 p 处的单位是一系列从 OUT OF ONE OBJECT x 进入
 双函子 (p, q) ↦ G(p, F(x,q)) 的对角线，及其族
 满足 p 方自然性的形状是楔形。

为什么 [Theory/Dinatural.v] 的 [Dinatural] 不是车辆，而是测量的车辆
 比断言。 [Dinatural F G] 将两个双函子 C^op ∏ C ⟶ D 通过 a 关联起来
 家人在对角线上； 这里的源必须是 CONSTANT
 x 处的双函子，三个事实表明它是错误的包装。 （一）
 源是恒定的，这正是 [Structure/Wedge.v] 自己的情况
 标头说楔子是用来的。
(ii) 命名的常数函子常数是
 [Constant_Functor]（Instance/Fun/Terminal.v），并要求
 模块在该文件的传递性项目内闭包中花费了 28 个模块（68
 没有它，有它 96，通过将其添加到种子集来测量，并且
 重新计算 .Makefile.coq.d) — 尽管将其视为关于 a 的评论
 未采取的路线而不是障碍物，因为 [Diagonal]
 (Functor/Diagonal.v) 将常量函子作为其 OBJECT ACTION 且
 它的模块已经在边际成本为 0 的闭包中； 它不是一个
 直接插入，作为 [Program Instance]，其 [fobj] 不需要减少。
(三)
 即使给定一个
 常数双函子 — 1 是 5 行并且产生零义务，所以
 这是从树上编译出来的，而不是争论的——非自然性
 六边形在定义上不是楔形条件：它带有两个
 [fmap[Const]_]残基，各一个[∘ id]，其两侧交换。 测量并驳斥了这两种情况的识别
 [eq_refl] 出现 CONVERSION 错误（“无法统一”，无 Universe 子句），
 并且两者是可互导的，每个方向均由 [rewrite !id_right]
 其次是 [symmetry]。 所以 [Theory/Dinatural.v] 不是必需的
 锉刀和楔子是交付的形状。

基本形式是第一位的。 [pa_unit_dinatural] 陈述了方程
 没有类包装器，因此读者无需展开 [Wedge] 即可看到它； 和
 它是与宇宙标识无关的常数楔子
 包装携带（请参阅标题中的 Universes 段落）。 其证明
 是 [symmetry]，然后是 Adjunction/Conjugate.v 的一个应用程序
 [conjugate_to_unit] 在
 §C 的共轭对 — 也就是说，练习 2 的答案是 [ConjugateUnit]
 共轭的特征，#394 已经有名字了。

国家的镜子是 [pa_counit_extranatural]、[ConjugateCounit]
 在同一对上读取特征； 这是超自然现象/边缘
 条件。 它仅以基本形式交付 — 没有 [Cowedge] 实例
 已构建（请参阅标头的 NOT-DELIVERED 列表了解原因）。 
*)

Section UnitWedge.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA : ParametrizedAdjunction F).

Notation "'G'" := (pa_right PA) (only parsing).

(*
The unit and counit at a fixed parameter, named.  The [Adjunction] slot of
   [unit] and [counit] is IMPLICIT and cannot be inferred from a family, so
   both are written fully applied here and nowhere else in this section. 

--------
单位和计数单位以固定参数命名。 [Adjunction] 插槽
 [unit] 和 [counit] 是隐式的，无法从族中推断出来，因此
 两者都在这里完全应用，而在本节的其他地方都没有。 
*)

Definition pa_unit (p : P) (x : X) : x ~> G p (F (x, p)) :=
  @unit A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) x.

Definition pa_counit (p : P) (a : A) : F (G p a, p) ~> a :=
  @counit A X (Partial_l F p) (pa_right PA p) (pa_adj PA p) a.

(*
The bifunctor whose diagonal the unit runs into: (p, q) ↦ G(p, F(x, q)),
   contravariant in p through Theorem 3's G and covariant in q through the
   other partial functor of F.  Note [∏⟶] is at level 9 and binds TIGHTER
   than application, so the parentheses round [Partial_r F x] are required. 

--------
单位对角线遇到的双函子： (p, q) ↦ G(p, F(x, q))，
 p 通过定理 3 的 G 实现逆变，通过定理 3 的 G 实现 q 协变
 F 的其他部分函子。注意 [∏⟶] 处于级别 9 并且绑定更紧密
 比应用程序更重要，因此需要 [Partial_r F x] 周围的括号。 
*)

Definition UnitIntegrand (x : X) : P^op ∏ P ⟶ X :=
  parametrized_right_adjoint_bifunctor PA
    ◯ (Id[P^op] ∏⟶ (Partial_r F x)).

Example unit_integrand_obj (x : X) (p q : P) :
  fobj[UnitIntegrand x] (p, q) = G p (F (x, q)) := eq_refl.

(* Exercise 2's answer, elementarily.  Both sides run x ~> G p (F (x, p')).  / 基本上是练习 2 的答案。 双方运行 x ~>G p(F(x, p'))。*)

Lemma pa_unit_dinatural (x : X) {p p' : P} (h : p ~> p') :
  fmap[G p] (fmap[Partial_r F x] h) ∘ pa_unit p x
    ≈ pa_param_mate PA h (F (x, p')) ∘ pa_unit p' x.
Proof.
  symmetry.
  exact (conjugate_to_unit (pa_adj PA p') (pa_adj PA p)
           (param_transform F h) (pa_param_mate PA h)
           (conjugate_conj_mate (pa_adj PA p') (pa_adj PA p)
              (param_transform F h)) x).
Qed.

(*
And the same fact packaged in Structure/Wedge.v's own class.  The two
   normalisations below are DEFINITIONAL — each closes by [reflexivity] —
   and what they exhibit is that [bimap[UnitIntegrand x] id h] is
   [fmap[G p] (fmap[Partial_r F x] h) ∘ pa_param_mate PA id (F (x, p))] while
   [bimap[UnitIntegrand x] (op h) id] is
   [fmap[G p] (fmap[Partial_r F x] id) ∘ pa_param_mate PA h (F (x, q))].
   Clearing the three identity residues then leaves exactly
   [pa_unit_dinatural]. 

--------
同样的事实也封装在 Structure/Wedge.v 自己的类中。 两人
 下面的标准化是定义性的——每个都以 [reflexivity] 结束——
 他们展示的是 [bimap[UnitIntegrand x] id h] 是
 [fmap[G p] (fmap[Partial_r F x] h) ∘ pa_param_mate PA id (F (x, p))] while
 [bimap[UnitIntegrand x] (op h) id] 是
 [fmap[G p] (fmap[Partial_r F x] id) ∘ pa_param_mate PA h (F (x, q))]。 
清除三个身份残基然后准确地留下
 [pa_unit_dinatural]。 
*)

#[local] Obligation Tactic := idtac.

Program Definition pa_unit_Wedge (x : X) : Wedge (UnitIntegrand x) := {|
  wedge_obj := x;
  wedge_map := fun p => pa_unit p x
|}.
Next Obligation.
  intros x p q h.
  transitivity ((fmap[G p] (fmap[Partial_r F x] h)
                   ∘ pa_param_mate PA (id[p]) (F (x, p)))
                  ∘ pa_unit p x).
  { reflexivity. }
  transitivity ((fmap[G p] (fmap[Partial_r F x] (id[q]))
                   ∘ pa_param_mate PA h (F (x, q)))
                  ∘ pa_unit q x).
  2: { reflexivity. }
  rewrite (pa_param_mate_id_at PA (F (x, p))).
  rewrite (@fmap_id P A (Partial_r F x) q).
  rewrite (@fmap_id A X (G p) (F (x, q))).
  rewrite id_right, id_left.
  apply pa_unit_dinatural.
Qed.

#[local] Obligation Tactic := program_simpl.

Example pa_unit_Wedge_obj (x : X) : @wedge_obj _ _ _ (pa_unit_Wedge x) = x
  := eq_refl.

Example pa_unit_Wedge_map (x : X) (p : P) :
  @wedge_map _ _ _ (pa_unit_Wedge x) p = pa_unit p x := eq_refl.

(*
The counit's mirror: extranaturality in the parameter.  Both sides run
   F (G p' a, p) ~> a. 

--------
计数的镜子：参数中的超自然性。 双方都跑
 F (G p' a, p) ~> a。 
*)

Lemma pa_counit_extranatural (a : A) {p p' : P} (h : p ~> p') :
  pa_counit p' a ∘ fmap[Partial_r F (G p' a)] h
    ≈ pa_counit p a ∘ fmap[Partial_l F p] (pa_param_mate PA h a).
Proof.
  exact (conjugate_to_counit (pa_adj PA p') (pa_adj PA p)
           (param_transform F h) (pa_param_mate PA h)
           (conjugate_conj_mate (pa_adj PA p') (pa_adj PA p)
              (param_transform F h)) a).
Qed.

End UnitWedge.

Arguments pa_unit {X P A F} PA p x.
Arguments pa_counit {X P A F} PA p a.
Arguments UnitIntegrand {X P A F} PA x.

(** ** G. The unit/counit presentation, and the two triangle identities  / ** G. 单位/单位表示，以及两个三角形恒等式*)

(*
Mac Lane §IX.4 Exercise 2's scope increment, and the one thing to be clear
   about is WHAT IS NEW.  The two triangle (zig-zag) identities at a FIXED
   parameter are not new: they are Theory/Adjunction.v's [counit_fmap_unit]
   and [fmap_counit_unit] applied at [pa_adj PA p], and [pa_triangle_left]
   and [pa_triangle_right] below are those corollaries re-exposed with the
   parameter written out, so a reader sees Mac Lane's display
   ε_{p,F(x,p)} ∘ F(η_{p,x}, p) = 1 rather than an unindexed ε ∘ Fη = 1.
   The file does not claim them as new and their proofs are a bare [exact].

   WHAT IS NEW is the PARAMETRIZED PACKAGING and its EQUIVALENCE with §A.
   [ParametrizedAdjunctionTransform] is §A's record with the hom-set
   adjunction replaced by the unit/counit one, and
   [parametrized_adjunction_iff_transform] proves the two interderivable by
   applying Adjunction/Natural/Transformation/Universal.v's two passages
   pointwise in p — nothing about units or counits is re-derived.

   STRENGTHS, MEASURED STRICT FIRST.  The family of right adjoints survives
   both passages and the round trip AT LEIBNIZ EQUALITY ([pat_of_pa_right],
   [pa_of_pat_right], [pa_pat_round_right]), and so do the unit and counit
   COMPONENTS ([pat_unit_is_pa_unit], [pat_counit_is_pa_counit]) — the
   transform reading's unit at (p, x) IS [pa_unit PA p x] on the nose.  The
   WHOLE RECORD does not: [pa_of_pat (pat_of_pa PA) = PA] is refuted at
   [eq_refl] with a CONVERSION error ("cannot unify"), because
   [Adjunction_from_Transform] rebuilds the hom-set isomorphism out of the
   transposes rather than returning the one it was given.  Nor does the
   TRANSPOSE: the strict form is refuted the same way, and what holds is
   [pa_pat_round_to] / [pa_pat_round_from] at ≈, each a bare [exact] of
   [to_adj_unit] / [from_adj_counit] — so the round trip's cost is exactly
   the universal-arrow rewriting ⌊f⌋ ≈ fmap[U] f ∘ η, which is where
   Universal.v's forward map comes from.

   Together with §F this is the full unit/counit description of a
   parametrized adjunction: two triangles per parameter, plus the wedge
   condition on the unit and the extranaturality condition on the counit as
   the parameter varies. 

--------
Mac Lane §IX.4 练习 2 的范围增量，以及需要明确的一件事
 关于什么是新的。 FIXED 处的两个三角形（之字形）恒等式
 参数不是新的：它们是 Theory/Adjunction.v 的 [counit_fmap_unit]
 和 [fmap_counit_unit] 应用在 [pa_adj PA p] 和 [pa_triangle_left]
 下面的 [pa_triangle_right] 是那些重新暴露的推论
 参数写出，以便读者看到 Mac Lane 的显示
 ε_{p,F(x,p)} ∘ F(η_{p,x}, p) = 1 而不是未索引的 ε ∘ Fη = 1。 
该文件并没有声称它们是新的，而且它们的证明只是一个裸露的 [exact]。

新功能是参数化封装及其与 §A 的等效项。 
[ParametrizedAdjunctionTransform] 是 §A 的 hom-set 记录
 附属物被单位/单位一取代，并且
 [parametrized_adjunction_iff_transform] 证明两者可互导
 应用 Adjunction/Natural/Transformation/Universal.v 的两个段落
 p 中的逐点 — 不会重新导出有关单位或数量的内容。

强项，首先要严格衡量。 右伴随家族幸存
 两个通道和往返 AT LEIBNIZ EQUALITY ([pat_of_pa_right],
 [pa_of_pat_right]、[pa_pat_round_right]），单位和单位也是如此
 组件（[pat_unit_is_pa_unit]、[pat_counit_is_pa_counit]）—
 将 (p, x) 处的读数单位变换为鼻子上的 [pa_unit PA p x]。 的
 WHOLE RECORD 没有：[pa_of_pat (pat_of_pa PA) = PA] 被驳斥于
 [eq_refl] 出现转换错误（“无法统一”），因为
 [Adjunction_from_Transform] 重建 hom-set 同构
 转置而不是返回给定的值。 也没有
 TRANSPOSE：严格形式以同样的方式反驳，成立的是
 [pa_pat_round_to] / [pa_pat_round_from] 在 ≈，每一个裸 [exact] 的
 [to_adj_unit] / [from_adj_counit] — 所以往返费用正好是
 通用箭头重写 ⌊f⌋ ≈ fmap[U] f ∘ η，其中
 Universal.v的前向图来自。

与 §F 一起，这是一个完整的单位/单位描述
 参数化附加：每个参数两个三角形，加上楔形
 单位上的条件和单位上的超自然条件为
 参数不同。 
*)

Section PATransform.

Context {X P A : Category}.

Record ParametrizedAdjunctionTransform (F : X ∏ P ⟶ A) := {
  pat_right : P → (A ⟶ X);
  pat_adj (p : P) :
    PAT.Adjunction_Transform (Partial_l F p) (pat_right p)
}.

End PATransform.

Arguments ParametrizedAdjunctionTransform {X P A} F.
Arguments pat_right {X P A F} _ _.
Arguments pat_adj {X P A F} _ _.

Section PATransformPassages.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.

Definition pat_of_pa (PA : ParametrizedAdjunction F) :
  ParametrizedAdjunctionTransform F := {|
  pat_right := pa_right PA;
  pat_adj p := @Adjunction_to_Transform A X (Partial_l F p)
                 (pa_right PA p) (pa_adj PA p)
|}.

Definition pa_of_pat (PT : ParametrizedAdjunctionTransform F) :
  ParametrizedAdjunction F := {|
  pa_right := pat_right PT;
  pa_adj p := @Adjunction_from_Transform A X (Partial_l F p)
                (pat_right PT p) (pat_adj PT p)
|}.

Theorem parametrized_adjunction_iff_transform :
  ParametrizedAdjunction F ↔ ParametrizedAdjunctionTransform F.
Proof. split; [ exact pat_of_pa | exact pa_of_pat ]. Defined.

(* the family of right adjoints crosses both ways and round-trips strictly  / 右伴随族严格双向交叉和往返*)

Example pat_of_pa_right (PA : ParametrizedAdjunction F) :
  pat_right (pat_of_pa PA) = pa_right PA := eq_refl.

Example pa_of_pat_right (PT : ParametrizedAdjunctionTransform F) :
  pa_right (pa_of_pat PT) = pat_right PT := eq_refl.

Example pa_pat_round_right (PA : ParametrizedAdjunction F) :
  pa_right (pa_of_pat (pat_of_pa PA)) = pa_right PA := eq_refl.

(* so do the unit and counit components  / 单元和单元组件也是如此*)

Example pat_unit_is_pa_unit (PA : ParametrizedAdjunction F) (p : P) (x : X) :
  transform[@PAT.unit A X (Partial_l F p) (pa_right PA p)
              (pat_adj (pat_of_pa PA) p)] x = pa_unit PA p x := eq_refl.

Example pat_counit_is_pa_counit
        (PA : ParametrizedAdjunction F) (p : P) (a : A) :
  transform[@PAT.counit A X (Partial_l F p) (pa_right PA p)
              (pat_adj (pat_of_pa PA) p)] a = pa_counit PA p a := eq_refl.

(*
the transposes survive only up to ≈, and the residue is exactly the
   universal-arrow rewriting 

--------
转置仅存活到 ≈，而剩余部分正是
 通用箭头重写 
*)

Lemma pa_pat_round_to (PA : ParametrizedAdjunction F)
      (p : P) (x : X) (a : A) (k : F (x, p) ~> a) :
  pa_to (pa_of_pat (pat_of_pa PA)) p x a k ≈ pa_to PA p x a k.
Proof.
  symmetry.
  exact (@to_adj_unit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x a k).
Qed.

Lemma pa_pat_round_from (PA : ParametrizedAdjunction F)
      (p : P) (x : X) (a : A) (g : x ~> pa_right PA p a) :
  pa_from (pa_of_pat (pat_of_pa PA)) p x a g ≈ pa_from PA p x a g.
Proof.
  symmetry.
  exact (@from_adj_counit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x a g).
Qed.

(* --- the two triangle identities, in parametrized form ---  / --- 两个三角形恒等式，参数化形式 ---*)

Theorem pa_triangle_left (PA : ParametrizedAdjunction F) (p : P) (x : X) :
  pa_counit PA p (F (x, p)) ∘ fmap[Partial_l F p] (pa_unit PA p x)
    ≈ id[F (x, p)].
Proof.
  exact (@counit_fmap_unit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x).
Qed.

Theorem pa_triangle_right (PA : ParametrizedAdjunction F) (p : P) (a : A) :
  fmap[pa_right PA p] (pa_counit PA p a) ∘ pa_unit PA p (pa_right PA p a)
    ≈ id[pa_right PA p a].
Proof.
  exact (@fmap_counit_unit A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) a).
Qed.

End PATransformPassages.

(** ** H. Riehl §4.4 Proposition 4.4.6(iii): mutual right adjointness  / ** H. Riehl §4.4 命题 4.4.6(iii)：互右伴随性*)

(*
Riehl, "Category Theory in Context", 2nd ed., §4.4 Proposition 4.4.6.
   Given a bifunctor F : X ∏ P ⟶ A with BOTH pointwise families of right
   adjoints — §A's (right adjoints to F(−,p), assembling G : P^op ∏ A ⟶ X)
   and the mirror one (right adjoints to F(x,−), assembling
   H : X^op ∏ A ⟶ P) — the two assembled bifunctors are MUTUALLY RIGHT
   ADJOINT in the remaining variable: for each c ∈ A,

       P(p, H(x, c))  ≅  X(x, G(p, c)),

   naturally in p and x.  That is Riehl's B(b, G(a,c)) ≅ A(a, H(b,c)) with
   the letters of this file.  Riehl's Exercise 4.4.ii IS this proposition —
   it asks for exactly the two-variable adjunction the proposition supplies —
   so it is NOT separate work and nothing further is built for it.

   IT IS AN INHABITANT OF THE TREE'S OWN CLASS, NOT A LOOKALIKE:
   [mutually_right_adjoint : AdjointOnTheRight mr_left mr_right] with
   [mr_left  := Partial_l (parametrized_right_adjoint_bifunctor PA)  c]
   [mr_right := Partial_l (parametrized_right_adjoint_bifunctor MPA) c]
   over Adjunction/Right.v's class, and it is a RECORD LITERAL with no
   tactic — its five fields are [mr_iso] and the four naturality lemmas
   above it, applied.  The type
   assignment was verified to typecheck before any proof was written:
   [mr_left : P^op ⟶ X] and [mr_right : X^op ⟶ P] are the class's S and T
   with its A := P and X := X, and the class's [aor {a x}] then reads
   between hom P a (T x) and hom X x (S a), which are the two hom-setoids
   displayed above ([mr_left_obj], [mr_right_obj], both [eq_refl]).

   THE MIRROR HYPOTHESIS NEEDS NO NEW RECORD, and the brief's conjecture that
   [Partial_l (F ◯ Swap) x] is [Partial_r F x] is MEASURED: both DATA fields
   agree at [eq_refl] ([mirror_partial_obj], [mirror_partial_fmap]), so
   [ParametrizedAdjunction (F ◯ Swap)] IS the mirror hypothesis.  The two
   functors are not equal as RECORDS — [Partial_l] and [Partial_r] rebuild
   their three law fields as separate Program obligations, the same
   measurement §D records — so an adjunction stated at one does not ascribe
   at the other, and [mirror_transport] is the field-copy that crosses it;
   it works only because every [Adjunction] field mentions its left adjoint
   solely through F x and fmap[F] g, both of which convert.  [mirror_family]
   packages a family stated in the natural [Partial_r F x ⊣ H x] form into
   the record, so the HYPOTHESIS a consumer supplies mentions no [Swap] —
   the record's type still does, since it is [ParametrizedAdjunction
   (F ◯ Swap)] and no second record is introduced.

   BOTH SIDES ARE A(F(x,p), c), which is why the isomorphism costs nothing:
   [mr_to] is §A's transpose at the parameter p composed with the MIRROR's
   inverse transpose at the parameter x, [mr_from] is the other composite,
   and the two round trips are the two adjunctions' own comp laws.

   THE FOUR NATURALITY FIELDS COME FROM THE THREE-VARIABLE NATURALITY of §C,
   and only TWO of them are proved directly.  [mr_to_nat_a] is Mac Lane's
   square for PA ([pa_natural_p]) after one [from_adj_nat_l] of MPA;
   [mr_to_nat_x] is Mac Lane's square for MPA read through the inverse
   transposes ([pa_square_iff_from], §C) after one [pa_natural_x] of PA.  The
   two [from] fields are then obtained by CONJUGATING those two with the
   isomorphism — apply [mr_from] to both sides and cancel with the round
   trips — so no third and fourth naturality argument is run.

   The arrow actions of the two functors are the two mates up to the residue
   [fmap[_] id] that [Partial_l] of the bifunctor leaves behind
   ([mr_left_fmap], [mr_right_fmap], both [eq_refl], with
   [mr_left_fmap_is_mate] and [mr_right_fmap_is_mate] clearing it). 

--------
Riehl，“语境中的范畴论”，第二版，§4.4 命题 4.4.6。 
给定一个双函子 F : X ∏ P ⟶ A ，具有两个右族点族
 伴随 — §A（F(−,p) 的右伴随，组装 G : P^op ∏ A ⟶ X）
 和镜像一（右邻 F(x,−)，组装
 H : X^op ∏ A ⟶ P) — 两个组装的双函子是互为对的
 剩余变量中的 ADJOINT：对于每个 c ∈ A，

P(p, H(x, c)) ≅ X(x, G(p, c)),

自然地在p和x中。 这就是 Riehl 的 B(b, G(a,c)) ≅ A(a, H(b,c)) ，其中
 该文件的字母。 Riehl 的练习 4.4.ii 是这个命题 —
 它要求的正是该命题提供的二变量附加词——
 所以它不是单独的工作，也没有为它构建任何进一步的东西。

它是树本身类别的居民，而不是长得很像的：
 [mutually_right_adjoint : AdjointOnTheRight mr_left mr_right] 与
 保护1X
 保护2X
 在 Adjunction/Right.v 的类上，它是一个记录文字，没有
 策略 — 它的五个字段是 [mr_iso] 和四个自然引理
 在其上方，应用。 类型
 在编写任何证明之前，作业已通过类型检查进行了验证：
 [mr_left : P^op ⟶ X] 和 [mr_right : X^op ⟶ P] 是该级别的 S 和 T
 其 A := P 和 X := X，然后该类的 [aor {a x}] 读取
 hom P a (T x) 和 hom X x (S a) 之间，这是两个 hom-setoid
 上面显示（[mr_left_obj]、[mr_right_obj]、均为 [eq_refl]）。

镜子假说不需要新的记录，简报的猜想是
 [Partial_l (F ◯ Swap) x] 是 [Partial_r F x] 已测量：两个数据字段
 同意 [eq_refl]（[mirror_partial_obj]，[mirror_partial_fmap]），所以
 [ParametrizedAdjunction (F ◯ Swap)] 是镜像假设。 两人
 函子与 RECORDS 不相等 — [Partial_l] 和 [Partial_r] 重建
 他们的三个法律领域作为单独的计划义务，相同
 测量 §D 记录 — 因此，其中所述的附加项并不归因
 另一方面，[mirror_transport] 是穿过它的现场副本；
 它起作用只是因为每个 [Adjunction] 字段都提到了它的左伴随
 仅通过 F x 和 fmap[F] g，两者都进行转换。 保护21X
 将自然 [Partial_r F x ⊣ H x] 形式中声明的族封装成
 记录，因此消费者提供的假设没有提及 [Swap] —
 记录的类型仍然如此，因为它是 [ParametrizedAdjunction
 (F ◯ Swap)]且不引入第二条记录。

两边都是 A(F(x,p), c)，这就是同构不需要任何成本的原因：
 [mr_to] 是 §A 在参数 p 处的转置，由 MIRROR 组成
 参数 x 处的逆转置，[mr_from] 是另一种组合，
 两次往返是两个附属物自己的补偿法则。

四个自然场来自 §C 的三变量自然性，
 并且只有其中两个被直接证明。 [mr_to_nat_a] 是 Mac Lane 的
 MPA 的一个 [from_adj_nat_l] 后，PA ([pa_natural_p]) 平方；
 [mr_to_nat_x] 是 Mac Lane 的 MPA 平方读取逆矩阵
 在 PA 的一个 [pa_natural_x] 之后转置 ([pa_square_iff_from], §C)。 的
 然后通过将这两个字段与
 同构 — 将 [mr_from] 应用于两侧并用圆取消
 旅行 - 所以没有第三和第四个自然性论证。

两个函子的箭头动作是直到残数的两个配合
 双函数器的 [Partial_l] 留下的 [fmap[_] id]
 （[mr_left_fmap]、[mr_right_fmap]、均为 [eq_refl]，具有
 [mr_left_fmap_is_mate] 和 [mr_right_fmap_is_mate] 清除它）。 
*)

Section MirrorFamily.

Context {X P A : Category}.
Context (F : X ∏ P ⟶ A).

Example mirror_partial_obj (x : X) (p : P) :
  fobj[Partial_l (F ◯ @Swap P X) x] p = fobj[Partial_r F x] p := eq_refl.

Example mirror_partial_fmap (x : X) {p p' : P} (h : p ~> p') :
  fmap[Partial_l (F ◯ @Swap P X) x] h = fmap[Partial_r F x] h := eq_refl.

Definition mirror_transport (x : X) (U : A ⟶ P)
  (Adj : Partial_r F x ⊣ U) : Partial_l (F ◯ @Swap P X) x ⊣ U :=
  @Build_Adjunction A P (Partial_l (F ◯ @Swap P X) x) U
    (@adj            _ _ _ _ Adj)
    (@to_adj_nat_l   _ _ _ _ Adj)
    (@to_adj_nat_r   _ _ _ _ Adj)
    (@from_adj_nat_l _ _ _ _ Adj)
    (@from_adj_nat_r _ _ _ _ Adj).

Definition mirror_family (H : X → (A ⟶ P))
  (Adjs : ∀ x : X, Partial_r F x ⊣ H x)
  : ParametrizedAdjunction (F ◯ @Swap P X) :=
  {| pa_right := H; pa_adj := fun x => mirror_transport x (H x) (Adjs x) |}.

Example mirror_family_right (H : X → (A ⟶ P))
        (Adjs : ∀ x : X, Partial_r F x ⊣ H x) :
  pa_right (mirror_family H Adjs) = H := eq_refl.

End MirrorFamily.

Arguments mirror_transport {X P A} F x U Adj.
Arguments mirror_family {X P A} F H Adjs.

Section MutuallyRight.

Context {X P A : Category}.
Context {F : X ∏ P ⟶ A}.
Context (PA  : ParametrizedAdjunction F).
Context (MPA : ParametrizedAdjunction (F ◯ @Swap P X)).
Context (c : A).

Definition mr_left  : P^op ⟶ X :=
  Partial_l (parametrized_right_adjoint_bifunctor PA) c.
Definition mr_right : X^op ⟶ P :=
  Partial_l (parametrized_right_adjoint_bifunctor MPA) c.

Example mr_left_obj (p : P) : mr_left p = pa_right PA p c := eq_refl.
Example mr_right_obj (x : X) : mr_right x = pa_right MPA x c := eq_refl.

Example mr_left_fmap {p p' : P} (g : p' ~> p) :
  fmap[mr_left] g
    = fmap[pa_right PA p'] (id[c]) ∘ pa_param_mate PA g c := eq_refl.

Example mr_right_fmap {x x' : X} (k : x ~> x') :
  fmap[mr_right] k
    = fmap[pa_right MPA x] (id[c]) ∘ pa_param_mate MPA k c := eq_refl.

Lemma mr_left_fmap_is_mate {p p' : P} (g : p' ~> p) :
  fmap[mr_left] g ≈ pa_param_mate PA g c.
Proof.
  transitivity (fmap[pa_right PA p'] (id[c]) ∘ pa_param_mate PA g c).
  { reflexivity. }
  rewrite fmap_id; now rewrite id_left.
Qed.

Lemma mr_right_fmap_is_mate {x x' : X} (k : x ~> x') :
  fmap[mr_right] k ≈ pa_param_mate MPA k c.
Proof.
  transitivity (fmap[pa_right MPA x] (id[c]) ∘ pa_param_mate MPA k c).
  { reflexivity. }
  rewrite fmap_id; now rewrite id_left.
Qed.

(* the two [Swap] reductions the naturality proofs consume  / 自然性证明消耗的两个 [Swap] 减少*)

Example mr_swap_fmap_l (x : X) {p p' : P} (g : p ~> p') :
  fmap[Partial_l (F ◯ @Swap P X) x] g = fmap[Partial_r F x] g := eq_refl.

Example mr_swap_fmap_r (p : P) {x x' : X} (k : x ~> x') :
  fmap[Partial_r (F ◯ @Swap P X) p] k = fmap[Partial_l F p] k := eq_refl.

(* the bijection, as the composite of the two transposes  / 双射，作为两个转置的复合*)

Definition mr_to (p : P) (x : X) (g : p ~> pa_right MPA x c)
  : x ~> pa_right PA p c :=
  pa_to PA p x c (pa_from MPA x p c g).

Definition mr_from (p : P) (x : X) (g : x ~> pa_right PA p c)
  : p ~> pa_right MPA x c :=
  pa_to MPA x p c (pa_from PA p x c g).

Lemma mr_to_respects (p : P) (x : X) :
  Proper (equiv ==> equiv) (mr_to p x).
Proof. intros g g' E; unfold mr_to, pa_to, pa_from; now rewrite E. Qed.

Lemma mr_from_respects (p : P) (x : X) :
  Proper (equiv ==> equiv) (mr_from p x).
Proof. intros g g' E; unfold mr_from, pa_to, pa_from; now rewrite E. Qed.

Lemma mr_to_from (p : P) (x : X) (g : x ~> pa_right PA p c) :
  mr_to p x (mr_from p x g) ≈ g.
Proof.
  unfold mr_to, mr_from, pa_to, pa_from.
  rewrite (@to_adj_comp_law A P (Partial_l (F ◯ @Swap P X) x)
             (pa_right MPA x) (pa_adj MPA x) p c).
  exact (@from_adj_comp_law A X (Partial_l F p)
           (pa_right PA p) (pa_adj PA p) x c g).
Qed.

Lemma mr_from_to (p : P) (x : X) (g : p ~> pa_right MPA x c) :
  mr_from p x (mr_to p x g) ≈ g.
Proof.
  unfold mr_to, mr_from, pa_to, pa_from.
  rewrite (@to_adj_comp_law A X (Partial_l F p)
             (pa_right PA p) (pa_adj PA p) x c).
  exact (@from_adj_comp_law A P (Partial_l (F ◯ @Swap P X) x)
           (pa_right MPA x) (pa_adj MPA x) p c g).
Qed.

#[local] Obligation Tactic := idtac.

Program Definition mr_iso (p : P) (x : X) :
  @Isomorphism Sets
    {| carrier := @hom P p (mr_right x)
     ; is_setoid := @homset P p (mr_right x) |}
    {| carrier := @hom X x (mr_left p)
     ; is_setoid := @homset X x (mr_left p) |} :=
  {| to   := {| morphism := mr_to p x |}
   ; from := {| morphism := mr_from p x |} |}.
Next Obligation. intros p x; exact (mr_to_respects p x). Qed.
Next Obligation. intros p x; exact (mr_from_respects p x). Qed.
Next Obligation. intros p x g; exact (mr_to_from p x g). Qed.
Next Obligation. intros p x g; exact (mr_from_to p x g). Qed.

#[local] Obligation Tactic := program_simpl.

(* naturality in the parameter: Mac Lane's square for PA  / 参数的自然性：Mac Lane 的 PA 平方*)

Lemma mr_to_nat_a {p p' : P} {x : X} (f : p ~> mr_right x) (g : p' ~> p) :
  mr_to p' x (f ∘ g) ≈ fmap[mr_left] g ∘ mr_to p x f.
Proof.
  unfold mr_to.
  transitivity (pa_to PA p' x c
                  (pa_from MPA x p c f ∘ fmap[Partial_r F x] g)).
  { apply (@to_adj_respects A X (Partial_l F p')
             (pa_right PA p') (pa_adj PA p') x c).
    exact (@from_adj_nat_l A P (Partial_l (F ◯ @Swap P X) x)
             (pa_right MPA x) (pa_adj MPA x) p' p c f g). }
  rewrite (pa_natural_p PA g x c (pa_from MPA x p c f)).
  apply compose_respects; [| reflexivity ].
  symmetry; apply mr_left_fmap_is_mate.
Qed.

(*
naturality in the other variable: Mac Lane's square for MPA, read through
   the inverse transposes, then PA's naturality in x 

--------
另一个变量的自然性：Mac Lane 的 MPA 平方，通读
 逆转置，则 PA 在 x 中的自然性 
*)

Lemma mr_to_nat_x {p : P} {x x' : X} (f : p ~> mr_right x') (k : x ~> x') :
  mr_to p x (fmap[mr_right] k ∘ f) ≈ mr_to p x' f ∘ k.
Proof.
  unfold mr_to.
  transitivity (pa_to PA p x c
                  (pa_from MPA x p c (pa_param_mate MPA k c ∘ f))).
  { apply (@to_adj_respects A X (Partial_l F p)
             (pa_right PA p) (pa_adj PA p) x c).
    apply (@from_adj_respects A P (Partial_l (F ◯ @Swap P X) x)
             (pa_right MPA x) (pa_adj MPA x) p c).
    apply compose_respects; [| reflexivity ].
    apply mr_right_fmap_is_mate. }
  transitivity (pa_to PA p x c
                  (pa_from MPA x' p c f ∘ fmap[Partial_l F p] k)).
  { apply (@to_adj_respects A X (Partial_l F p)
             (pa_right PA p) (pa_adj PA p) x c).
    exact (fst (pa_square_iff_from MPA k (pa_param_mate MPA k))
             (pa_natural_p MPA k) p c f). }
  exact (pa_natural_x PA p (pa_from MPA x' p c f) k).
Qed.

(*
the two inverse readings, by conjugating the two above with the
   isomorphism; no further naturality argument is run 

--------
两个相反的读数，通过将上面的两个与
 同构； 没有进一步的自然性论证 
*)

Lemma mr_from_nat_a {p p' : P} {x : X} (q : x ~> mr_left p) (g : p' ~> p) :
  mr_from p' x (fmap[mr_left] g ∘ q) ≈ mr_from p x q ∘ g.
Proof.
  transitivity (mr_from p' x (mr_to p' x (mr_from p x q ∘ g))).
  - apply mr_from_respects.
    rewrite (mr_to_nat_a (mr_from p x q) g).
    apply compose_respects; [ reflexivity |].
    symmetry; apply mr_to_from.
  - apply mr_from_to.
Qed.

Lemma mr_from_nat_x {p : P} {x x' : X} (q : x' ~> mr_left p) (k : x ~> x') :
  mr_from p x (q ∘ k) ≈ fmap[mr_right] k ∘ mr_from p x' q.
Proof.
  transitivity (mr_from p x (mr_to p x (fmap[mr_right] k ∘ mr_from p x' q))).
  - apply mr_from_respects.
    rewrite (mr_to_nat_x (mr_from p x' q) k).
    apply compose_respects; [| reflexivity ].
    symmetry; apply mr_to_from.
  - apply mr_from_to.
Qed.

Definition mutually_right_adjoint : AdjointOnTheRight mr_left mr_right :=
  {| aor := mr_iso
   ; to_aor_nat_a := fun p p' x f g => mr_to_nat_a f g
   ; to_aor_nat_x := fun p x x' f k => mr_to_nat_x f k
   ; from_aor_nat_a := fun p p' x q g => mr_from_nat_a q g
   ; from_aor_nat_x := fun p x x' q k => mr_from_nat_x q k |}.

Example mr_aor_is_iso (p : P) (x : X) :
  @aor P X mr_left mr_right mutually_right_adjoint p x = mr_iso p x
  := eq_refl.

Example mr_aor_to_is_mr_to (p : P) (x : X) (g : p ~> mr_right x) :
  to (@aor P X mr_left mr_right mutually_right_adjoint p x) g
    = mr_to p x g := eq_refl.

Example mr_aor_from_is_mr_from (p : P) (x : X) (g : x ~> mr_left p) :
  from (@aor P X mr_left mr_right mutually_right_adjoint p x) g
    = mr_from p x g := eq_refl.

End MutuallyRight.

Arguments mr_left {X P A F} PA c.
Arguments mr_right {X P A F} MPA c.
Arguments mr_to {X P A F} PA MPA c p x g.
Arguments mr_from {X P A F} PA MPA c p x g.
Arguments mutually_right_adjoint {X P A F} PA MPA c.
