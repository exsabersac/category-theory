Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(*
Lib.v sets [Default Proof Using "Type"], which keeps only the section
   variables occurring in a statement.  The additivity hypotheses here
   ([AU], [AF]) occur only in the PROOFS of the lemmas that consume
   them, those statements being equations between morphisms that
   mention no functor class, so they would be discarded.  "All"
   retains them, the Theory/EckmannHilton.v and
   Theory/Category/Monoid.v precedent. 

--------
Lib.v 设置 [Default Proof Using "Type"]，仅保留该部分
 语句中出现的变量。 这里的可加性假设
 （[AU]、[AF]）仅出现在消耗的引理的 PROOFS 中
 它们，这些陈述是态射之间的方程
 没有提及函子类，因此它们将被丢弃。 “全部”
 保留它们，Theory/EckmannHilton.v 和
 理论/类别/Monoid.v 先例。 
*)
Local Set Default Proof Using "All".

(** * Adjunctions between Ab-categories are additive

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.1 Theorem 3 (printed p. 85) [maclane:IV.1:thm3]: if C and D
    are Ab-categories, U : C ⟶ D is an additive functor, and F ⊣ U,
    then the left adjoint F is itself additive and the adjunction
    bijection

        F x ~{C}~> y   ≅   x ~{D}~> U y

    is an isomorphism of ABELIAN GROUPS, not merely of sets.  Dually,
    a right adjoint of an additive functor is additive.
    nLab: https://ncatlab.org/nlab/show/additive+functor
          https://ncatlab.org/nlab/show/adjoint+functor

    THE CLASS IS CONSUMED, NOT BUILT.  The catalog issue behind this
    file records the tree as having no notion of an additive functor.
    That is FALSE, and the correction is not a matter of naming:
    [AdditiveFunctor] is declared at Structure/AbCategory.v with
    preservation of [padd] as its ONLY field, and that file already
    proves the two clauses a reader would expect to owe here —
    [fmap_pzero] ("whence T0 = 0", by the idempotency
    cancellation [padd_idem_zero]) and [fmap_abneg] (by
    uniqueness of additive inverses) — as well as the closure
    instances [Id_AdditiveFunctor] and
    [Compose_AdditiveFunctor].  Nothing in this file redefines
    or reproves any of them; the pzero and abneg clauses below are
    applications of those two theorems.

    WHAT IS PROVED, AND IN WHICH ORDER.

    (1) THE TRANSPOSES ARE ADDITIVE.  With F ⊣ U and U additive,
        [to_adj_padd] proves ⌊padd a b⌋ ≈ padd ⌊a⌋ ⌊b⌋, with
        [to_adj_pzero] and [to_adj_abneg] the unit and negation
        clauses.  The route is the in-tree [to_adj_unit], which
        recovers ⌊f⌋ ≈ fmap[U] f ∘ η, followed by [fmap_padd] for U
        and [compose_padd_right] — so the transpose is additive
        because U is and because composition is bilinear, which is
        exactly Mac Lane's sentence.  The mirror [from_adj_padd] and
        its two siblings run through [from_adj_counit] and
        [compose_padd_left], and require F additive instead.

    (2) THEOREM 3 ITSELF.  [left_adjoint_additive] takes an
        [AdditiveFunctor U] and a F ⊣ U and produces an
        [AdditiveFunctor F] — a genuine inhabitant of the class, so
        it composes with [Compose_AdditiveFunctor] and can be fed to
        anything demanding additivity, rather than being a bare
        equation.  The proof compares the two transposes: both
        fmap[F] (padd f g) and padd (fmap[F] f) (fmap[F] g) transpose
        to padd (η ∘ f) (η ∘ g), the first by [fmap_from_adj_unit]
        and [compose_padd_left], the second by clause (1); the
        conclusion is then injectivity of ⌊−⌋, which is [adj_to_inj],
        a two-line consequence of [to_adj_comp_law].

    (3) THE HOM-GROUP ISOMORPHISM.  Mac Lane's conclusion is a PAIR
        of claims and this file delivers both halves separately as
        well as packaged.  [hom_ab] reads each hom-setoid of an
        Ab-category that is LOCALLY PROPOSITIONAL — a hypothesis
        this clause did not carry before; see the strength-change
        paragraph below — as an [Instance/Ab.v] [AbObject] — its
        commutative-monoid part is [padd]/[pzero] and its negation is
        [abneg], every law being a field or corollary of
        [AbEnriched] — and [adj_hom_ab_iso] exhibits the adjunction
        bijection as an [@Isomorphism Ab], the two legs being ⌊−⌋ and
        ⌈−⌉ as [AbHom]s and the two round trips being
        [to_adj_comp_law] and [from_adj_comp_law] verbatim.  So the
        landing place is the tree's own category of abelian groups
        rather than a bespoke record.  An earlier draft of this header
        said the packaging COSTS a universe identification; measuring
        it refutes that — [adj_hom_ab_iso]'s constraint block carries
        the same identification its unpackaged counterpart does and no
        other — and the corrected reading is the universe paragraph
        below.

    (4) THE DUAL.  [right_adjoint_additive]: if F ⊣ U and F is
        additive then U is.  It is obtained by transport rather than
        by a second argument, and the transport needed a
        construction the tree did not have: nothing anywhere
        inhabits [Preadditive (C^op)] or [AbEnriched (C^op)] —
        searching for the application shape rather than for a name,
        the only hit outside this file is Structure/Preadditive.v's
        PROSE remark that the laws are self-dual, which is a sentence
        and not a term.  [Preadditive_op]
        and [AbEnriched_op] supply them here — every field is the
        original field, with [compose_padd_left] and
        [compose_padd_right] exchanged and likewise the two absorption
        laws, since composition in C^op is C's flipped — and
        [AdditiveFunctor_op]/[AdditiveFunctor_unop] carry additivity
        across [Opposite_Functor] in both directions.  Theorem 3 at
        [Opposite_Adjunction] then reads off the dual.

    (5) RIEHL'S COROLLARY 4.6.9, PARTLY — and note which hypothesis is
        assumed rather than derived: Riehl's point is that in a
        SEMIADDITIVE setting the enrichment comes for free, finite
        direct sums being simultaneously finite products and
        coproducts, whereas [left_adjoint_additive_of_biproducts]
        ASSUMES [AbEnriched C] and [AbEnriched D] and derives only the
        ADDITIVITY OF THE ADJOINT.  Deriving the enrichment from
        semiadditivity is not attempted.  See the section below for
        exactly what lands and what does not; the summary is that the
        biproduct bridge asked for is delivered in the orientation the
        adjunction supplies, and the semiadditive corollary is stated
        with the biproducts of the source category as an explicit
        hypothesis rather than derived from a completeness assumption.

    UNIVERSES, MEASURED OFF BOTH THE BINDER AND THE CONSTRAINT BLOCK.
    Two identifications are present and NEITHER is introduced here.
    (a) Every constant in this file is over C : Category@{u u0 u0} —
    hom identified with PROOF — inherited from the donor classes,
    which are declared that way: [AbEnriched@{u u0}] and
    [Preadditive@{u u0}] each take a [Category@{u u0 u0}], as do
    [ZeroObject] and [Biproduct].  That list is not exhaustive:
    [adj_to_inj] and [adj_from_inj] mention none of those four and
    carry the identification anyway, and measured under
    [Constraint ch < cp] the donor there is [Adjunction] (rejected),
    while [Functor] at those levels is ACCEPTED and so is not one.
    The blanket statement holds; the attribution is per-constant.

    (b) Every result whose statement mentions ⊣ ADDITIONALLY
    identifies the two categories' hom-and-proof universes with each
    other, [to_adj_padd] and [left_adjoint_fmap_padd] both carrying
    [u0 = u2].  That identification has AT LEAST THREE INDEPENDENT
    DONORS and no single one of them is "the" cause.  Measured in a
    section declaring [Constraint bh < ah] — which satisfies the bound
    [bh <= ah] while violating the equation — with C and D at those
    levels: (i) [AdditiveFunctor] ALONE is rejected, with ONE functor
    in the command and no adjunction anywhere, because its binder
    reuses a single level for BOTH categories' hom-and-proof while its
    own constraint block is EMPTY — this file's second instance of the
    binder/block trap named below — and BOTH cited statements take an
    [AdditiveFunctor U] hypothesis, so this donor alone accounts for
    their [u0 = u2]; (ii) merely having functors in BOTH directions is
    rejected too, [Functor] forcing source-hom ≤ target-hom, so
    F : D ⟶ C together with U : C ⟶ D forces equality with no
    adjunction present; (iii) [Adjunction] is rejected as well, and is
    the third of the three.

    An earlier revision of this header claimed the identification was
    the [Adjunction] class's and that the attribution DISCRIMINATED,
    citing [fmap_padd_of_preserved_coproduct] — which mentions both
    categories through a functor, mentions no adjunction, and carries
    only the BOUND [u2 <= u0].  That control is real and IS accepted at
    those levels, but it does NOT discriminate: it removes all three
    donors at once (one functor rather than two, [Preadditive] in
    place of [AbEnriched], and no [AdditiveFunctor]), so it is a
    control for "one functor", not for "adjunction versus no
    adjunction".  The claim is withdrawn.  Test/ProbeAdditive349.v now
    pins all three donors as FORMABILITY negatives beside that
    accepted control, so the measurement is guarded rather than merely
    recorded.

    So the Ab packaging costs nothing in identifications:
    [adj_hom_ab_iso] carries the same [u0 = u2] its unpackaged
    counterpart does, plus one fresh strict inequality for the
    [Isomorphism]'s own universe.  [hom_ab] itself is this file's
    sharpest instance of the binder/block trap: its constraint block
    is LITERALLY EMPTY while its binder reads [Category@{u0 u u}], so
    a reader who checks only the block concludes "no identification"
    and is wrong.  None of this is claimed unavoidable; no
    re-annotation of any donor was attempted.

    STRENGTHS, MEASURED STRICT-FIRST.  Every readback was attempted at
    [eq_refl] before being stated at ≈, and TWELVE hold and are
    shipped as [Example]s so the claims are machine-checked rather
    than asserted: both legs of the
    packaged group isomorphism ARE the transposes
    ([adj_hom_ab_iso_to]/[_from]); all four data fields of [hom_ab]
    are the enrichment's own ([hom_ab_carrier], [hom_ab_plus],
    [hom_ab_zero], [hom_ab_neg]); the opposite enrichment is the
    original read at swapped endpoints ([padd_op_is_padd],
    [abneg_op_is_abneg]) — which is why the dual costs no proof; the
    biproduct bridge keeps the data it is handed
    ([bridge_inl_strict]); and the image biproduct's object and
    structure maps are the F-images on the nose
    ([image_biproduct_obj], [image_biproduct_inl],
    [image_biproduct_exl]).

    What was attempted strict and REJECTED, and is therefore stated
    at ≈, is every equation whose two sides differ by a rewriting.
    Three were measured in particular: transpose additivity
    ([to_adj_padd]'s statement at [eq_refl]), Theorem 3's own field
    ([left_adjoint_fmap_padd]), and the coproduct-diagonal
    factorization ([padd_copair_diag]).  Read that at exactly its
    strength: those three were MEASURED, in a scratch file compiled
    against this one, and are NOT guarded by a [Fail] here — nothing
    in this file would notice if a later change made one of them
    definitional.  No claim is made that any of them could be
    strengthened; [padd] is an abstract field of a class, so nothing
    about it reduces.

    A RECORDED STRENGTH CHANGE: TEN STATEMENTS HERE CARRY A
    HYPOTHESIS THEY DID NOT CARRY BEFORE.  An earlier revision of
    this header stated clause (3) unconditionally — "an adjunction
    between Ab-enriched categories induces an isomorphism of
    hom-groups", with [hom_ab] read off any [AbEnriched C].  Since
    the PR "algebraic carriers are sets" (2026-09-17) an [AbObject]
    carries [cmon_prop], a [PropEquiv] for its carrier setoid, and
    [hom_ab]'s carrier IS [C]'s hom-setoid; an arbitrary category
    supplies no [Prop] mirror of its `≈`, [Cat] being the standing
    counterexample, where an [F ≈ G] is itself a family of
    isomorphisms (Lib/Setoid/Propositional.v,
    Instance/Sets/Propositional.v's header).  So the hypothesis sits
    exactly at the PASSAGE from the internal enrichment to the
    concrete record, and nowhere else: [AbEnriched] and
    [Preadditive] are untouched and keep the ambient `≈`, which is
    the SCOPE paragraph of Structure/Complete.v's size note (item 4)
    read at this file.

    The ten: [hom_ab], [hom_ab_carrier], [hom_ab_plus],
    [hom_ab_zero] and [hom_ab_neg] take
    [{LP : LocallyPropositional C}]; [adj_to_ab], [adj_from_ab],
    [adj_hom_ab_iso], [adj_hom_ab_iso_to] and [adj_hom_ab_iso_from]
    take it on BOTH categories ([LPC] and [LPD]), the isomorphism's
    two ends being hom-groups of C and of D.  Nothing else in this
    file changed statement — the transpose-additivity lemmas,
    [left_adjoint_additive], [right_adjoint_additive] and the
    biproduct section read as they did.  [LocallyPropositional] is a
    class, so every concrete ambient discharges it by resolution:
    [Ab_LocallyPropositional] (Instance/Ab.v),
    [RMod_LocallyPropositional] (Instance/Mod.v),
    [CMon_LocallyPropositional] (Instance/CMon.v) and
    [DeloopRig_LocallyPropositional] (Theory/Algebra/Rig.v).
    Those are the ambients the nine module and bimodule objects
    built on [hom_ab] actually use, so none of them gained a
    hypothesis.

    WHAT IS NOT DELIVERED.  No characterization of additive functors
    as the biproduct-preserving ones (Mac Lane Proposition VIII.2.4,
    which is strictly more than the definition and belongs to its own
    catalog item).  No additive-adjunction CLASS bundling F ⊣ U with
    both additivity witnesses, and hence no category of such.  No
    naturality statement for [adj_hom_ab_iso] in x or y as a functor
    into Ab, so it is a family of group isomorphisms and not an
    isomorphism of Ab-valued bifunctors.  (Since #454 the one-variable
    Ab-valued hom functors themselves exist, as
    Functor/Representable/Additive.v's [HomAb] and [CoHomAb]; the
    sentence before this one still holds, [adj_hom_ab_iso] not being
    restated as a natural isomorphism between them.)  No monoidal or enriched
    reading, so nothing here says that an adjunction between
    Ab-categories is an Ab-ENRICHED adjunction in the sense of
    Construction/Enriched.v.  No concrete instantiation: no in-tree
    adjunction between two Ab-enriched categories is exhibited, so
    every result here is a conditional and the file adds no witness
    to docs/INHABITATION.md.

    TWO ENGINEERING FINDINGS, both about elaboration rather than
    mathematics, recorded so the next reader does not rediscover them.
    (a) A [CMonHom] written as a record literal whose [cmon_map] field
    is a transpose — [{| cmon_map := to adj ... |}] — is REJECTED: the
    expected type is reported as [SetoidMorphism ?M ?N] with the two
    setoid arguments still evars, so the hom-setoid literals the [adj]
    field carries are never matched against [hom_ab]'s.  Building the
    same term with [unshelve econstructor] and discharging the field
    by [exact] elaborates without complaint, and that is why
    [adj_to_ab], [adj_from_ab] and [adj_hom_ab_iso] are in proof mode
    rather than written as terms.  (b) [Preadditive_op] and
    [AbEnriched_op] must be [Program Definition]s: as plain
    [Definition]s the [padd] field is rejected with the two hom-sets
    reported at swapped endpoints, even though the term is the right
    one — [padd_op_is_padd] closes by [eq_refl], so no transport was
    inserted and no obligation was generated (the file has none). *)

(**
** Injectivity of the two transposes

    A transpose is one leg of an isomorphism of setoids, so it is
    injective; the two round-trip corollaries of Theory/Adjunction.v
    are all that is needed.  Stated here rather than upstream because
    the copy a name search finds, [Instance/Rng/Free.v]'s
    [to_adj_injective], sits in a file this one does not require —
    that search was by NAME, so it is not evidence that no other
    spelling of the same fact exists.  The names are kept apart
    deliberately: the [print-assumptions] gate audits in one scope,
    where two constants called [to_adj_injective] could not be told
    apart. 

--------
** 两个转置的内射性

 转置是 setoids 同构的一条腿，所以它是
 单射； Theory/Adjunction.v 的两个往返推论
 这就是所需要的一切。 此处说明而不是上游，因为
 名称搜索找到的副本 [Instance/Rng/Free.v] 的
 [to_adj_injective]，位于该文件不需要的文件中 —
 该搜索是通过 NAME 进行的，因此这并不能证明没有其他人
 存在相同事实的拼写。 名字是分开的
 故意：[print-assumptions] 门在一个范围内进行审核，
 其中两个名为 [to_adj_injective] 的常量无法被告知
 分开。 
*)

Section AdjunctionInjectivity.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Lemma adj_to_inj {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj f ≈ to adj g → f ≈ g.
Proof.
  intro H.
  rewrite <- (to_adj_comp_law f), <- (to_adj_comp_law g).
  now apply from_adj_respects.
Qed.

Lemma adj_from_inj {x : D} {y : C} (f g : x ~{D}~> U y) :
  from adj f ≈ from adj g → f ≈ g.
Proof.
  intro H.
  rewrite <- (from_adj_comp_law f), <- (from_adj_comp_law g).
  now apply to_adj_respects.
Qed.

End AdjunctionInjectivity.

(**
** The transposes are group homomorphisms

    Mac Lane's Theorem 3 asserts two things at once, and this section
    isolates the half that needs only ONE of the two functors to be
    additive.  The forward transpose ⌊−⌋ is additive as soon as U is;
    the inverse transpose ⌈−⌉ is additive as soon as F is.  Theorem 3
    proper, in the next section, is what closes the loop by deriving
    the second hypothesis from the first. 

--------
** 转置是群同态

 Mac Lane 定理 3 同时断言了两件事，本节
 隔离仅需要两个函子之一的一半
 添加剂。 只要 U 是，前向转置 ⌊−⌋ 就是可加的；
 只要 F 是，反转置 ⌈−⌉ 就是可加的。 定理3
 正确的，在下一节中，是通过推导来关闭循环的
 第一个假设的第二个假设。 
*)

Section AdditiveTranspose.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(**
*** The forward transpose, given an additive right adjoint

    ⌊f⌋ ≈ fmap[U] f ∘ η ([to_adj_unit]), so additivity of ⌊−⌋ is
    additivity of fmap[U] followed by bilinearity of composition in
    its left argument. 

--------
*** 正向转置，给定加性右伴随

 ⌊f⌋ ≈ fmap[U] f ∘ η ([to_adj_unit])，所以 ⌊−⌋ 的可加性为
 fmap[U] 的可加性随后是组合的双线性
 它的左参数。 
*)

Section ForwardTranspose.

Context `{AU : @AdditiveFunctor C D AC AD U}.

Theorem to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) ≈ padd (to adj f) (to adj g).
Proof.
  rewrite !to_adj_unit.
  rewrite (@fmap_padd C D AC AD U AU _ _ f g).
  apply compose_padd_right.
Qed.

Theorem to_adj_pzero {x : D} {y : C} :
  to adj (@pzero C _ (F x) y) ≈ pzero.
Proof.
  rewrite to_adj_unit.
  rewrite (@fmap_pzero C D AC AD U AU (F x) y).
  apply compose_pzero_left.
Qed.

Theorem to_adj_abneg {x : D} {y : C} (f : F x ~{C}~> y) :
  to adj (abneg f) ≈ abneg (to adj f).
Proof.
  rewrite !to_adj_unit.
  rewrite (@fmap_abneg C D AC AD U AU _ _ f).
  apply compose_abneg_right.
Qed.

End ForwardTranspose.

(**
*** The inverse transpose, given an additive left adjoint

    ⌈f⌉ ≈ ε ∘ fmap[F] f ([from_adj_counit]); the mirror of the above,
    with bilinearity used in the right argument instead. 

--------
*** 逆转置，给定加法左伴随

 ⌈f⌉ ≈ ε ∘ fmap[F] f ([from_adj_counit]); 上面的镜子，
 相反，在正确的参数中使用双线性。 
*)

Section BackwardTranspose.

Context `{AF : @AdditiveFunctor D C AD AC F}.

Theorem from_adj_padd {x : D} {y : C} (f g : x ~{D}~> U y) :
  from adj (padd f g) ≈ padd (from adj f) (from adj g).
Proof.
  rewrite !from_adj_counit.
  rewrite (@fmap_padd D C AD AC F AF _ _ f g).
  apply compose_padd_left.
Qed.

Theorem from_adj_pzero {x : D} {y : C} :
  from adj (@pzero D _ x (U y)) ≈ pzero.
Proof.
  rewrite from_adj_counit.
  rewrite (@fmap_pzero D C AD AC F AF x (U y)).
  apply compose_pzero_right.
Qed.

Theorem from_adj_abneg {x : D} {y : C} (f : x ~{D}~> U y) :
  from adj (abneg f) ≈ abneg (from adj f).
Proof.
  rewrite !from_adj_counit.
  rewrite (@fmap_abneg D C AD AC F AF _ _ f).
  apply compose_abneg_left.
Qed.

End BackwardTranspose.

End AdditiveTranspose.

(**
** Mac Lane §IV.1 Theorem 3: a left adjoint of an additive
       functor is additive

    Both fmap[F] (padd f g) and padd (fmap[F] f) (fmap[F] g)
    transpose to padd (η ∘ f) (η ∘ g).  For the first this is
    [fmap_from_adj_unit] (fmap[F] h ≈ ⌈η ∘ h⌉, so its transpose is
    η ∘ h by [from_adj_comp_law]) together with bilinearity of
    composition; for the second it is [to_adj_padd] followed by the
    same reading applied to each summand.  Injectivity of ⌊−⌋ closes
    it.  Note which hypothesis does the work: U's additivity is used
    exactly once, inside [to_adj_padd]. 

--------
** Mac Lane §IV.1 定理 3：加法的左伴随
 函子是可加的

 fmap[F] (padd f g) 和 padd (fmap[F] f) (fmap[F] g)
 转置为 padd (\eta ∘ f) (\eta ∘ g)。 首先这是
 [fmap_from_adj_unit] (fmap[F] h ≈ ⌈η ∘ h⌉，因此其转置为
 η ∘ h by [from_adj_comp_law]) 以及双线性
 组成； 第二个是 [to_adj_padd]，然后是
 每个被加数应用相同的读数。 ⌊−⌋ 的内射性闭合
 它。 注意哪个假设起作用：使用 U 的可加性
 恰好一次，在 [to_adj_padd] 内。 
*)

Section LeftAdjointAdditive.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.
Context `{AU : @AdditiveFunctor C D AC AD U}.

(*
The transpose of fmap[F] h is η ∘ h.  Half of [fmap_from_adj_unit]
   read forwards, isolated because it is used three times below. 

--------
fmap[F] h 的转置为 η ∘ h。 [fmap_from_adj_unit] 的一半
 向前读，隔离，因为它在下面使用了 3 次。 
*)
Lemma to_adj_fmap_left {x y : D} (h : x ~{D}~> y) :
  to adj (fmap[F] h) ≈ unit ∘ h.
Proof.
  rewrite (fmap_from_adj_unit h).
  apply from_adj_comp_law.
Qed.

Theorem left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g).
Proof.
  apply adj_to_inj.
  rewrite to_adj_fmap_left.
  rewrite to_adj_padd.
  rewrite !to_adj_fmap_left.
  apply compose_padd_left.
Qed.

(*
Mac Lane's Theorem 3, as an inhabitant of the class rather than as
   an equation: it may be handed to [Compose_AdditiveFunctor], to
   [fmap_pzero]/[fmap_abneg], or to the backward-transpose section
   above. 

--------
麦克莱恩定理 3，作为类的居民而不是作为
 一个方程：可以将其交给 [Compose_AdditiveFunctor]，以
 [fmap_pzero]/[fmap_abneg]，或向后转置部分
 上面。 
*)
#[export] Instance left_adjoint_additive :
  @AdditiveFunctor D C AD AC F := {|
  fmap_padd := @left_adjoint_fmap_padd
|}.

(*
There is nothing to read back here, and an earlier revision of this
   file shipped an [Example] pretending otherwise.  [AdditiveFunctor]
   is a structure ON a given functor rather than a bundled functor, so
   "the produced witness leaves F unperturbed" has no content to state.
   The [Example] asserting [@fmap D C F x y f = fmap[F] f] was a
   SYNTACTIC TAUTOLOGY — [fmap[F]] IS notation for [@fmap _ _ F _ _]
   (Theory/Functor.v) — so it never mentioned
   [left_adjoint_additive] and compiled at an arbitrary functor with no
   adjunction in sight.  Removed rather than repaired. 

--------
这里没有什么可读的，还有一个早期的修订版
 文件发送了一个 [Example] 假装不是这样。 保护1X
 是给定函子上的结构而不是捆绑函子，所以
 “出示的证人让 F 保持平静”没有可说明的内容。 
[Example] 断言 [@fmap D C F x y f = fmap[F] f] 是
 句法重述 — [fmap[F]] 是 [@fmap _ _ F _ _] 的表示法
 (Theory/Functor.v) — 所以它从未提及
 [left_adjoint_additive] 并在任意函子上编译，没有
 附属在眼前。 拆除而不是修复。 
*)

(*
With Theorem 3 in force, the inverse transpose is additive too —
   so BOTH legs of the adjunction bijection are group homomorphisms
   under the single hypothesis that U is additive.  This is what
   makes the hom-group isomorphism below available at the strength
   Mac Lane states it. 

--------
在定理 3 生效的情况下，转置也是可加的 —
 所以附加双射的两条腿都是群同态
 在 U 是可加性的单一假设下。 这就是
 使得下面的 hom 群同构在强度下可用
 麦克莱恩这样说。 
*)
Corollary adj_from_padd {x : D} {y : C} (f g : x ~{D}~> U y) :
  from adj (padd f g) ≈ padd (from adj f) (from adj g).
Proof. exact (from_adj_padd f g). Qed.

Corollary adj_from_pzero {x : D} {y : C} :
  from adj (@pzero D _ x (U y)) ≈ pzero.
Proof. exact from_adj_pzero. Qed.

Corollary adj_from_abneg {x : D} {y : C} (f : x ~{D}~> U y) :
  from adj (abneg f) ≈ abneg (from adj f).
Proof. exact (from_adj_abneg f). Qed.

End LeftAdjointAdditive.

(**
** The hom-sets as abelian groups, and the bijection as a group
       isomorphism

    Mac Lane's conclusion has two halves and the reviewer bar for
    this file is that both be visible.  The first is the additivity
    of F, above.  The second is that the bijection

        F x ~{C}~> y   ≅   x ~{D}~> U y

    respects the group structure, and the honest way to say that in
    this library is to exhibit it as an isomorphism in [Ab], the
    tree's own category of abelian groups — which is possible
    precisely because an [AbObject] is a setoid with a commutative
    monoid structure and a negation, and an [AbEnriched] category
    supplies exactly that on each hom-setoid.

    AN EARLIER REVISION stopped that sentence there.  Since the PR
    "algebraic carriers are sets" (2026-09-17) an [AbObject] carries
    one further field, [cmon_prop], and an [AbEnriched] category does
    NOT supply it: it is a property of the ambient hom-setoids, not of
    the enrichment.  Both categories of this section are therefore
    assumed [LocallyPropositional] ([LPC], [LPD] below), and the ten
    constants that gained the hypothesis are named in the
    strength-change paragraph of the file header.

    UNIVERSES.  An [AbObject]'s carrier is a [SetoidObject], which
    identifies a setoid's carrier and relation universes; so this
    section is stated over C : Category@{u u0 u0}.  The identification
    is not introduced here — Theory/Adjunction.v's [adj] field builds
    [SetoidObject] literals out of the very same hom-setoids — but it
    is a genuine restriction relative to the previous sections, which
    carry none, and it is the reason the additivity lemmas are
    delivered as free-standing theorems as well as through this
    packaging. 

--------
** hom 集作为阿贝尔群，双射作为群
 同构

Mac Lane 的结论分为两部分，审稿人栏为
 这个文件是两者都是可见的。 第一个是可加性
 F，上面。 第二个是双射

F x ~{C}~> y ≅ x ~{D}~> U y

尊重团体结构，并诚实地说
 该库将在 [Ab] 中将其展示为同构，即
 树自己的阿贝尔群类别——这是可能的
 正是因为 [AbObject] 是具有交换律的集合体
 幺半群结构和否定，以及 [AbEnriched] 类别
 为每个 hom-setoid 提供准确的信息。

早期的修订将这句话停在那里。 自从公关
 “代数载体是集合”（2026-09-17）[AbObject] 携带
 另一个字段 [cmon_prop] 和 [AbEnriched] 类别确实
 不提供它：它是环境 hom-setoids 的属性，而不是
 的充实。 因此，本节的两个类别都是
 假定为 [LocallyPropositional]（下面为 [LPC]、[LPD]），并且十个
 获得假设的常数被命名为
 文件头的强度更改段落。

宇宙。 [AbObject] 的载体是 [SetoidObject]，
 识别集合体的载体和关系宇宙； 所以这个
 部分在 C : Category@{u u0 u0} 上陈述。 鉴定
 这里就不介绍了——Theory/Adjunction.v的[adj]字段构建
 [SetoidObject] 文字来自完全相同的 hom-setoids — 但它
 相对于前面的部分来说是一个真正的限制，其中
 不携带任何内容，这就是可加性引理的原因
 作为独立定理以及通过此传递
 包装。 
*)

Section HomGroups.

(*
[hom_ab] is a plain [Definition] rather than an [Instance]: it is a
   reading of a hom-setoid, not something typeclass resolution should
   ever be searching for.

   [LP] is new since the PR "algebraic carriers are sets" (2026-09-17).  An
   [AbObject] carries [cmon_prop], the property that its carrier's `≈` is
   logically equivalent to a [Prop]-valued relation, and here the carrier IS
   [C]'s hom-setoid; an arbitrary category supplies no such relation
   (Instance/Sets/Propositional.v's header records the measurement for [Cat],
   where an `≈` of functors IS a family of isomorphisms).  So the ambient
   category must be LOCALLY PROPOSITIONAL.  The hypothesis is a class, so it
   is discharged by resolution wherever an instance is in scope: at [Ab] and
   [RMod R] by [Ab_LocallyPropositional] and [RMod_LocallyPropositional], and
   those are the ambients the nine module and bimodule objects built on
   [hom_ab] actually use. 

--------
[hom_ab] 是一个普通的 [Definition]，而不是 [Instance]：它是一个
 读取 hom-setoid，而不是类型类解析应该的内容
 一直在寻找。

[LP] 是自 PR“代数载体是集合”（2026-09-17）以来的新产品。 安
 [AbObject]携带[cmon_prop]，其载体``≈`的性质为
 逻辑上等价于 [Prop] 值关系，这里载体是
 [C] 的 hom-setoid； 任意类别不提供这种关系
 （Instance/Sets/Propositional.v 的标头记录了 [Cat] 的测量值，
 其中函子的“≈”是同构族）。 所以环境
 类别必须是局部建议的。 假设是一个类，所以它
 只要实例在范围内，就会通过解析释放：在 [Ab] 和
 [RMod R]、[Ab_LocallyPropositional] 和 [RMod_LocallyPropositional]，以及
 这些是构建九个模块和双模块对象的环境
 [hom_ab]实际使用。 
*)
Definition hom_ab {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  AbObject := {|
  ab_cmon :=
    {| cmon_setoid :=
         {| carrier := @hom C x y; is_setoid := @homset C x y |};
       cmon_zero := @pzero C _ x y;
       cmon_plus := @padd C _ x y;
       cmon_plus_respects := @padd_respects C _ x y;
       cmon_plus_assoc := @padd_assoc C _ x y;
       cmon_plus_comm := @padd_comm C _ x y;
       cmon_plus_zero_l := @padd_zero_left C _ x y;
       cmon_prop := locally_prop x y |};
  ab_neg := @abneg C AC x y;
  ab_neg_respects := @abneg_respects C AC x y;
  (*
[padd_abneg] is stated as f + (−f) ≈ 0 while [ab_neg_left] wants
     (−f) + f ≈ 0; commutativity of the enrichment reconciles them. 

--------
[padd_abneg] 表示为 f + (−f) ≈ 0 而 [ab_neg_left] 想要
 (−f) + f ≈ 0； 丰富化的交换性使它们协调一致。 
*)
  ab_neg_left := fun f =>
    Equivalence_Transitive _ _ _
      (@padd_comm C _ x y (@abneg C AC x y f) f)
      (@padd_abneg C AC x y f)
|}.

(*
The four data fields are the enrichment's own, on the nose: nothing
   is rebuilt, so every [AbEnriched] law about [padd] is literally a
   law about this group.  Measured at [eq_refl], not assumed. 

--------
四个数据字段是浓缩本身的，表面上看：什么都没有
 被重建，所以关于 [padd] 的每个 [AbEnriched] 定律实际上都是一个
 关于这个群体的法律。 在 [eq_refl] 上测量，未假设。 
*)
Example hom_ab_carrier {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  carrier (cmon_setoid (hom_ab AC x y)) = (x ~{C}~> y).
Proof. exact eq_refl. Qed.

Example hom_ab_plus {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  cmon_plus (hom_ab AC x y) = @padd C _ x y.
Proof. exact eq_refl. Qed.

Example hom_ab_zero {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  cmon_zero (hom_ab AC x y) = @pzero C _ x y.
Proof. exact eq_refl. Qed.

Example hom_ab_neg {C : Category} {LP : LocallyPropositional C}
  (AC : AbEnriched C) (x y : C) :
  ab_neg (hom_ab AC x y) = @abneg C AC x y.
Proof. exact eq_refl. Qed.

Context {C D : Category}.
(* Both ambients must be locally propositional; see [hom_ab] above.  / 两种环境都必须是局部命题的； 请参阅上面的 [hom_ab]。*)
Context {LPC : LocallyPropositional C}.
Context {LPD : LocallyPropositional D}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.
Context `{AU : @AdditiveFunctor C D AC AD U}.

(*
The forward transpose as a homomorphism of abelian groups.  Its
   underlying setoid map is the transpose itself; the two
   homomorphism laws are [to_adj_pzero] and [to_adj_padd]. 

--------
前向转置作为阿贝尔群的同态。 其
 底层 setoid 映射是转置本身； 两个
 同态定律是 [to_adj_pzero] 和 [to_adj_padd]。 
*)
Definition adj_to_ab (x : D) (y : C) :
  AbHom (hom_ab AC (F x) y) (hom_ab AD x (U y)).
Proof.
  unshelve econstructor.
  - exact (to (@adj C D F U A x y)).
  - exact (@to_adj_pzero C D AC AD F U A AU x y).
  - exact (@to_adj_padd C D AC AD F U A AU x y).
Defined.

(*
And the inverse transpose, which is additive by Theorem 3 —
   no second hypothesis on F is taken. 

--------
以及逆转置，根据定理 3 进行相加 —
 不对 F 采取第二个假设。 
*)
Definition adj_from_ab (x : D) (y : C) :
  AbHom (hom_ab AD x (U y)) (hom_ab AC (F x) y).
Proof.
  unshelve econstructor.
  - exact (from (@adj C D F U A x y)).
  - exact (@adj_from_pzero C D AC AD F U A AU x y).
  - exact (@adj_from_padd C D AC AD F U A AU x y).
Defined.

(*
Mac Lane's second clause: the adjunction bijection is an
   isomorphism of abelian groups.  Both round trips are the existing
   [to_adj_comp_law]/[from_adj_comp_law], since [Ab]'s hom-setoid is
   pointwise equality of the underlying maps.

   AN EARLIER REVISION stated this for any two Ab-enriched categories.
   It now rests on [LPC] and [LPD] above, because both of its ends are
   [hom_ab]s and an [AbObject] carries [cmon_prop] — see [hom_ab] and
   the strength-change paragraph of the file header.  The two
   [Example]s below it ([adj_hom_ab_iso_to], [adj_hom_ab_iso_from])
   inherit the same two hypotheses, and their [eq_refl] strength is
   unchanged. 

--------
Mac Lane 的第二个子句：附加双射是
 阿贝尔群的同构。 两个往返都是现有的
 [to_adj_comp_law]/[from_adj_comp_law]，因为 [Ab] 的 hom-setoid 是
 底层映射的逐点相等。 

早期的修订针对任何两个富含抗体的类别都说明了这一点。 
它现在依赖于上面的 [LPC] 和 [LPD]，因为它的两端都是
 [hom_ab] 和 [AbObject] 搭载 [cmon_prop] — 请参阅 [hom_ab] 和
 文件头的强度变化段落。 两人
 其下方的 [Example]（[adj_hom_ab_iso_to]、[adj_hom_ab_iso_from]）
 继承了相同的两个假设，他们的 [eq_refl] 强度是
 不变。 
*)
Definition adj_hom_ab_iso (x : D) (y : C) :
  @Isomorphism Ab (hom_ab AC (F x) y) (hom_ab AD x (U y)).
Proof.
  unshelve econstructor.
  - exact (adj_to_ab x y).
  - exact (adj_from_ab x y).
  - intro f; apply from_adj_comp_law.
  - intro f; apply to_adj_comp_law.
Defined.

(*
The two legs are the transposes on the nose, not merely equivalent
   to them: the group isomorphism is the set isomorphism with its
   structure exhibited, and nothing was rebuilt. 

--------
两条腿是鼻子上的转置，而不仅仅是等价
 对他们来说：群同构是集合同构及其
 结构展示出来，没有重建任何东西。 
*)
Example adj_hom_ab_iso_to (x : D) (y : C) (f : F x ~{C}~> y) :
  cmon_map (to (adj_hom_ab_iso x y)) f = to (@adj C D F U A x y) f.
Proof. exact eq_refl. Qed.

Example adj_hom_ab_iso_from (x : D) (y : C) (f : x ~{D}~> U y) :
  cmon_map (from (adj_hom_ab_iso x y)) f = from (@adj C D F U A x y) f.
Proof. exact eq_refl. Qed.

End HomGroups.

(**
** The dual: a right adjoint of an additive functor is additive

    Obtained by transport across opposites rather than by a second
    argument.  The transport needed two constructions the tree did
    not carry: [Preadditive_op] and [AbEnriched_op].  Every field is
    the corresponding field of the original — composition in C^op is
    C's with its arguments exchanged, so the two bilinearity laws
    trade places and so do the two absorption laws, while the
    commutative-monoid laws are unchanged, [hom] in C^op being [hom]
    in C at swapped endpoints. 

--------
** 对偶：加法函子的右伴随是可加的

 通过穿越相反的运输而不是通过第二次获得
 论点。 运输需要树所做的两次构造
 不携带：[Preadditive_op] 和 [AbEnriched_op]。 每个字段都是
 C^op 中原始 — 组合的相应字段为
 C 的参数交换，因此两个双线性定律
 贸易场所，两个吸收定律也是如此，而
 交换幺半群定律不变，C^op 中的 [hom] 为 [hom]
 在 C 中交换端点处。 
*)

Program Definition Preadditive_op {C : Category} (P : @Preadditive C) :
  @Preadditive (C^op) := {|
  padd := fun x y => @padd C P y x;
  pzero := fun x y => @pzero C P y x;
  padd_respects := fun x y => @padd_respects C P y x;
  padd_assoc := fun x y => @padd_assoc C P y x;
  padd_comm := fun x y => @padd_comm C P y x;
  padd_zero_left := fun x y => @padd_zero_left C P y x;
  compose_padd_left := fun x y z h f g =>
    @compose_padd_right C P z y x f g h;
  compose_padd_right := fun x y z f g h =>
    @compose_padd_left C P z y x h f g;
  compose_pzero_left := fun x y z f => @compose_pzero_right C P z y x f;
  compose_pzero_right := fun x y z f => @compose_pzero_left C P z y x f
|}.

Program Definition AbEnriched_op {C : Category} (AC : AbEnriched C) :
  AbEnriched (C^op) := {|
  abenriched_preadditive := Preadditive_op (@abenriched_preadditive C AC);
  abneg := fun x y => @abneg C AC y x;
  abneg_respects := fun x y => @abneg_respects C AC y x;
  padd_abneg := fun x y => @padd_abneg C AC y x
|}.

(*
The opposite enrichment is the original one read at swapped
   endpoints, definitionally — which is what makes the transport of
   additivity below proof-free. 

--------
相反的丰富内容是在交换时阅读的原始内容
 从定义上讲，端点——这就是传输的原因
 以下可加性无需证明。 
*)
Example padd_op_is_padd {C : Category} (P : @Preadditive C) (x y : C) :
  @padd (C^op) (Preadditive_op P) x y = @padd C P y x.
Proof. exact eq_refl. Qed.

Example abneg_op_is_abneg {C : Category} (AC : AbEnriched C) (x y : C) :
  @abneg (C^op) (AbEnriched_op AC) x y = @abneg C AC y x.
Proof. exact eq_refl. Qed.

(*
Additivity crosses [Opposite_Functor] in both directions with no
   proof content: the opposite functor's [fmap] IS the original's at
   swapped endpoints, and [padd] in the opposite enrichment IS [padd]
   at swapped endpoints, so the two [fmap_padd] statements are the
   same statement. 

--------
可加性在两个方向上穿过 [Opposite_Functor]，没有
 证明内容：相反函子的 [fmap] 是原始函子的 at
 交换端点，相反浓缩中的 [padd] 是 [padd]
 在交换的端点处，因此两个 [fmap_padd] 语句是
 同样的声明。 
*)
Definition AdditiveFunctor_op {C D : Category}
  {AC : AbEnriched C} {AD : AbEnriched D} (G : C ⟶ D)
  (AG : @AdditiveFunctor C D AC AD G) :
  @AdditiveFunctor (C^op) (D^op) (AbEnriched_op AC) (AbEnriched_op AD)
    (Opposite_Functor G).
Proof.
  constructor.
  intros x y f g.
  exact (@fmap_padd C D AC AD G AG _ _ f g).
Defined.

Definition AdditiveFunctor_unop {C D : Category}
  {AC : AbEnriched C} {AD : AbEnriched D} (G : C ⟶ D)
  (AG : @AdditiveFunctor (C^op) (D^op) (AbEnriched_op AC)
          (AbEnriched_op AD) (Opposite_Functor G)) :
  @AdditiveFunctor C D AC AD G.
Proof.
  constructor.
  intros x y f g.
  exact (@fmap_padd (C^op) (D^op) (AbEnriched_op AC) (AbEnriched_op AD)
           (Opposite_Functor G) AG _ _ f g).
Defined.

Section RightAdjointAdditive.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (AF : @AdditiveFunctor D C AD AC F).

(*
[Opposite_Adjunction A : U^op ⊣ F^op], so in the opposite pair the
   LEFT adjoint is U^op and the right adjoint is F^op.  Theorem 3
   applied there yields additivity of U^op, which [AdditiveFunctor_unop]
   carries back to U. 

--------
[Opposite_Adjunction A : U^op ⊣ F^op]，所以在相反的一对中
 左伴随是 U^op，右伴随是 F^op。 定理3
 在那里应用产生 U^op 的可加性，[AdditiveFunctor_unop]
 带回 U。 
*)
Definition right_adjoint_additive : @AdditiveFunctor C D AC AD U :=
  AdditiveFunctor_unop U
    (@left_adjoint_additive (D^op) (C^op) (AbEnriched_op AD)
       (AbEnriched_op AC) (Opposite_Functor U) (Opposite_Functor F)
       (Opposite_Adjunction F U A) (AdditiveFunctor_op F AF)).

End RightAdjointAdditive.

(**
** Riehl §4.6 Corollary 4.6.9: additivity with NO additivity
       hypothesis

    Riehl, "Category Theory in Context", §4.6 Corollary 4.6.9: between
    categories in which finite direct sums are simultaneously finite
    products and finite coproducts, BOTH adjoints of an adjunction are
    additive, with no additivity assumed of either.  The reason is that
    a left adjoint preserves coproducts, and in such a category the
    coproduct carries the product structure too, so the enrichment —
    which is computed by the biproduct — is carried along with it.

    WHAT LANDS HERE, AND WHAT DOES NOT.  The reusable missing piece the
    catalog issue names is the bridge between [Biproduct] and the two
    one-sided universal properties.  It is delivered in the orientation
    an adjunction actually supplies: [biproduct_of_coproduct] promotes
    a COPRODUCT with a compatible pair of retractions to a full
    [Biproduct], the product half being derived from preadditivity by
    the identity decomposition — the exact dual of Semiadditive.v's
    [cartesian_bi_is_coproduct], which the tree carried only in the
    product orientation and only bundled with a chosen [Cartesian]
    structure.  On top of it the adjunction supplies everything else by
    hom-set arguments: [adj_image_is_coproduct] (a left adjoint carries
    a coproduct to a coproduct — transposition and [to_adj_nat_l], no
    colimit vocabulary and no shape category) and [adj_fmap_pzero] (a
    left adjoint kills zero morphisms, because F of the initial object
    has singleton hom-sets).  [adj_image_biproduct] then assembles the
    two into the statement that a left adjoint PRESERVES biproducts,
    with the F-images of all four structure maps as the image's
    structure maps.

    Read the dependency accurately: [adj_image_biproduct] is a
    free-standing result and the transfer theorem does NOT consume it.
    [fmap_padd_of_preserved_coproduct] — the reusable statement, over
    an ARBITRARY functor with no adjunction anywhere — takes the
    coproduct property and the zero-preservation directly and rebuilds
    the image biproduct inside its own proof, as a single local
    definition.  That is deliberate rather than incidental: a
    universe-polymorphic biproduct constant mentioned twice in one goal
    acquires two universe instances, which the final rewriting step
    then cannot identify, and a single [pose]d local term has one.
    [left_adjoint_fmap_padd_biproduct] supplies the two hypotheses from
    the adjunction, and [left_adjoint_additive_of_biproducts] packages
    the result as an [AdditiveFunctor] over Ab-enriched categories with
    NO additivity hypothesis on either functor.

    WHAT IS NOT DELIVERED, PRECISELY.  The biproducts of the SOURCE
    category are an explicit hypothesis ([HasBiproducts D]), not
    derived from a completeness or abelian assumption; nothing here
    says a semiadditive category has them, and no [Semiadditive] or
    [Abelian] class is consulted.  The dual clause of Riehl's
    corollary — a RIGHT adjoint is additive under the same hypotheses —
    is NOT stated: transporting it across opposites the way
    [right_adjoint_additive] does would need [ZeroObject (C^op)] and a
    [Biproduct] transport, neither of which exists in tree and neither
    of which is built here.  Nothing connects any of this to
    Adjunction/Continuity.v's [right_adjoint_preserves_limits] /
    [left_adjoint_preserves_colimits]: the coproduct preservation below
    is proved directly from the hom-set bijection and is not exhibited
    as an instance of those theorems, so no bridge between the
    elementary and the [Colimit]-shaped readings is claimed.  Finally,
    no separation is proved: it is not shown that the hypotheses here
    are weaker than assuming U additive, only that they are different. 

--------
** Riehl §4.6 推论 4.6.9：与 NO 加和性
 假设

Riehl，“语境中的范畴论”，§4.6 推论 4.6.9：之间
 有限直和同时也是有限的类别
 产品和有限副产品，附加的两个伴随物是
 加法，假设两者都没有加和性。 原因是
 左伴随保留余积，并且在这样的类别中
 副产品也带有产品结构，因此丰富 -
 由二积计算得出的 — 随之而来。

什么会降落在这里，什么不会。 可重复使用的缺失部分
 目录问题名称是 [Biproduct] 和两者之间的桥梁
 片面的普遍属性。 它是按方向交付的
 附件实际上提供：[biproduct_of_coproduct] 提升
 具有一对兼容的回缩的 COPRODUCT
 [Biproduct]，乘积的一半源自预加性
 恒等分解 — Semiadditive.v 的精确对偶
 [cartesian_bi_is_coproduct]，该树仅在
 产品定位，仅与选定的 [Cartesian] 捆绑在一起
 结构。 除此之外，该附件还提供了其他一切
 hom-set 参数：[adj_image_is_coproduct]（左伴随携带
 余积到余积 — 转置和 [to_adj_nat_l]，否
 colimit 词汇和无形状类别）和 [adj_fmap_pzero]（a
 左伴随杀死零态射，因为初始对象的 F
 有单例 hom-sets）。 [adj_image_biproduct] 然后组装
 两个到左伴随保留二积的语句中，
 将所有四个结构图的 F 图像作为图像
 结构图。

准确读取依赖关系：[adj_image_biproduct] 是一个
 独立的结果，转移定理不会消耗它。 
[fmap_padd_of_preserved_coproduct] — 可重用语句，结束
 任何地方都没有附加的任意函子 - 取
 直接联积属性和零保存并重建
 其自身证明内的图像二积，作为单个本地
 定义。 这是故意的而不是偶然的：
 宇宙多态二积常数在一个目标中被提及两次
 获取两个 Universe 实例，这是最后的重写步骤
 然后无法识别，单个 [pose]d 本地术语有一个。 
[left_adjoint_fmap_padd_biproduct] 提供了两个假设
 附件和 [left_adjoint_additive_of_biproducts] 包
 结果为 [AdditiveFunctor] 与 Ab 富集类别的比较
 任何一个函子都没有可加性假设。

确切地说，什么是未交付的。 SOURCE 的副产品
 类别是一个明确的假设（[HasBiproducts D]），而不是
 从完整性或阿贝尔假设导出； 这里什么都没有
 说半加性类别有它们，但没有 [Semiadditive] 或
 参考[Abelian] 等级。 Riehl 的双重条款
 推论 — 在相同的假设下，右伴随词是可加的 —
 没有说明：将其运过对面的路
 [right_adjoint_additive] 确实需要 [ZeroObject (C^op)] 和一个
 [Biproduct] 传输，两者都不存在于树中，也不存在
 其中之一是在这里建造的。 这一切都与
 Adjunction/Continuity.v 的 [right_adjoint_preserves_limits] /
 [left_adjoint_preserves_colimits]：下面的联积保存
 直接从 hom-set 双射证明且未展示
 作为这些定理的一个例子，所以之间没有桥梁
 基本的和 [Colimit] 形状的读数已被声明。 最后，
 没有证明分离：没有表明这里的假设
 比假设 U 加性弱，只是它们不同。 
*)

Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.

(**
*** The biproduct bridge, coproduct orientation

    Dual to Semiadditive.v's [cartesian_bi_is_coproduct]: there a
    product plus preadditivity yields the coproduct half; here a
    coproduct plus preadditivity yields the product half.  The pivot is
    the same in both, the decomposition of the identity as the sum of
    the two "project then reinject" idempotents — which on this side is
    proved by the coproduct's own uniqueness clause. 

--------
*** 双积桥、联积导向

 Dual to Semiadditive.v 的 [cartesian_bi_is_coproduct]：有一个
 乘积加上预加和得到联积的一半； 这里有一个
 副积加上预加性得到乘积的一半。 枢轴是
 两者相同，将身份分解为总和
 两个“项目然后重新注入”幂等 - 在这一侧是
 由余积自身的唯一性子句证明。 
*)

Section CoproductBiproduct.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.

Section Bridge.

Context {x y b : C}.
Context (i1 : x ~> b) (i2 : y ~> b) (p1 : b ~> x) (p2 : b ~> y).
Context (H11 : p1 ∘ i1 ≈ id) (H22 : p2 ∘ i2 ≈ id).
Context (H12 : p1 ∘ i2 ≈ zero_mor) (H21 : p2 ∘ i1 ≈ zero_mor).
Context (Hco : ∀ (z : C) (f : x ~> z) (g : y ~> z),
                 ∃! h : b ~> z, (h ∘ i1 ≈ f) ∧ (h ∘ i2 ≈ g)).

(* Two morphisms out of b that agree on both injections agree.  / b 中与两次注入一致的两个态射一致。*)
Lemma additive_coprod_ext {z : C} (u v : b ~> z) :
  u ∘ i1 ≈ v ∘ i1 → u ∘ i2 ≈ v ∘ i2 → u ≈ v.
Proof.
  intros Hl Hr.
  transitivity (unique_obj (Hco z (u ∘ i1) (u ∘ i2))).
  - symmetry.
    apply (uniqueness (Hco z (u ∘ i1) (u ∘ i2)) u).
    split; reflexivity.
  - apply (uniqueness (Hco z (u ∘ i1) (u ∘ i2)) v).
    split; [ now symmetry | now symmetry ].
Qed.

(*
The identity decomposition.  Both sides restrict to i1 along i1 and
   to i2 along i2, so [additive_coprod_ext] identifies them. 

--------
身份分解。 双方都沿着 i1 限制到 i1 并且
 沿着 i2 到 i2，因此 [additive_coprod_ext] 识别它们。 
*)
Lemma coprod_id_decomp : padd (i1 ∘ p1) (i2 ∘ p2) ≈ id.
Proof.
  apply additive_coprod_ext.
  - rewrite compose_padd_right.
    rewrite <- !comp_assoc.
    rewrite H11, H21.
    rewrite id_right, zero_mor_left.
    rewrite <- pzero_zero_mor.
    now rewrite padd_zero_right, id_left.
  - rewrite compose_padd_right.
    rewrite <- !comp_assoc.
    rewrite H12, H22.
    rewrite id_right, zero_mor_left.
    rewrite <- pzero_zero_mor.
    now rewrite padd_zero_left, id_left.
Qed.

(*
The product half: the mediator into b is the sum of the reinjected
   legs, and uniqueness is [coprod_id_decomp] applied to a competitor. 

--------
乘积一半：b 中的中介是重新注入的总和
 腿，独特之处在于 XPTECT0X 应用于竞争对手。 
*)
Definition coprod_is_product (z : C) (f : z ~> x) (g : z ~> y) :
  ∃! h : z ~> b, (p1 ∘ h ≈ f) ∧ (p2 ∘ h ≈ g).
Proof.
  unshelve refine {| unique_obj := padd (i1 ∘ f) (i2 ∘ g) |}.
  - split.
    + rewrite compose_padd_left.
      rewrite !comp_assoc.
      rewrite H11, H12.
      rewrite id_left, zero_mor_right.
      rewrite <- pzero_zero_mor.
      apply padd_zero_right.
    + rewrite compose_padd_left.
      rewrite !comp_assoc.
      rewrite H21, H22.
      rewrite id_left, zero_mor_right.
      rewrite <- pzero_zero_mor.
      apply padd_zero_left.
  - intros v [Hl Hr].
    symmetry.
    transitivity (padd (i1 ∘ p1) (i2 ∘ p2) ∘ v).
    + now rewrite coprod_id_decomp, id_left.
    + rewrite compose_padd_right.
      rewrite <- !comp_assoc.
      now rewrite Hl, Hr.
Defined.

Definition biproduct_of_coproduct : Biproduct x y := {|
  biproduct_obj := b;
  bi_inl := i1;
  bi_inr := i2;
  bi_exl := p1;
  bi_exr := p2;
  bi_exl_inl := H11;
  bi_exr_inr := H22;
  bi_exl_inr := H12;
  bi_exr_inl := H21;
  bi_is_product := coprod_is_product;
  bi_is_coproduct := Hco
|}.

(*
The bridge keeps the data it was given: the object and all four
   structure maps are the supplied ones on the nose, so a consumer may
   read them back without a comparison morphism. 

--------
桥保存所给的数据：对象和所有四个
 结构图是在鼻子上提供的，因此消费者可以
 在没有比较态射的情况下读回它们。 
*)
Example bridge_inl_strict : bi_inl biproduct_of_coproduct = i1.
Proof. exact eq_refl. Qed.

End Bridge.

(*
The enrichment addition read off a biproduct through the coproduct
   mediator alone: f + g ≈ [f, g] ∘ Δ.  This is [bi_copair_pair] at
   identity legs, and it is the form the transfer below needs, since
   the copairing is what a left adjoint preserves. 

--------
富集添加通过副产品读出副产品
 单独中介：f + g ≈ [f, g] ∘ Δ。 这是 [bi_copair_pair]，位于
 身份腿，它是下面的转移所需要的形式，因为
 共配对是左伴随所保留的。 
*)
Lemma padd_copair_diag {a c : C} (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B ≈ padd f g.
Proof.
  unfold bi_diag.
  rewrite bi_copair_pair.
  now rewrite !id_right.
Qed.

End CoproductBiproduct.

(**
*** A left adjoint carries biproducts to biproducts

    Three hom-set arguments and no colimit machinery: the image of a
    coproduct is a coproduct because the transpose turns
    precomposition with fmap[F] i into postcomposition with i
    ([to_adj_nat_l]); the image of the initial object has singleton
    hom-sets because the transpose lands in hom-sets out of the initial
    object; and the four interaction laws are functoriality plus that
    second fact. 

--------
*** 左伴随将二积带到二积

 三个 hom-set 参数且无余极限机制：a 的图像
 余积是余积，因为转置变成
 使用 fmap[F] i 进行预合成，使用 i 进行后合成
 （[to_adj_nat_l]）； 初始对象的图像具有单例
 hom-sets，因为转置落在初始的 hom-sets 中
 对象； 四个相互作用定律是函子性加上
 第二个事实。 
*)

Section LeftAdjointBiproducts.

Context {C D : Category}.
Context `{ZC : @ZeroObject C}.
Context `{ZD : @ZeroObject D}.
Context `{PC : @Preadditive C}.
Context `{PD : @Preadditive D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(*
Hom-sets out of the image of D's initial object are singletons: the
   transpose carries them isomorphically onto hom-sets out of the
   initial object itself, where [zero_unique] applies. 

--------
D 的初始对象的图像中的 Hom 集是单例：
 转置将它们同构到 hom-sets 上
 初始对象本身，其中 [zero_unique] 适用。 
*)
Lemma adj_image_initial_unique {z : C}
  (h k : F (@initial_obj D (@zero_initial D ZD)) ~{C}~> z) : h ≈ k.
Proof.
  apply adj_to_inj.
  apply (@zero_unique D (@zero_initial D ZD)).
Qed.

(*
Hence a left adjoint kills the enrichment zero.  The zero morphism
   factors through D's zero object, and its image therefore factors
   through F of the initial object, whose outgoing morphisms are all
   equal — in particular equal to [pzero], which absorbs. 

--------
因此，左伴随消除了富集零。 零态射
 通过 D 的零对象进行因式分解，因此它的图像因式分解
 到初始对象的 F，其传出态射都是
 等于 — 特别是等于 [pzero]，它吸收。 
*)
Lemma adj_fmap_pzero {a c : D} :
  fmap[F] (@pzero D PD a c) ≈ @pzero C PC (F a) (F c).
Proof.
  rewrite pzero_zero_mor.
  unfold zero_mor.
  rewrite <- comp_assoc.
  rewrite fmap_comp.
  rewrite (adj_image_initial_unique
             (fmap[F] (@zero D (@zero_initial D ZD) c)) pzero).
  apply compose_pzero_left.
Qed.

Corollary adj_fmap_zero_mor {a c : D} :
  fmap[F] (@zero_mor D ZD a c) ≈ @zero_mor C ZC (F a) (F c).
Proof.
  rewrite <- pzero_zero_mor.
  rewrite adj_fmap_pzero.
  apply pzero_zero_mor.
Qed.

Section ImageBiproduct.

Context {a a' : D}.
Context (B : Biproduct a a').

(*
The image of the coproduct half.  The mediator is the transpose of
   the mediator downstairs: ⌊h ∘ fmap[F] i⌋ ≈ ⌊h⌋ ∘ i, so the two
   conditions on h are exactly the two conditions on ⌊h⌋. 

--------
副产品一半的图像。 中介者是转置
 楼下调解人： ⌊h ∘ fmap[F] i⌋ ≈ ⌊h⌋ ∘ i，所以两个
 h 上的条件恰好是 ⌊h⌋ 上的两个条件。 
*)
Definition adj_image_is_coproduct (z : C)
  (f : F a ~> z) (g : F a' ~> z) :
  ∃! h : F (biproduct_obj B) ~> z,
    (h ∘ fmap[F] (bi_inl B) ≈ f) ∧ (h ∘ fmap[F] (bi_inr B) ≈ g).
Proof.
  unshelve refine
    {| unique_obj :=
         from adj (bi_copair B (to adj f) (to adj g)) |}.
  - split.
    + apply adj_to_inj.
      rewrite to_adj_nat_l.
      rewrite from_adj_comp_law.
      apply bi_copair_inl.
    + apply adj_to_inj.
      rewrite to_adj_nat_l.
      rewrite from_adj_comp_law.
      apply bi_copair_inr.
  - intros v [Hl Hr].
    apply adj_to_inj.
    rewrite from_adj_comp_law.
    apply bi_copair_unique.
    + rewrite <- to_adj_nat_l.
      now apply to_adj_respects.
    + rewrite <- to_adj_nat_l.
      now apply to_adj_respects.
Defined.

(*
The image biproduct: the object is F of the object downstairs and
   ALL FOUR structure maps are the F-images of the originals.  That is
   what makes the transfer lemmas below available — a biproduct merely
   isomorphic to this one would not give them. 

--------
图像二积：该物体是楼下物体的F，并且
 所有四个结构图都是原始的 F 图像。 那就是
 是什么使得下面的转移引理可用——仅仅是一个二积
 与此同构不会给它们。 
*)
Definition adj_image_biproduct : Biproduct (F a) (F a').
Proof.
  unshelve eapply biproduct_of_coproduct.
  - exact (fobj[F] (biproduct_obj B)).
  - exact (fmap[F] (bi_inl B)).
  - exact (fmap[F] (bi_inr B)).
  - exact (fmap[F] (bi_exl B)).
  - exact (fmap[F] (bi_exr B)).
  - rewrite <- fmap_comp, bi_exl_inl.
    apply fmap_id.
  - rewrite <- fmap_comp, bi_exr_inr.
    apply fmap_id.
  - rewrite <- fmap_comp, bi_exl_inr.
    apply adj_fmap_zero_mor.
  - rewrite <- fmap_comp, bi_exr_inl.
    apply adj_fmap_zero_mor.
  - exact adj_image_is_coproduct.
Defined.

(*
The image biproduct is on the nose the image of the original: its
   object is F of the object, and ALL FOUR structure maps are the
   F-images of the originals.  A biproduct merely isomorphic to this
   one would not support the transfer below, whose diagonal step is
   proved against the F-images of the projections. 

--------
图像二积在鼻子上是原始图像：它的
 对象是对象的 F，所有四个结构图都是
 原件的 F 图像。 与此仅同构的二乘积
 不支持下面的转移，其对角线步长为
 根据投影的 F 图像证明。 
*)
Example image_biproduct_obj :
  biproduct_obj adj_image_biproduct = fobj[F] (biproduct_obj B).
Proof. exact eq_refl. Qed.

Example image_biproduct_inl :
  bi_inl adj_image_biproduct = fmap[F] (bi_inl B).
Proof. exact eq_refl. Qed.

Example image_biproduct_exl :
  bi_exl adj_image_biproduct = fmap[F] (bi_exl B).
Proof. exact eq_refl. Qed.

End ImageBiproduct.

End LeftAdjointBiproducts.

(**
*** Transfer: a functor whose image of a biproduct is again a
        biproduct is additive at that pair

    Stated for an ARBITRARY functor and with no adjunction anywhere:
    this is the reusable half of Riehl's corollary, and the adjunction
    is only what supplies its two hypotheses.  Those hypotheses are
    exactly what a left adjoint gives — that the images of the two
    injections make the image object a coproduct, and that the functor
    kills zero morphisms — and the missing product half is
    manufactured inside the proof by [biproduct_of_coproduct].

    Both halves of the biproduct are then spent, on different steps and
    for a reason worth naming: the copairing transfers by the coproduct
    universal property, but the DIAGONAL is a product-side mediator and
    transfers only by the product universal property.  That is why the
    coproduct alone does not suffice and why the bridge was needed. 

--------
*** 传递：一个函子，其二积的图像又是 a
 二积是该对的加法

针对任意函子且在任何地方都没有附加物的情况进行说明：
 这是里尔推论的可重复使用的一半，并且附加
 只是提供了它的两个假设。 这些假设是
 正是左伴随所给出的——两个图像
 注入使图像对象成为余积，并且函子
 杀死零态射——而缺失的乘积一半是
 由 [biproduct_of_coproduct] 在样张内制造。

然后将副产品的两半用于不同的步骤和
 出于一个值得命名的原因：副产品的共配对转移
 通用属性，但 DIAGONAL 是产品方中介，
 仅通过产品通用属性进行转让。 这就是为什么
 仅有余积是不够的，也是为什么需要这座桥的原因。 
*)

Section BiproductTransfer.

Context {C D : Category}.
Context `{ZC : @ZeroObject C}.
Context `{ZD : @ZeroObject D}.
Context `{PC : @Preadditive C}.
Context `{PD : @Preadditive D}.
Context {G : D ⟶ C}.

Theorem fmap_padd_of_preserved_coproduct {a c : D} (B : Biproduct a a)
  (Hz : ∀ u v : D, fmap[G] (@zero_mor D ZD u v) ≈ zero_mor)
  (Hco : ∀ (z : C) (u : G a ~> z) (v : G a ~> z),
     ∃! h : fobj[G] (biproduct_obj B) ~{C}~> z,
       (h ∘ fmap[G] (bi_inl B) ≈ u) ∧ (h ∘ fmap[G] (bi_inr B) ≈ v))
  (f g : a ~> c) :
  fmap[G] (padd f g) ≈ padd (fmap[G] f) (fmap[G] g).
Proof.
  assert (H11 : fmap[G] (bi_exl B) ∘ fmap[G] (bi_inl B) ≈ id)
    by (rewrite <- fmap_comp, bi_exl_inl; apply fmap_id).
  assert (H22 : fmap[G] (bi_exr B) ∘ fmap[G] (bi_inr B) ≈ id)
    by (rewrite <- fmap_comp, bi_exr_inr; apply fmap_id).
  assert (H12 : fmap[G] (bi_exl B) ∘ fmap[G] (bi_inr B) ≈ zero_mor)
    by (rewrite <- fmap_comp, bi_exl_inr; apply Hz).
  assert (H21 : fmap[G] (bi_exr B) ∘ fmap[G] (bi_inl B) ≈ zero_mor)
    by (rewrite <- fmap_comp, bi_exr_inl; apply Hz).
  (*
One local biproduct on the image object, with the four F-images as
     its structure maps.  It is introduced by [pose] rather than by a
     free-standing definition so that every reference below is to the
     same term; the four field readings that follow are then available
     by conversion and need no unfolding. 

--------
图像对象上的一个局部二积，其中四个 F 图像为
 其结构图。 它是由 [pose] 而不是由
 独立的定义，因此下面的每个引用都是对
 相同的术语； 随后可获得以下四个现场读数
 通过转换，无需展开。 
*)
  pose (GB := biproduct_of_coproduct
                (fmap[G] (bi_inl B)) (fmap[G] (bi_inr B))
                (fmap[G] (bi_exl B)) (fmap[G] (bi_exr B))
                H11 H22 H12 H21 Hco).
  assert (Ecop : fmap[G] (bi_copair B f g)
                   ≈ bi_copair GB (fmap[G] f) (fmap[G] g)).
  { symmetry.
    apply (bi_copair_unique GB (fmap[G] f) (fmap[G] g)
             (fmap[G] (bi_copair B f g))).
    - transitivity (fmap[G] (bi_copair B f g ∘ bi_inl B)).
      + rewrite fmap_comp; reflexivity.
      + now rewrite bi_copair_inl.
    - transitivity (fmap[G] (bi_copair B f g ∘ bi_inr B)).
      + rewrite fmap_comp; reflexivity.
      + now rewrite bi_copair_inr. }
  assert (Ediag : fmap[G] (bi_diag B) ≈ bi_diag GB).
  { unfold bi_diag.
    symmetry.
    apply (bi_pair_unique GB id id (fmap[G] (bi_pair B id id))).
    - transitivity (fmap[G] (bi_exl B ∘ bi_pair B id id)).
      + rewrite fmap_comp; reflexivity.
      + rewrite bi_exl_pair; apply fmap_id.
    - transitivity (fmap[G] (bi_exr B ∘ bi_pair B id id)).
      + rewrite fmap_comp; reflexivity.
      + rewrite bi_exr_pair; apply fmap_id. }
  rewrite <- (padd_copair_diag B f g).
  rewrite fmap_comp.
  rewrite Ecop, Ediag.
  apply (padd_copair_diag GB (fmap[G] f) (fmap[G] g)).
Qed.

End BiproductTransfer.

(**
*** Riehl's corollary at one pair of objects

    No additivity is assumed of F or of U: only that the source
    carries a biproduct of the domain with itself. 

--------
*** 里尔对一对物体的推论

 不假设 F 或 U 具有可加性：仅假设源
 带有域与其自身的二积。 
*)

Section LeftAdjointPadd.

Context {C D : Category}.
Context `{ZC : @ZeroObject C}.
Context `{ZD : @ZeroObject D}.
Context `{PC : @Preadditive C}.
Context `{PD : @Preadditive D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Theorem left_adjoint_fmap_padd_biproduct {a c : D} (B : Biproduct a a)
  (f g : a ~> c) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g).
Proof.
  apply (fmap_padd_of_preserved_coproduct B).
  - intros u v; apply adj_fmap_zero_mor.
  - apply (adj_image_is_coproduct B).
Qed.

End LeftAdjointPadd.

(**
*** The packaged corollary

    An [AdditiveFunctor] produced with no additivity hypothesis on
    either adjoint.  The preadditive structures are the ones underlying
    the two Ab-enrichments, so the conclusion is about the same [padd]
    the rest of this file uses; the negation plays no role in the
    argument and is present only because [AdditiveFunctor] is declared
    over [AbEnriched]. 

--------
*** 打包的推论

 [AdditiveFunctor] 的产生没有可加性假设
 任一伴随。 预加法结构是基础结构
 两种 Ab 富集，因此结论与 [padd] 大致相同
 该文件的其余部分使用； 否定在其中不起任何作用
 参数并且仅因为声明了 [AdditiveFunctor] 而存在
 超过 [AbEnriched]。 
*)

Definition left_adjoint_additive_of_biproducts
  {C D : Category} {AC : AbEnriched C} {AD : AbEnriched D}
  `{ZC : @ZeroObject C} `{ZD : @ZeroObject D}
  {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
  (HB : @HasBiproducts D ZD) :
  @AdditiveFunctor D C AD AC F.
Proof.
  constructor.
  intros a c f g.
  exact (@left_adjoint_fmap_padd_biproduct C D ZC ZD
           (@abenriched_preadditive C AC) (@abenriched_preadditive D AD)
           F U A a c (@biproduct D ZD HB a a) f g).
Defined.
