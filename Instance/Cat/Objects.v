(* * * The objects functor on the category of categories / * * 范畴的对象函子在范畴的范畴上 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”,
 Springer GTM 5, 2nd ed., §IV.2 Exercise 9, printed p. 90
 (maclane:IV.2:ex9), where the result is attributed to
 N. Smythe.
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/indiscrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/Cat
 nLab:      https://ncatlab.org/nlab/show/strict+category
 nLab:      https://ncatlab.org/nlab/show/connected+component
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

 Mac Lane's exercise asks for the adjoint string carried by the functor
 that sends a category to its set of objects:

 Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete

 -- four functors between a category of categories and a category of
 sets, each adjoint to the next.  This file is the FOUNDATION of that
 development: it builds the objects functor and the middle adjunction
 [StrictCat_Disc ⊣ StrictCat_Objects], and it SETTLES THE DOMAIN AND
 CODOMAIN, which the two remaining modules inherit.  Both halves of
 that settlement are forced by REFUTATION ONCE THE TARGET IS REQUIRED
 TO COMPARE OBJECT MAPS BY LEIBNIZ EQUALITY, and both refutations are
 proved below (§6 and §7).  Read that qualifier: it is load-bearing.
 An objects functor [Cat ⟶ Sets] DOES exist if the objects are given
 the ISOMORPHISM setoid instead -- it compiles with zero obligations
 and is closed under the global context -- and issue #357's own item 1
 names that alternative (“with equality, or with isomorphism, if a
 choice has to be made -- the exercise wants the strict version”).  So
 the strict reading is the EXERCISE'S choice; what §6 and §7 prove is
 that ONCE it is taken, the domain and codomain are forced.
 Throughout, a Roman
 numeral names one of the notes that follow and a [§] names a section
 of the development proper.

 Delivered here:

 (a) [disc_ext]: the extension of a function [A → obj[C]] to a
 functor [DiscreteCat A ⟶ C].  This is NOT the tree's
 [DiscreteCat_Functor], and the difference is a universe pin --
 see item I, THIRD.

 (b) [StrictCat_Objects : StrictCat ⟶ Coq], the objects functor,
 and [StrictCat_Disc : Coq ⟶ StrictCat], the discrete functor.

 (c) [disc_adj_iso], the hom-setoid isomorphism, and the packaged
 record [Disc_Objects_Adjunction], of type
 [StrictCat_Disc ⊣ StrictCat_Objects].  There is no analogue here
 of the universe wall that Instance/Top/Forgetful.v meets for the
 corresponding [Top] triple -- see §8.

 (d) [Disc_Full] and [Disc_Faithful]: the discrete functor is fully
 faithful, which is the categorical reading of the fact that the
 unit of the adjunction is the identity ([unit_is_id], §5).

 (e) The two refutations that force the domain and codomain:
 [objects_not_functorial_over_Cat] and
 [no_carrier_functor_Sets_StrictCat], the latter instantiated at
 BOTH the discrete and the indiscrete object map, so that it is
 binding on the right-hand wing as well as on this file.

 (f) [Objects_not_Faithful]: the objects functor genuinely forgets.

 I. A PRIOR-ART CORRECTION, ON THREE COUNTS, EACH MEASURED.

 FIRST, the catalog issue states that the indiscrete half “has no
 construction at all -- searching for it finds only comments”.  That
 is FALSE.  Instance/Discrete/Reconstruct.v has declared
 [Indiscrete (A : Type) : Category], with [hom := fun _ _ => unit],
 [homset := Morphism_equality] and every category law discharged by
 the ambient obligation tactic, since it was written; it is CONSUMED
 here (§6 uses it for the [Cat] refutation) and nothing rebuilds it.
 It has TWO independent consumers already: Theory/Skeleton/
 Separation.v, and -- worth reading beside §6 -- Instance/Cat/
 Pullback.v, whose [IB := Indiscrete bool] drives
 [FibreProduct_not_Cat_pullback], a refutation of a DIFFERENT
 statement turning on the SAME fact, that [Cat] cannot see the
 difference between [true] and [false] there.  (Two further files
 match a name search and are not consumers: Instance/Top.v has an
 unrelated [Section Indiscrete] about the indiscrete TOPOLOGY, and
 Instance/Top/Forgetful.v mentions the word only in prose.)

 What is genuinely absent is narrower and worth stating precisely:
 [Indiscrete] is an OBJECT MAP only.  No arrow action, no functor
 and no adjunction exists for it anywhere in the tree -- both
 consumers above use it on objects alone.

 SECOND, the issue's work item 4 asks that the connected-components
 functor be defined.  That is FALSE too: Theory/Connected/
 Components.v declares [Pi0 : Cat ⟶ Sets] with [fobj := pi0]
 and [fmap := pi0_fmap], and its three functor laws are proved
 there.  Only the ADJUNCTION is missing.  Item II below records the
 consequence: [Pi0] cannot join the string built here.

 THIRD -- and this one WAS a correction to a donor rather than to
 the issue, which flagged the risk correctly -- Instance/Discrete.v's
 [DiscreteCat_Functor] was universe-unannotated and PINNED ITS
 SOURCE AT [Set]:

 DiscreteCat_Functor@{u u0 u1 u2} :
 ∀ {A : Type@{u}} {C : Category@{u0 u2 u2}},
 (A → obj[C]) → DiscreteCat@{u Set Set} A ⟶ C

 Building [StrictCat_Disc] over it would have propagated a [Set]
 pin on the hom AND proof universes of every discrete category, and
 [disc_ext] is the same construction with the binders written out.

 RECORDED CORRECTION.  That signature is HISTORY.  In the PR
 “algebraic carriers are sets” (2026-09-17) the donor was annotated
 in place at Instance/Discrete.v as
 [DiscreteCat_Functor@{o h p uo uh up +}], and it now reaches every
 level [disc_ext] reaches; §8's [Section SetPin] records the repair
 and keeps the two former negatives as positive CONTROLS, so what
 that section guards is an AGREEMENT between three interchangeable
 discrete extensions rather than a pin.  An earlier revision of this
 paragraph also said the pin was “a minimization artifact of the
 [Build_Quiver_Standard_Eq] family that
 Construction/Free/Quiver/Examples.v already records”; that
 attribution named the wrong donor and is withdrawn -- [About] put
 it on [DiscreteCat_Functor]'s own elaboration.  [disc_ext] is
 retained for the reason §1 and §8 give, that it is written with
 [refine] and so mints no auxiliary universe.

 II. THE DOMAIN DECISION: [StrictCat] AND [Coq], BOTH FORCED.

 The issue's item 1 asks whether the objects functor should live on
 [StrictCat], and Theory/Connected/Components.v already
 flags the question from the other side, noting that [Cat]'s
 hom-setoid is natural isomorphism and that “a functor into [Sets]
 out of a strict category of categories would be a different
 statement and is not built”.  The answer is settled here by two
 counterexamples, not by taste.

 THE SOURCE MUST BE [StrictCat].  Any objects functor must send a
 pair of [≈]-equal functors to a pair of [≈]-equal maps, and both
 candidate targets compare object maps by LEIBNIZ equality: the
 [equiv] of [ObjSetoid] (Theory/Connected/Components.v) is
 [@eq obj[C]], and [Coq]'s hom-setoid is pointwise [=]
 (Instance/Coq.v).  So [fmap_respects] for any objects functor INTO
 SUCH A TARGET is exactly the proposition [ObjRespectsCat] of §6 --
 and over [Cat] that proposition is FALSE.  It is NOT an obligation
 every conceivable objects functor owes: give the objects the
 isomorphism setoid and [fmap_respects] becomes [fobj_iso], which
 every functor satisfies.  The witness is the swap endofunctor of
 [Indiscrete bool]: every hom-set there is [unit], so the identity
 functor and the negation functor are naturally isomorphic, hence
 [≈] in [Cat], while their object maps differ at [true].  Over
 [StrictCat] the same proposition is the FIRST PROJECTION of the
 hom-setoid ([objects_respects_StrictCat], a [:=] with no tactic),
 because [Functor_StrictEq_Setoid]'s [eq_on_obj] field IS it.

 THE TARGET MUST BE [Coq].  This half is not in the issue at all,
 and it is the mirror image: [StrictCat_Disc] must send a pair of
 [≈]-equal maps to [≈]-equal functors, and [≈] in [StrictCat] again
 demands Leibniz equality of object maps -- which [Sets]-morphisms
 do not supply, [≈] there being the target setoid's own relation.
 §7 proves the general form: NO object map [K : Sets → StrictCat]
 that is pointed, injective on points and natural on points can
 respect [≈], the witness being [bool] under the everywhere-true
 setoid.  It is instantiated at the discrete object map AND at the
 indiscrete one, so it forces the target for the right-hand wing
 too, which is why it is stated generally rather than for
 [StrictCat_Disc] alone.
 [Coq] is AN in-tree category of sets (not the only one --
 Instance/Ens.v and Instance/EnsV.v also compare morphisms pointwise
 by [=]; [Coq] is simply the natural choice here) whose [≈] on
 morphisms IS
 pointwise Leibniz equality, which is exactly [StrictCat]'s
 [eq_on_obj]; that coincidence is what makes the string possible.

 CONSEQUENCE FOR THE FOURTH ADJOINT, STATED RATHER THAN GLOSSED.
 [Pi0]'s domain is [Cat] and its codomain is [Sets], so it shares
 NEITHER end with [StrictCat_Objects : StrictCat ⟶ Coq], and by §6
 it cannot simply be restricted to [StrictCat] and re-aimed, since the
 objects functor does not exist over [Cat] at all.  What follows is
 that [Components ⊣ StrictCat_Disc] is a SEPARATE statement over a
 different pair of categories, not a fourth term of this string, and any
 module delivering it must either build a [Coq]-valued π₀ or state
 the adjunction elsewhere.  NOTHING HERE PROVES that no such
 [Coq]-valued π₀ exists; that question is left open, and the
 reduction to quotient types that suggests it is hard is an
 argument, not a theorem, and is not made here.

 NAMING, AND WHY THE OBVIOUS NAMES WERE UNAVAILABLE.  Both [Discrete]
 and [Indiscrete] are taken: [Discrete] is Structure/Discrete.v's
 PREDICATE on a category (an assertion that it has only identity
 morphisms), and [Indiscrete] is the category constructor of item I
 above.  And [Objects] is taken too, by Solver/Expr.v's reification
 CLASS -- a live hazard rather than a cosmetic one, since shadowing it
 would break the Solver's typeclass resolution wherever both modules
 are imported.  This file therefore follows the Instance/Top/
 Forgetful.v precedent and prefixes the functors with the structured
 category, whichever way they run: [StrictCat_Objects] and
 [StrictCat_Disc] here, and [StrictCat_Indisc] for the right-hand
 wing's mirror.  These names are binding on the remaining modules;
 all three were verified to have zero tree-wide occurrences first.

 III. WHAT IS CONSUMED, AND WHAT IS BUILT.

 CONSUMED, not rebuilt: Instance/Discrete.v's [DiscreteCat] -- the
 SHAPE, whose three universes are already free, so only the FUNCTOR
 [DiscreteCat_Functor] is replaced and only for the reason in item I
 (it is still named here, in §8, as the subject of a probe);
 Instance/Discrete/Reconstruct.v's [Indiscrete];
 Instance/StrictCat.v's [StrictCat] with Theory/Functor.v's
 [Functor_StrictEq_Setoid]; Instance/Coq.v's [Coq];
 Instance/Cat.v's [Cat]; Theory/Functor.v's [Build_Functor],
 [fmap_id], [Full] and [Faithful]; Theory/Isomorphism.v's
 [Isomorphism] and [iso_from_to]; Theory/Adjunction.v's
 [Adjunction], [Build_Adjunction'], [unit] and [counit]; and
 [Eqdep_dec.UIP_dec], which is Hedberg and axiom-free, in §9 alone.
 Not one category, functor-category or adjunction lemma is
 re-proved.

 BUILT: [disc_ext], [StrictCat_Objects], [StrictCat_Disc],
 [disc_adj_iso], [Disc_Objects_Adjunction], [Disc_Full],
 [Disc_Faithful], the two refutations with their witnesses, and
 [Objects_not_Faithful].

 IV. STRENGTHS, MEASURED STRICT-FIRST.  Ten readbacks hold at [eq_refl]
 and are shipped as [Example]s: the object and arrow actions of
 [StrictCat_Objects] ([objects_obj], [objects_map]); the object
 action of [StrictCat_Disc] and the object action of its arrow
 action ([disc_on_obj], [disc_map]); both legs of the transposition
 ([adj_to_forgets] and [adj_from_extends]); one of the two round
 trips ([adj_to_from]); THE UNIT IS THE IDENTITY FUNCTION ON THE
 NOSE ([unit_is_id]) and the counit is the identity on objects
 ([counit_obj]); and the object half of the remaining round trip
 ([roundtrip_obj]).

 EXACTLY ONE STEP IS [≈]-ONLY, AND ITS CAUSE IS EXHIBITED RATHER
 THAN DESCRIBED.  The round trip [disc_ext (fobj[F]) ≈ F] is
 REFUTED at [eq_refl] ([adj_from_to_strict], §5), and the failure is
 localized to a single field by a pair of probes with a passing
 control between them: the OBJECT map returns on the nose
 ([roundtrip_obj]), the ARROW map does not ([roundtrip_map]), and
 what separates them is precisely [fmap_id] -- [disc_ext] sends the
 only morphism of a discrete hom-set to [id], while [F] sends it to
 [fmap[F] id], and [roundtrip_map_equiv] closes the gap by
 [symmetry; exact (fmap_id)] and nothing else.  This is also why
 [Disc_Full] costs one line and [Disc_Faithful] costs none.

 An engineering note on that step, worth carrying: [apply fmap_id]
 FAILS there, reporting that it cannot unify [fmap[?F] id{?C}] with
 [fmap[x] eq_refl] -- the elaborator will not unify [id{?C}] against
 the [eq_refl] that IS the identity of a discrete category.  The
 fully applied [exact (@fmap_id _ _ x a)] works.

 The adjunction is packaged through [Build_Adjunction']
 (Theory/Adjunction.v) rather than [Build_Adjunction], and that
 is a measured economy rather than a style choice: the smart
 constructor asks only for the two [to]-side naturality clauses,
 which live in [Coq], where [≈] is pointwise [=] -- so BOTH CLOSE BY
 [reflexivity].  The full constructor would have put the same two
 naturality squares in [StrictCat], i.e. as transport-laden
 strict-equality-of-functors goals.

 V. UNIVERSES, MEASURED OFF BOTH THE BLOCK AND THE BINDER.

 NO CONSTRAINT BLOCK IN THIS FILE CONTAINS A UNIVERSE EQUATION.
 Every entry of every block is a [<] or a [<=]; that was checked
 constant by constant, not sampled.  [disc_ext@{o h p q}] carries
 only [DiscreteCat]'s own bounds together with [h <= p], which is
 [Class Category]'s, and contains no [Set] -- which is the whole
 point of item I.3.  [StrictCat_Objects] and [StrictCat_Disc]
 each take six universe binders, spread six DISTINCT levels across
 them, and identify nothing.

 BUT THE BINDER IS WHERE THE IDENTIFICATION HIDES, AND THIS FILE
 REPORTS IT AGAINST ITSELF.  [Disc_Objects_Adjunction@{u u0 u1}]
 displays as

 StrictCat_Disc@{u u1 u u1 u u1}
 ⊣ StrictCat_Objects@{u u u1 u u1 u1}

 -- twelve slots filled from two levels, so the inner categories
 come out as [Category@{u1 u1 u1}], objects, homs and proofs
 identified, on a block whose only strict entry is [u1 < u].  A
 reader who inspects the block alone concludes “no identification”
 and is WRONG.  That identification is MINIMIZATION AND NOT CONTENT,
 and §8 guards the claim rather than asserting it: the adjunction
 TYPE is formable with the inner hom universe declared STRICTLY
 BELOW the inner object universe.  Producing the annotated
 constants is not attempted here -- [Program]'s obligations mint
 fresh universes, so the annotation cannot simply be written on --
 and the gap is recorded as repairable, not as unavoidable.

 Two donor identifications are named rather than repaired, and
 neither is introduced here: [StrictCat@{u u0 u1 u2 u3}] is declared
 at [Category@{u u0 u0}], so it identifies its OWN hom and proof
 universes; and [Coq@{u u0 u1 u2}] carries [u0 = u1] and [u0 = u2]
 in its own block.  Those are the only universe equations in the two
 ambient categories' OWN declarations -- a claim about those two
 constants, not about the whole transitive closure, which was not
 swept.  Neither is claimed unavoidable.

 VI. AUDIT.  68 constants, ALL CLOSED UNDER THE GLOBAL CONTEXT
 ([Print Module] lists 68 and the file declares no [Record], [Class]
 or [Inductive], so there is no unlisted [Build_*]; each was queried
 by fully qualified name, which is what reaches the 25 [Program]
 obligations a [.glob] sweep cannot see; 43 names are declared in
 the source and 43 + 25 = 68).  ZERO of the 68 names collides
 anywhere in the tree -- a sweep that FOUND one, and it was live:
 [Objects] is Solver/Expr.v's reification class, which is why the
 functors carry the [StrictCat_] prefix (item II).  THREE [Fail]
 probes, of TWO KINDS kept lexically apart -- two CONVERSION
 in §5, one FORMABILITY in §8 -- each stripped once and its kind
 read off the whole error message, beside an instrument check and
 twelve positive controls -- nine [Check]s in §8 and three passing
 [Example]s beside the §5 negatives.  An earlier revision of this
 item counted FIVE probes (three formability) and ten controls
 (seven [Check]s); the PR “algebraic carriers are sets”
 (2026-09-17) turned §8's two [Set] negatives into controls, which
 is where both differences come from.  Each of the three section-local
 [Constraint] declarations was additionally tested by deletion, and
 they behave differently -- one INERT, one LOAD-BEARING, one
 meaning-giving; §8 records which is which, since a reader who
 assumes a [Constraint] is doing work is wrong a third of the
 time here.  Rename-simulated 6/6 on an unpadded
 denominator (the constants a NEGATIVE names, file-local ones by the
 definition-site method since a whole-file rename is a no-op), every
 one of them breaking the file at a non-[Fail] line.  That exercise
 FOUND a vacuous guard: [DiscreteCat_Functor] was named only inside
 its own [Fail], so a rename of the donor would have turned that
 probe silently green; the control that closes it exists for that
 reason.  That hazard is now moot in this file -- since the donor's
 annotation the probe in question IS a [Check] -- but the control
 is kept, because a rename would then break the file outright,
 which is the stronger guard.

 VII. WHAT IS NOT DELIVERED.

 No [StrictCat_Indisc], and no [StrictCat_Objects ⊣ StrictCat_Indisc]:
 that is the right-hand wing, which this file only makes possible --
 by fixing the two categories, and by proving in §7 that the
 indiscrete object map cannot be aimed at [Sets] either.  In
 particular NOTHING here claims that the right adjoint exists.

 No [Components ⊣ StrictCat_Disc], and no [Coq]-valued π₀ at all:
 item II records why [Pi0] cannot be reused, and records equally
 that no impossibility is proved for a differently-built π₀.

 No comparison with Theory/Connected/Components.v's [ObjSetoid],
 which is the [Sets]-valued object map: §7 shows the [Sets]-valued
 STRING is unavailable, but nothing here states a functor
 [StrictCat ⟶ Sets] (which does exist) nor relates it to this one.

 No uniqueness statement for either adjoint; no naturality of
 [disc_adj_iso] in [A] or [C] beyond the two clauses
 [Build_Adjunction'] consumes; no monad or comonad on either side of
 the adjunction and hence nothing about idempotency; no statement
 that [StrictCat_Disc] is a reflective or coreflective embedding; no
 preservation, reflection or creation of limits; no [Full] or
 [Faithful] for [StrictCat_Objects] beyond §9's REFUTATION of
 faithfulness; no equivalence between [StrictCat] and anything; and
 no annotated ([Set]-free-inner-universe) restatement of the packaged
 adjunction, per §5. 

 --------
 书籍：      Mac Lane，《为工作中的数学家准备的范畴论》，
 Springer GTM 5，第2版，§IV.2 习题 9，印刷第90页
 (maclane:IV.2:ex9)，结果归功于
 N. Smythe。
 nLab:       https://ncatlab.org/nlab/show/discrete+category 
 nLab:       https://ncatlab.org/nlab/show/indiscrete+category 
 nLab:       https://ncatlab.org/nlab/show/adjoint+string 
 nLab:       https://ncatlab.org/nlab/show/Cat 
 nLab:       https://ncatlab.org/nlab/show/strict+category 
 nLab:       https://ncatlab.org/nlab/show/connected+component 
 维基百科:   https://en.wikipedia.org/wiki/Adjoint_functors 

 Mac Lane 的习题要求求出由将类别映射到其对象集合的函子所携带的伴随链：

 Components  ⊣  Discrete  ⊣  Objects  ⊣  Indiscrete-- 四个函子在一个类别的类别与集合类别之间，每一个都是下一个的伴随。这个文件是该发展的基础：它构建了对象函子和中间伴随 [StrictCat_Disc ⊣ StrictCat_Objects]，并且确定了定义域和值域，这是剩下的两个模块继承的。这种确定的两部分都是通过反驳强制的，一旦要求目标通过莱布尼茨等式比较对象映射，并且这两个反驳在下文（第6节和第7节）中被证明。注意这个限定词：它是承重的。如果对象被赋予同构集合论元组，则一个对象的函子 [Cat ⟶ Sets] 的确存在——它可以在没有任何义务的情况下编译，并且在全局上下文中是封闭的——而问题 #357 的第 1 条目命名了该替代方案（“如果必须做选择，则使用等式或同构——练习要求严格版本”）。因此，严格的解读是练习的选择；§6 和 §7 证明的是，一旦选择了它，定义域和余域就被强制确定。整个文中，罗马数字表示后续注释之一，而 [§] 表示具体开发部分的章节。

 以下是具体内容：

 (a) [disc_ext]：将函数 [A → obj[C] ] 扩展为函子 [DiscreteCat A ⟶ C]。这不是树的 [DiscreteCat_Functor]，差别在于宇宙标记——见第 I 项，第 3 点。(b)  [StrictCat_Objects : StrictCat ⟶ Coq]，对象函子，
 和 [StrictCat_Disc : Coq ⟶ StrictCat]，离散函子。

 (c)  [disc_adj_iso]，同态集合等价同构，以及打包记录 [Disc_Objects_Adjunction]，类型为
 [StrictCat_Disc ⊣ StrictCat_Objects]。在此处没有类似于 Instance/Top/Forgetful.v 对应 [Top] 三元组遇到的宇宙墙——参见 §8。

 (d)  [Disc_Full] 和 [Disc_Faithful]：离散函子是全忠实的，这在范畴论中解释为伴随函子的单位是恒等映射 ([unit_is_id], §5) 的事实。

 (e)  强制定义域和值域的两个反证：
 [objects_not_functorial_over_Cat] 和
 [no_carrier_functor_Sets_StrictCat]，后者在离散对象映射和非离散对象映射上都实例化，因此它不仅作用于右翼，也作用于此文件。(f) [Objects_not_Faithful]：对象函子确实会遗忘。

 I. 一项已有技术的修正，从三个方面进行，每个方面都有测量。首先，目录问题中指出，不可分半部分“根本没有任何构造——搜索它只能找到评论”。这是错误的。Instance/Discrete/Reconstruct.v 已经声明了 [Indiscrete (A : Type) : Category]，以及 [hom := fun _ _ => unit]、[homset := Morphism_equality]，并且其每个类别法则自编写以来都通过环境义务策略得到 discharged；它在这里被使用（第6节用于 [Cat] 的反驳），没有任何东西重建它。它已经有两个独立的使用者：Theory/Skeleton/Separation.v，以及——值得在第6节旁边阅读的——Instance/Cat/Pullback.v，其中 [IB := Indiscrete bool] 驱动 [FibreProduct_not_Cat_pullback]，这是对一个不同命题的反驳，该命题依赖于同一个事实，即 [Cat] 无法区分那里的 [true] 和 [false]。（还有两个文件匹配名称搜索，但不是使用者：Instance/Top.v 有一个与离散拓扑无关的 [Section Indiscrete]，Instance/Top/Forgetful.v 只在文字描述中提到这个词。）

 真正缺失的是更具体的内容，值得准确说明：[Indiscrete] 仅是一个对象映射。树中的任何位置都没有箭头作用、函子或伴随存在——上面两个使用者仅在对象上使用它。第二，问题的工作项4要求定义连通分量函子。这也是错误的：Theory/Connected/Components.v 声明了 [Pi0 : Cat ⟶ Sets] 与 [fobj := pi0] 和 [fmap := pi0_fmap]，并且其三个函子定律在那里得到了证明。只有伴随（ADJUNCTION）缺失。下面的项目 II 记录了结果：[Pi0] 无法加入这里构建的字符串。

 第三——而这一项是对捐赠者的更正，而不是对问题的更正（问题本身正确地标出了风险）——Instance/Discrete.v 的 [DiscreteCat_Functor] 没有注释宇宙，并且将其源固定在 [Set]：

 DiscreteCat_Functor@{u u0 u1 u2} :
 ∀ {A : Type@{u}} {C : Category@{u0 u2 u2}},
 (A → obj [C] ) → DiscreteCat@{u Set Set} A ⟶ C在其上构建 [StrictCat_Disc] 将会在 hom 上传播一个 [Set] 引脚，并证明每个离散范畴的宇宙，而 [disc_ext] 是同样的构造，只是将绑定器写了出来。已记录更正。那个签名已经成为历史。在 PR “代数承载体是集合”（2026-09-17）中，捐赠者在 Instance/Discrete.v 中被标注为 [DiscreteCat_Functor@{o h p uo uh up +}]，现在它可以达到 [disc_ext] 所达到的每个级别；第 8 节的 [Section SetPin] 记录了修复，并将两个以前的负值作为正控制保留，所以该部分所保护的是三个可互换离散扩展之间的协议，而不是一个固定器。这一段的早期修订版本还说固定器是 [Build_Quiver_Standard_Eq] 家族的 “最小化人工产物”，Construction/Free/Quiver/Examples.v 已经记录了这一点；该归属指出了错误的捐赠者，因此已撤回——[About] 将其归于 [DiscreteCat_Functor] 自己的阐述。[disc_ext] 被保留的原因如第 §1 和 §8 所述，因为它与 [refine] 一起书写，因此不生成任何辅助宇宙。

 II. 域决定：[StrictCat] 和 [Coq]，均被强制。

 该问题的第1项询问对象函子是否应存在于 [StrictCat]，而 Theory/Connected/Components.v 已经从另一侧标记了这一问题，指出 [Cat] 的同类集是自然同构，并且“从严格的类目类别进入 [Sets] 的函子将是一个不同的陈述，并且尚未构建”。此处通过两个反例解决了答案，而不是凭个人喜好。源必须是 [StrictCat]。任何对象函子必须将一对 [≈]-相等的函子映射到一对 [≈]-相等的映射，并且两个候选目标通过莱布尼茨相等比较对象映射：ZW63WZZ 在 [ObjSetoid] (Theory/Connected/Components.v) 中是 [@eq obj[C]，而 [Coq] 的同态集是逐点 [=] (Instance/Coq.v)。因此，对于任何进入这种目标的对象函子，ZW68WZZ 恰好是 §6 中的命题 [ObjRespectsCat] ——并且在 [Cat] 上，该命题是假的。这并不是每一个可想象的对象函子都必须承担的义务：给对象同构集，ZW71WZZ 就变成了 [fobj_iso]，而每个函子都满足这一点。证人是 [Indiscrete bool] 的交换端函子：在那里每个同态集合都是 [unit]，因此恒等函子和取反函子自然同构，因此在 [Cat] 中 [≈] ，而它们的对象映射在 [true] 上不同。在 [StrictCat] 上，同样的命题是同态集合体 ([objects_respects_StrictCat], a [:=] 无策略) 的第一投影，因为 [Functor_StrictEq_Setoid] 的 [eq_on_obj] 字段就是它。目标必须是 [Coq]。这一半根本不在问题中，而且它是镜像：[StrictCat_Disc] 必须将一对 [≈] -相等的映射发送到 [≈] -相等的函子，而 [≈] 在 [StrictCat] 中再次要求对象映射的莱布尼茨相等性——[Sets] -态射无法提供，[≈] 在那里是目标集合的自身关系。§7 证明了通用形式：没有任何对象映射 [K : Sets → StrictCat] 是指向的、在点上单射且在点上自然的，可以尊重 [≈]，其证据是 [bool] 在处处为真的集合上成立。它在离散对象映射和不可分对象映射上都有实例化，因此也强制了右侧部分的目标，这就是为什么它被一般性地陈述，而不仅仅针对 [StrictCat_Disc]。[Coq] 是集合的一个树内范畴（不是唯一的——Instance/Ens.v 和 Instance/EnsV.v 也通过 [=] 对态射进行逐点比较；[Coq] 仅仅是在这里的自然选择），其 [≈] 在态射上的操作是逐点 Leibniz 相等，这正好是 [StrictCat] 的 [eq_on_obj]；这种巧合使得这个表达式成为可能。对第四个伴随的结果，直接陈述而非注释。
 [Pi0] 的定义域是 [Cat]，值域是 [Sets]，因此它与 [StrictCat_Objects : StrictCat ⟶ Coq] 没有共享端点，根据 §6
 它不能简单地限制到 [StrictCat] 并重新指向，因为在 [Cat] 上根本不存在对象函子。 由此可知，
 [Components ⊣ StrictCat_Disc] 是在一对不同范畴上的独立陈述，而不是这一串中的第四项，任何提供它的模都必须要么构造一个 [Coq] 值的 π₀，要么在其他地方陈述伴随。 此处没有任何内容证明不存在这样的 [Coq] 值的 π₀；这个问题仍然开放，而将其简化为商类型所暗示的困难性是一个论证，而不是定理，并且在此没有给出。命名，以及为什么显而易见的名字不可用。[Discrete] 和 [Indiscrete] 都已经被占用：[Discrete] 是 Structure/Discrete.v 中一个范畴的谓词（断言它只有恒等态射），而 [Indiscrete] 是上述项目 I 的范畴构造器。[Objects] 也已经被占用了，是 Solver/Expr.v 中的 reification 类——这是一个实际的危险而非表面问题，因为如果遮蔽它，将会破坏在同时导入这两个模块时 Solver 的类型类解析。因此，本文件遵循 Instance/Top/Forgetful.v 的先例，并为函子加上结构化范畴的前缀，无论它们如何运行：这里是 [StrictCat_Objects] 和 [StrictCat_Disc]，右侧模块镜像则是 [StrictCat_Indisc]。这些名称对于剩余的模块是有约束力的；
 所有三个名称首先都被验证在整个树中没有出现过。

 III. 被消耗的是什么，以及被构建的是什么。已被使用，未重建：Instance/Discrete.v 的 [DiscreteCat] —— 其形状，其三个宇宙已自由，因此仅 FUNCTOR [DiscreteCat_Functor] 被替换，并且仅出于第 I 项中的原因（它仍在此处，第 8 节中，作为探针的对象）；Instance/Discrete/Reconstruct.v 的 [Indiscrete]；Instance/StrictCat.v 的 [StrictCat] 与 Theory/Functor.v 的 [Functor_StrictEq_Setoid]；Instance/Coq.v 的 [Coq]；Instance/Cat.v 的 [Cat]；Theory/Functor.v 的 [Build_Functor]、[fmap_id]、[Full] 和 [Faithful]；Theory/Isomorphism.v 的 [Isomorphism] 和 [iso_from_to]；Theory/Adjunction.v 的 [Adjunction]、[Build_Adjunction']、[unit] 和 [counit]；以及仅在第 9 节中存在的 Hedberg 且无公理的 [Eqdep_dec.UIP_dec]。没有一个范畴、函子范畴或伴随引理被重新证明。构建：[disc_ext]，[StrictCat_Objects]，[StrictCat_Disc]，[disc_adj_iso]，[Disc_Objects_Adjunction]，[Disc_Full]，[Disc_Faithful]，两个带其见证的反驳，以及[Objects_not_Faithful]。

 四、强度，按严格优先顺序测量。十个回读保持在[eq_refl]，并以[Example]形式运输：[StrictCat_Objects]的对象和箭头操作（[objects_obj]，[objects_map]）；[StrictCat_Disc]的对象操作及其箭头操作的对象操作（[disc_on_obj]，[disc_map]）；换位的两条支腿（[adj_to_forgets]和[adj_from_extends]）；两个往返中的一个（[adj_to_from]）；该单位在鼻子上的单位函数（[unit_is_id]），余单位在对象上的恒等（[counit_obj]）；以及剩余往返的对象部分（[roundtrip_obj]）。确切地说，只有一步是 [≈]，并且它的原因是展示出来的，而不是描述的。往返 [disc_ext (fobj[F] ) ≈ F] 在 [eq_refl] ( [adj_from_to_strict], §5) 被反驳，这个失败通过一对探针在它们之间的通过控制而局部化到一个字段：OBJECT 映射精确返回 ( [roundtrip_obj] )，ARROW 映射没有返回 ( [roundtrip_map] )，将它们区分开来的正是 [fmap_id] -- [disc_ext] 将一个离散同态集的唯一态射发送到 [id]，而 [F] 将它发送到 [fmap[F] id]，而 [roundtrip_map_equiv] 通过 [symmetry; exact (fmap_id)] 弥合了差距，仅此而已。这也是为什么 [Disc_Full] 需要一行，而 [Disc_Faithful] 不需要任何行的原因。关于该步骤的一条工程说明，值得记下：[apply fmap_id] 在这里失败，报告无法将 [fmap[?F] id{?C}] 与 [fmap[x] eq_refl] 统一——展开器不会将 [id{?C}] 与 [eq_refl]（它是离散范畴的恒等元）统一。完全应用的 [exact (@fmap_id _ _ x a)] 可以正常工作。这个伴随通过 [Build_Adjunction'] (Theory/Adjunction.v) 打包，而不是 [Build_Adjunction]，这是一种经过衡量的经济性，而不是风格选择：智能构造器只要求两个 [to] 侧的自然性条款，这些条款存在于 [Coq]，其中 [≈] 是逐点 [=] ——所以两者都靠近 [reflexivity]。完整的构造器会将相同的两个自然性方格放在 [StrictCat]，即作为带有传输的函子严格等式目标。

 V. 宇宙，同时从代码块和绑定器进行衡量。此文件中的约束块不包含宇宙方程。
 每个块的每一项都是 [<] 或 [<=]；这是逐个常量检查的，而不是抽样的。[disc_ext@{o h p q}] 只携带 [DiscreteCat] 自身的界限以及 [h <= p]，这就是 [Class Category] 的界限，并且不包含 [Set]——这正是条目 I.3 的要点。[StrictCat_Objects] 和 [StrictCat_Disc] 各自使用六个宇宙绑定器，在它们之间分布六个不同的层级，并且不标识任何内容。

 但绑定器是识别隐藏的地方，而此文件自己报告了它。[Disc_Objects_Adjunction@{u u0 u1}] 显示为

 StrictCat_Disc@{u u1 u u1 u u1}
 ⊣ StrictCat_Objects@{u u u1 u u1 u1}-- 从两个层级填充了十二个槽，因此内部类别显示为 [Category@{u1 u1 u1}]，对象、Hom 和证明已被识别，在一个唯一严格条目为 [u1 < u] 的区块上。单独检查该区块的读者会得出“未识别”的结论，这种结论是错误的。该识别是最小化而非内容，而第8节保护该主张，而不是断言它：附加类型可以形成，前提是内部 Hom 宇宙被严格声明在内部对象宇宙之下。此处不尝试生成带注释的常量——[Program] 的义务是铸造新的宇宙，因此不能简单地在其上书写注释——并且该缺口被记录为可修复，而非不可避免。两个捐赠者标识被命名而不是修复，并且这里没有引入它们：[StrictCat@{u u0 u1 u2 u3}] 在 [Category@{u u0 u0}] 声明，因此它识别其自身的 hom 和 proof 宇宙；而 [Coq@{u u0 u1 u2}] 在其自己的块中包含 [u0 = u1] 和 [u0 = u2]。这是两个环境类别自身声明中唯一的宇宙等式——这是关于这两个常量的声明，而不是关于整个传递闭包的声明，传递闭包并未被扫过。没有一个被声称是不可避免的。VI. 审计。68 个常量，在全局上下文下全部封闭（[Print Module] 列出了 68 个，并且文件未声明 [Record]、[Class] 或 [Inductive]，因此没有未列出的 [Build_*]；每一个都是通过完全限定名称查询的，这就是为什么 25 个 [Program] 义务 [.glob] 扫描无法看到；源代码中声明了 43 个名称，43 + 25 = 68）。在树中，68 个名称中没有一个发生冲突——一次扫描发现了一个，并且它是活跃的：[Objects] 是 Solver/Expr.v 的具象化类，这就是为什么函子带有 [StrictCat_] 前缀（项目 II）。三根 [Fail] 探针，分为两种类型在词汇上分开——第 §5 节的两个 CONVERSION，第 §8 节的一个 FORMABILITY——每根探针剥离一次，并读取整条错误信息，旁边进行仪器检查和十二个阳性对照——第 §8 节的九个 [Check]，以及第 §5 节阴性结果旁边的三个通过 [Example]。该项目的早期修订版统计了五根探针（三个 formability）和十个对照（七个 [Check]）；PR “代数载体是集合”（2026-09-17）将第 §8 节的两个 [Set] 阴性结果转为对照，这就是两个差异的来源。三段局部 [Constraint] 声明中的每一段都经过删除测试，并且它们的行为不同——一个惰性，一个承重，一个赋予意义；§8 记录了哪一个是哪一个，因为假设 [Constraint] 在工作中的读者在这里三分之一的时间都是错的。在未填充的分母上进行模拟重命名 6/6（常量使用 NEGATIVE 名称，文件局部的通过定义点方法，因为整个文件的重命名是无操作），它们中的每一个都在非 [Fail] 行打破文件。那次测试发现了一个空的保护：[DiscreteCat_Functor] 仅在其自身的 [Fail] 内命名，因此捐赠者的重命名会静默地将该探测变为绿色；关闭它的控制存在正是出于这个原因。现在这个文件中这个风险已经无关紧要——因为捐赠者的注释表明所讨论的探针确实是 [Check]——但控制项仍然保留，因为重新命名会直接破坏文件，这是更强的保障。

 VII. 未交付内容。

 没有 [StrictCat_Indisc]，也没有 [StrictCat_Objects ⊣ StrictCat_Indisc]：
 这是右翼部分，本文件仅通过修复这两个类别，并在第7节证明不连续对象映射也不能指向 [Sets] 来使其成为可能。特别是，这里没有任何内容声称右伴随存在。

 没有 [Components ⊣ StrictCat_Disc]，也没有 [Coq] 值的 π₀：
 第II项说明了为什么 [Pi0] 不能被重复使用，并同样记录了对于构建方式不同的 π₀，没有证明任何不可能性。无法与 Theory/Connected/Components.v 的 [ObjSetoid] 进行比较，它是 [Sets] 值对象映射：§7 显示 [Sets] 值的 STRING 不可用，但此处没有说明函子 [StrictCat ⟶ Sets]（它确实存在）或将其与此相关联。对于任一伴随没有唯一性声明；在 [A] 或 [C] 中 [disc_adj_iso] 没有超出 [Build_Adjunction'] 两个条款的自然性；在伴随的任一侧都没有幺半群或余幺半群，因此关于幂等性也没有任何内容；没有说明 [StrictCat_Disc] 是反射或共反射嵌入；没有关于极限的保持、反射或创建；除了第 §9 节对忠实性的反驳之外，[StrictCat_Objects] 没有 [Full] 或 [Faithful]；[StrictCat] 与任何事物之间没有等价；并且没有根据第 §5 节，对已封装伴随进行带注释的（[Set] 无内部宇宙）重述。
*)

(* * ** §1. The discrete extension, with its universes written out / * ** §1. 离散扩展，其宇宙已被写出 *)

(*
 A function [f : A → obj[C]] extends to a functor out of the discrete
 category on [A]: an object goes to its image, and the only morphism of
 a discrete hom-set -- an equality proof -- goes to the identity,
 transported along that proof.

 This is Instance/Discrete.v's [DiscreteCat_Functor] with the
 universe binders written out and the setoid [rewrite] avoided.  BOTH
 changes were load-bearing and were measured separately.  Written
 without the binders, minimization pins the source at
 [DiscreteCat@{o Set Set}] -- which WAS the donor's actual signature,
 and the pin §8 used to exhibit.  And discharging the [fmap_comp]
 branch with [now rewrite id_left] instead of [symmetry; apply
 id_left] drags [Morphisms] universes in that no annotation can bind
 (the elaborator reports an unbound universe, and adding further
 binders only renames it).

 TWO RECORDED CORRECTIONS.  First, the donor is no longer written
 without binders: it was annotated in place in the PR “algebraic
 carriers are sets” (2026-09-17), so [disc_ext] is now a SECOND
 [Set]-free extension rather than the only one, and §8 checks the two
 against each other instead of separating them.  Second, an earlier
 revision of this paragraph ended “A [Program Definition] cannot be
 annotated here at all, since its obligations mint fresh universes;
 hence the [refine].”  That is FALSE as stated and the annotated donor
 is the counterexample: a [Program Definition] takes binders like any
 other, and a trailing [+] in the binder list allows exactly the fresh
 universes its obligations mint.  What [refine] buys is narrower and is
 still true -- it mints NO auxiliary universe, so [disc_ext@{o h p q}]
 needs no [+] where [DiscreteCat_Functor@{o h p uo uh up +}] does. 

 --------
 一个函数 [f : A → obj[C] ] 可以扩展为从 [A] 上的离散范畴出去的函子：一个对象映射到它的像，而离散 Hom 集合中的唯一态射——一个等式证明——映射到沿该证明传递的恒等态射。

 这是 Instance/Discrete.v 中的 [DiscreteCat_Functor]，其中宇宙绑定器已写出，并避免使用集合等价 [rewrite]。两种更改都是承载性的，并分别进行了测量。没有绑定器的写法中，最小化将源固定在 [DiscreteCat@{o Set Set}] ——那是捐赠者的实际签名，并且固定 §8 用来展示它。而使用 [now rewrite id_left] 代替 [symmetry; apply id_left] 来处理 [fmap_comp] 分支，会拖入 [Morphisms] 宇宙，使得没有注解能够绑定它（展开器报告了一个未绑定的宇宙，添加更多绑定器只是重命名它）。两个已记录的更正。首先，捐赠者不再写成没有绑定器的形式：它已在 PR “代数载体是集合”（2026-09-17）中进行了注释，因此 [disc_ext] 现在是第二个 [Set] -自由扩展，而不是唯一的一个，并且第8节将两者相互比对，而不是将它们分开。其次，本段的早期修订版本以“一个 [Program Definition] 在这里根本不能被注释，因为它的义务会生成新的宇宙；因此 [refine] ”结尾。这种说法是错误的，注释过的捐赠者就是反例：一个 [Program Definition] 像其他任何一个一样接受绑定器，并且绑定器列表中尾随的 [+] 刚好允许它的义务生成新的宇宙。[refine] 购买的东西更狭窄，并且仍然是真的——它不会铸造辅助宇宙，所以 [disc_ext@{o h p q}] 不需要 [+]，然而 [DiscreteCat_Functor@{o h p uo uh up +}] 需要。
*)
Definition disc_ext@{o h p q} {A : Type@{o}} {C : Category@{q h p}}
  (f : A → obj[C]) : DiscreteCat@{o h p} A ⟶ C.
Proof.
  unshelve refine (@Build_Functor (DiscreteCat@{o h p} A) C f
                    (fun x y (e : x = y) =>
                       match e in _ = z return f x ~{C}~> f z with
                       | eq_refl => id end) _ _ _).
  - intros x y e1 e2 He. destruct He. reflexivity.
  - intros x. reflexivity.
  - intros x y z g e. destruct g, e. simpl. symmetry; apply id_left.
Defined.

(** ** §2. The objects functor / ** §2. 对象函子 *)

(*
 [obj[-]] on objects and [fobj[-]] on arrows.  All three functor laws
 are discharged by the ambient obligation tactic, and there is a reason
 rather than an accident behind that: [fmap_respects] is the FIRST
 PROJECTION of [Functor_StrictEq_Setoid]'s pair, whose first component
 [eq_on_obj] IS the required pointwise Leibniz equality of object maps
 (§6's [objects_respects_StrictCat] writes that projection out as a
 [:=] with no tactic), and the identity and composition laws ask only
 for [∀ x, x = x] on the underlying object maps. 

 --------
 [obj[-] 在对象上，[fobj[-] 在箭头上。所有三条函子定律都由环境义务策略解决，这背后有原因而非偶然：[fmap_respects] 是 [Functor_StrictEq_Setoid] 对的第一个投影，其第一个分量 [eq_on_obj] 是所需的逐点莱布尼茨等式的对象映射（第6节的 [objects_respects_StrictCat] 将该投影写为一个 [:=] 而没有使用策略），并且恒等与组合定律仅要求 [∀ x, x = x] 在基础对象映射上成立。
*)
Program Definition StrictCat_Objects : StrictCat ⟶ Coq := {|
  fobj := fun C => obj[C];
  fmap := fun _ _ F => fobj[F]
|}.

(** ** §3. The discrete functor / ** §3. 离散函子 *)

(*
 The three obligations are [fmap_respects], [fmap_id] and [fmap_comp],
 each a strict equality of functors between discrete categories: the
 object component is supplied by the hypothesis (respectively by
 [eq_refl]) and the coherence field vanishes once the discrete
 morphism -- an equality proof -- is destructed. 

 --------
 这三个义务是 [fmap_respects]、[fmap_id] 和 [fmap_comp]，每一个都是离散范畴之间函子严格相等：对象分量由假设提供（分别由 [eq_refl] 提供），一旦离散态射——一个等式证明——被析构，相干场便消失。
*)
Program Definition StrictCat_Disc : Coq ⟶ StrictCat := {|
  fobj := fun A => DiscreteCat A;
  fmap := fun A B (f : A ~{Coq}~> B) => disc_ext (C := DiscreteCat B) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.

(** ** §4. The adjunction / ** §4. 附加 *)

(*
 The transposition.  A functor out of a discrete category IS its object
 map, and that is the whole content: [to] forgets the arrow action and
 [from] is [disc_ext].  Two obligations remain -- that [from] respects
 [≈], and the round trip [from ∘ to ≈ id]; the other round trip and
 the [Proper] certificate for [to] are discharged by the ambient
 tactic, which is already the strict/[≈] split §5 measures. 

 --------
 置换。从离散范畴出的函子就是它的对象映射，这就是全部内容：[to] 忘记箭头作用，而 [from] 是 [disc_ext]。还剩下两个义务——[from] 尊重 [≈]，以及往返 [from ∘ to ≈ id]；其他往返和 [to] 的 [Proper] 证明由环境策略完成，该策略已经是严格/[≈] 分解 §5 的方法。
*)
Program Definition disc_adj_iso (A : obj[Coq]) (C : obj[StrictCat]) :
  @Isomorphism Sets
    {| carrier := @hom StrictCat (StrictCat_Disc A) C
     ; is_setoid := @homset StrictCat (StrictCat_Disc A) C |}
    {| carrier := @hom Coq A (StrictCat_Objects C)
     ; is_setoid := @homset Coq A (StrictCat_Objects C) |} := {|
  to   := {| morphism := fun (F : DiscreteCat A ⟶ C) => fobj[F] |};
  from := {| morphism := fun (f : A → obj[C]) => disc_ext f |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. destruct e.
  unfold Logic.transport, Logic.transport_r, Logic.transport; simpl.
  symmetry; exact (@fmap_id _ _ x a).
Defined.

(*
 Mac Lane's middle adjunction.  Both naturality clauses close by
 [reflexivity]: [Build_Adjunction'] states them for the FORWARD
 transpose, which lands in [Coq], where [≈] is pointwise [=] and where
 forgetting the arrow action of a composite is forgetting it twice. 

 --------
 Mac Lane 的中间伴随。两个自然性条款通过关闭
 [reflexivity] :  [Build_Adjunction'] 为正向伴随转置进行了说明，这到达了 [Coq] ，其中 [≈] 在点上是 [=]，并且在复合的箭头作用上忘记一次就是忘记两次。
*)
Definition Disc_Objects_Adjunction : StrictCat_Disc ⊣ StrictCat_Objects.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact disc_adj_iso.
  - intros A B C f g. reflexivity.
  - intros A B C f g. reflexivity.
Defined.

(** ** §5. Strengths, strict first / ** §5. 优势，先严格 *)

Example objects_obj (C : obj[StrictCat]) :
  fobj[StrictCat_Objects] C = obj[C] := eq_refl.

Example objects_map (C D : obj[StrictCat]) (F : C ~{StrictCat}~> D)
  (x : C) : fmap[StrictCat_Objects] F x = F x := eq_refl.

Example disc_on_obj (A : obj[Coq]) :
  fobj[StrictCat_Disc] A = DiscreteCat A := eq_refl.

Example disc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Disc] f] x = f x := eq_refl.

Example adj_to_forgets (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  to (disc_adj_iso A C) F = fobj[F] := eq_refl.

Example adj_from_extends (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) (x : A) :
  fobj[from (disc_adj_iso A C) f] x = f x := eq_refl.

Example adj_to_from (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) :
  to (disc_adj_iso A C) (from (disc_adj_iso A C) f) = f := eq_refl.

(*
 The unit is the IDENTITY FUNCTION, not merely a natural isomorphism:
 the transpose of [id] at [StrictCat_Disc A] is [fobj[Id]], which is
 [fun x => x] on the nose.  The counit is the identity on objects, and
 cannot be the identity functor, for the same reason
 Adjunction/Diagonal/Finite.v
 records for the diagonal: [counit] at [C] is a functor
 [StrictCat_Disc (StrictCat_Objects C) ⟶ C] between two DIFFERENT
 categories. 

 --------
 单位是恒等函子，而不仅仅是自然同构：在 [StrictCat_Disc A] 上 [id] 的转置是 [fobj[Id]，其在本质上就是 [fun x => x]。余单位在对象上是恒等的，但不能是恒等函子，原因与 Adjunction/Diagonal/Finite.v 对角线记录的相同：在 [C] 上 [counit] 是两个不同范畴之间的函子 [StrictCat_Disc (StrictCat_Objects C) ⟶ C]。
*)
Example unit_is_id (A : obj[Coq]) (a : A) :
  @unit _ _ _ _ Disc_Objects_Adjunction A a = a := eq_refl.

Example counit_obj (C : obj[StrictCat])
  (x : StrictCat_Disc (StrictCat_Objects C)) :
  fobj[@counit _ _ _ _ Disc_Objects_Adjunction C] x = x := eq_refl.

(*
 THE ONE [≈]-ONLY STEP, REFUTED AT [eq_refl] AND THEN LOCALIZED.  The
 two probes below sit either side of a passing control, so the cause is
 read off rather than guessed: the OBJECT map returns on the nose, the
 ARROW map does not, and the residue is exactly [fmap_id]. 

 --------
 唯一 [≈]——唯一步骤，在 [eq_refl] 被驳回，然后被本地化。下面的两个探针分别位于一个经过的控制的两侧，因此原因是直接读取而不是猜测：OBJECT 地图准确返回，ARROW 地图没有返回，而残余正好是 [fmap_id]。
*)
Fail Example adj_from_to_strict (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) = F := eq_refl.

Example adj_from_to_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) ≈ F.
Proof. exact (iso_from_to (disc_adj_iso A C) F). Qed.

Example roundtrip_obj (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fobj[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] x = fobj[F] x
  := eq_refl.

Fail Example roundtrip_map (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    = fmap[F] (eq_refl : x = x) := eq_refl.

Example roundtrip_map_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    ≈ fmap[F] (eq_refl : x = x).
Proof. symmetry; exact (@fmap_id _ _ F x). Qed.

(*
 [StrictCat_Disc] is fully faithful, which is what “the unit is the identity”
 says categorically.  Faithfulness costs NOTHING -- the ambient tactic
 discharges it, since injectivity of [fmap[StrictCat_Disc]] is the first
 projection of a strict functor equality.  Fullness costs exactly the
 round trip above, i.e. exactly one [fmap_id]. 

 --------
 [StrictCat_Disc] 是完全忠实的，这正是“单位是恒等映射”在范畴论上的意思。忠实性不花费任何代价——环境策略会处理它，因为 [fmap[StrictCat_Disc] 的单射性是严格函子等式的第一个投影。丰满性正好需要上面提到的来回过程，即恰好一个 [fmap_id]。
*)
#[export] Program Instance Disc_Faithful : Faithful StrictCat_Disc.

#[export] Program Instance Disc_Full : Full StrictCat_Disc := {|
  prefmap := fun A B (G : StrictCat_Disc A ~{StrictCat}~> StrictCat_Disc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_from_to (disc_adj_iso x (StrictCat_Disc y)) g).
Defined.

(* * ** §6. Why the source is [StrictCat] and not [Cat] / * ** §6. 为什么源是 [StrictCat] 而不是 [Cat] *)

(*
 [ObjRespectsCat] is exactly the [fmap_respects] obligation that ANY
 objects functor owes, at either candidate target: both [Coq]'s
 hom-setoid and [ObjSetoid]'s [equiv] are Leibniz equality of objects,
 so respecting [≈] means carrying [≈]-equal functors to POINTWISE
 LEIBNIZ-EQUAL object maps. 

 --------
 [ObjRespectsCat] 正是任何对象函子在任一候选目标上所应承担的 [fmap_respects] 义务：[Coq] 的同态集合和 [ObjSetoid] 的 [equiv] 都是对象的莱布尼茨等同性，因此尊重 [≈] 意味着将 [≈] 等同的函子映射到逐点莱布尼茨等同的对象映射。
*)
Definition ObjRespectsCat : Type :=
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset Cat C D) F G → ∀ x : C, F x = G x.

(* Over [StrictCat] it is the FIRST PROJECTION of the hom-setoid: a [:=] with no tactic. / 超过 [StrictCat] 它是同值类集的第一次投影：一个 [:=] 没有策略。 *)
Definition objects_respects_StrictCat :
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset StrictCat C D) F G → ∀ x : C, F x = G x :=
  fun C D F G H => `1 H.

Lemma indiscrete_hom_eq (a b : Datatypes.unit) : a = b.
Proof. now destruct a, b. Qed.

(*
 The witness.  In [Indiscrete bool] every hom-set is [unit], so the
 negation endofunctor is naturally isomorphic to the identity -- the
 component at each object is [tt], invertible by [tt] -- while its
 object map differs from the identity's at [true]. 

 --------
 证人。在 [Indiscrete bool] 中，每个同态集都是 [unit]，因此否定自函子自然同构于恒等函子——在每个对象处的分量是 [tt]，可由 [tt] 逆转——然而其对象映射在 [true] 处不同于恒等映射。
*)
Program Definition SwapI : Indiscrete bool ⟶ Indiscrete bool := {|
  fobj := negb;
  fmap := fun _ _ _ => tt
|}.

Lemma swap_iso_in_Cat :
  @equiv _ (@homset Cat (Indiscrete bool) (Indiscrete bool))
         (Id[Indiscrete bool]) SwapI.
Proof.
  unshelve eexists.
  - intro x. unshelve eexists; simpl; try exact tt; apply indiscrete_hom_eq.
  - intros x y f; simpl; apply indiscrete_hom_eq.
Qed.

(*
 Hence there is no objects functor over [Cat] INTO A TARGET WHOSE
 MORPHISM [≈] IS POINTWISE LEIBNIZ EQUALITY OF OBJECTS -- [Coq], or
 [Sets] at [ObjSetoid] -- and not merely that this one construction
 fails there.  The qualifier is necessary and is not a hedge: an
 objects functor [Cat ⟶ Sets] over the ISOMORPHISM setoid exists, with
 [fmap_respects] discharged by [fobj_iso].  That is the alternative
 issue #357 item 1 itself offers, and it is excluded here by the
 exercise's request for the strict version, NOT by this theorem. 

 --------
 因此不存在一个对象函子在  [Cat]  上到一个目标，其中的态射  [≈]  是对象的逐点莱布尼茨等式 -- [Coq]，或者 [Sets] 在 [ObjSetoid] --，而不仅仅是说这一个构造在那里失败。这个限定词是必要的，并不是一种保留：在同构类型集上存在一个对象函子 [Cat ⟶ Sets]，并且 [fmap_respects] 被 [fobj_iso] 解决。这就是替代问题 #357 项目 1 本身提出的，并且它在这里被排除，是因为练习要求严格版本，而不是因为这个定理。
*)
Theorem objects_not_functorial_over_Cat : ObjRespectsCat → False.
Proof.
  intro K.
  exact (eq_ind true (fun b : bool => if b then True else False) I false
           (K _ _ (Id[Indiscrete bool]) SwapI swap_iso_in_Cat true)).
Qed.

(* * ** §7. Why the target is [Coq] and not [Sets] / * ** §7. 为什么目标是 [Coq] 而不是 [Sets] *)

(*
 The mirror-image refutation.  It is stated for an ARBITRARY object map
 [K : obj[Sets] → obj[StrictCat]] rather than for [StrictCat_Disc], because it
 has to be binding on the right-hand wing too: the two instantiations
 at the end of this section are the discrete and the INDISCRETE object
 maps, and both are refuted by the same theorem.

 The hypotheses are the least that make [K] deserve the name: it is
 POINTED (each object of [K A] is named by a point of [A]), that naming
 is INJECTIVE, and it is NATURAL (the arrow action carries the name of
 [x] to the name of [f x]).  Both [DiscreteCat ∘ carrier] and
 [Indiscrete ∘ carrier] satisfy all three with [Kpt] the identity. 

 --------
 镜像反驳。它是针对任意对象映射 [K : obj[Sets] → obj [StrictCat]] 而不是 [StrictCat_Disc] 陈述的，因为它也必须在右翼上具有约束力：本节末的两个实例化分别是离散和非离散对象映射，并且它们都被同一个定理所反驳。

 这些假设是使 [K] 值得命名的最小条件：它是有指向的（[K A] 的每个对象都由 [A] 的一个点命名），这种命名是单射，并且它是自然的（箭头操作将 [x] 的名称带到 [f x] 的名称）。[DiscreteCat ∘ carrier] 和 [Indiscrete ∘ carrier] 都满足这三个条件，[Kpt] 是恒等映射。
*)
Definition PointedObjectMap
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A]) : Type :=
  (∀ (A : obj[Sets]) (x y : carrier A), Kpt A x = Kpt A y → x = y)
    * (∀ (A B : obj[Sets]) (f : A ~{Sets}~> B) (x : carrier A),
         fobj[Kmap A B f] (Kpt A x) = Kpt B (f x)).

(*
 The separating object: [bool] under the everywhere-true setoid.  Two
 constant maps out of it are [≈] without being pointwise equal, which
 is precisely what a [Sets]-morphism may do and a [StrictCat]-morphism
 may not. 

 --------
 分离对象：在处处成立的集合等价关系下的 [bool]。两个从它出发的常数映射是 [≈]，但它们在每一点上并不相等，这正是 [Sets]-态射可以做而 [StrictCat]-态射不允许的。
*)
Program Definition BlurBool : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition kTrue : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => true |}.

Program Definition kFalse : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => false |}.

Lemma k_equiv : kTrue ≈ kFalse.
Proof. intro x; exact I. Qed.

Theorem no_carrier_functor_Sets_StrictCat
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A])
  (HK : PointedObjectMap K Kmap Kpt)
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat (K A) (K B)) (Kmap A B f) (Kmap A B g))
  : False.
Proof.
  destruct HK as [Kinj Kobj].
  pose proof (`1 (Kresp _ _ kTrue kFalse k_equiv) (Kpt BlurBool true)) as H.
  rewrite (Kobj BlurBool BlurBool kTrue true) in H.
  rewrite (Kobj BlurBool BlurBool kFalse true) in H.
  apply Kinj in H.
  discriminate.
Qed.

(*
 Instantiation 1: the DISCRETE object map on carriers, i.e. §3's
 [StrictCat_Disc] re-aimed at [Sets].  It is refuted. 

 --------
 实例化 1：承载体上的离散对象映射，即第 §3 节的 [StrictCat_Disc] 重新指向 [Sets]。它被驳斥了。
*)
Definition disc_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  DiscreteCat (carrier A) ~{StrictCat}~> DiscreteCat (carrier B) :=
  disc_ext (C := DiscreteCat (carrier B)) f.

Definition disc_carrier_pointed :
  PointedObjectMap (fun A => DiscreteCat (carrier A)) disc_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem disc_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (disc_carrier_Kmap A B f) (disc_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ disc_carrier_pointed Kresp).
Qed.

(*
 Instantiation 2: the INDISCRETE object map on carriers -- the right
 adjoint of the right-hand wing, re-aimed at [Sets].  It is refuted by
 the SAME theorem, which is why §7 is stated generally.  This is the
 sense in which the codomain decision is binding on that module. 

 --------
 实例化 2：载体上的非连续对象映射——右侧的右伴随，被重新指向 [Sets]。它被相同的定理所驳斥，这也是为什么第 7 节以一般形式陈述的原因。这就是值域决定对该模块具有约束力的意义。
*)
Program Definition ind_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  Indiscrete (carrier A) ~{StrictCat}~> Indiscrete (carrier B) := {|
  fobj := f;
  fmap := fun _ _ _ => tt
|}.

Definition ind_carrier_pointed :
  PointedObjectMap (fun A => Indiscrete (carrier A)) ind_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem ind_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (ind_carrier_Kmap A B f) (ind_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ ind_carrier_pointed Kresp).
Qed.

(** ** §8. The universe boundary / ** §8. 宇宙边界 *)

(*
 Instrument check: [Fail] is live in this file.  Every negative below
 and in §5 was additionally stripped once and its failure kind read off
 the whole error message -- two CONVERSION failures in §5 (reporting
 “cannot unify”, with no universe clause) and one FORMABILITY refusal
 here (reporting “universe inconsistency: Cannot enforce ...”).
 The two kinds are kept lexically apart.

 RECORDED CORRECTION.  An earlier revision counted THREE formability
 refusals here: the [StrictCat] donor identification of the section
 after next, plus two [Set] pins in [Section SetPin].  The two [Set]
 pins are gone -- see that section -- so the count is now one. 

 --------
 仪器检查：[Fail] 在此文件中处于活动状态。以下所有负面情况以及 §5 中的情况都额外剥离了一次，并且其失败类型从整个错误信息中读取——§5 中有两个 CONVERSION 失败（报告“无法统一”，没有宇宙子句）以及这里有一个 FORMABILITY 拒绝（报告“宇宙不一致：无法强制执行...”）。这两种类型在词汇上保持分开。

 已记录的修正。早期版本统计此处有三个可形成性拒绝：[StrictCat] 捐献者识别的是下下一节，以及 [Set] 在 [Section SetPin] 中的两个销钉。两个 [Set] 销钉已经消失——参见该节——所以现在计数为一个。
*)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
 Section-local [Universes]/[Constraint] declarations do not leak; the
 Instance/Fun/Group.v precedent applies, so these probes live in the
 library file beside the constants they guard rather than in [Test/].

 FIRST: item I.3's [Set] pin -- now REPAIRED, and this section is the
 record of the repair.

 RECORDED CORRECTION.  An earlier revision stated this section as two
 FORMABILITY NEGATIVES: over a category whose homs are declared
 strictly above [Set], ascribing [DiscreteCat_Functor f] to
 [DiscreteCat@{uo uh uh} A ⟶ C] and ascribing [Indiscrete] to
 [Type@{uo} → Category@{uo uh uh}] were both refused, each reading
 “universe inconsistency: Cannot enforce Set = uh”, because both donors
 were declared with bare binders and minimization pinned their hom and
 proof levels to [Set].  The comment added that the [Constraint] below
 was INERT for those two negatives, since what they fired on was the
 donors' literal [Set] meeting the rigid declared level [uh].

 In the PR “algebraic carriers are sets” (2026-09-17) both donors were
 annotated in place -- [DiscreteCat_Functor@{o h p uo uh up +}] at
 Instance/Discrete.v and [Indiscrete@{o h p}] at
 Instance/Discrete/Reconstruct.v -- so both ascriptions are now
 ACCEPTED and both lines below are positive controls.  The [Constraint]
 remains inert, and is kept for the reason it was kept before: it
 states the intended reading, and the whole section is only interesting
 above [Set].

 What this section still guards is therefore not a refusal but an
 AGREEMENT: the two annotated donors and the hand-written [disc_ext]
 reach the same declared levels, so the tree now has three
 interchangeable discrete extensions rather than one usable one and two
 pinned ones.  [disc_ext] is retained because it is written with
 [refine] rather than [Program] and so mints no auxiliary universe;
 §1's paragraph on that difference stands.

 Contrast the section after next, where the analogous [Constraint] IS
 load-bearing and the negative is real: deleting the [Constraint] makes
 that negative succeed and the file stops compiling. 

 --------
 部分本地 [Universes] / [Constraint] 声明不会泄漏；Instance/Fun/Group.v 的先例适用，因此这些探针与它们保护的常量一起存在于库文件中，而不是存在于 [Test/] 中。

 首先：I.3 项的 [Set] 引脚——现已修复，本节是修复记录。已记录更正。早期的修订将本节说明为两个可成形性否定：针对其同构体被严格声明在 [Set] 上方的类别，将 [DiscreteCat_Functor f] 分配给 [DiscreteCat@{uo uh uh} A ⟶ C]，以及将 [Indiscrete] 分配给 [Type@{uo} → Category@{uo uh uh}] 都被拒绝，每个都显示“宇宙不一致：无法强制 Set = uh”，因为两个供体均以裸绑定器声明，并且最小化将它们的同构体和证明级别固定在 [Set]。评论补充说，下方的 [Constraint] 对这两个否定是惰性的，因为它们触发的是供体的字面 [Set]，满足刚性声明级别 [uh]。在 PR “代数载体是集合”（2026-09-17）中，两个捐赠者都在原位进行了注释——[DiscreteCat_Functor@{o h p uo uh up +}] 位于 Instance/Discrete.v，[Indiscrete@{o h p}] 位于 Instance/Discrete/Reconstruct.v——所以两个标注现在都被接受，并且下面的两行都是阳性对照。[Constraint] 保持不变，并保留了之前保留它的原因：它说明了预期的读取方式，并且整节内容仅在 [Set] 之上才有趣。因此，本节仍然保护的不是拒绝，而是一种协议：两个带注释的捐赠者和手写的 [disc_ext] 达到了相同的声明级别，因此该树现在有三个可互换的离散扩展，而不是一个可用的和两个固定的。[disc_ext] 被保留，因为它是用 [refine] 而不是 [Program] 写的，因此不会创建辅助宇宙；第1节关于该差异的段落仍然有效。

 对比下一节，其中类似的 [Constraint] 是承重的，而否定是真实的：删除 [Constraint] 会使该否定生效，并且文件停止编译。
*)
Section SetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (A : Type@{uo}) (C : Category@{uo uh uh}) (f : A → obj[C]).

  (*
 controls: the shape and the functor type ARE formable here, and both
 donors ARE nameable. 

 --------
 控制：这里可以形成形状和函子类型，并且两个供体都可以命名。
*)
  Check (DiscreteCat@{uo uh uh} A).
  Check (DiscreteCat@{uo uh uh} A ⟶ C).
  Check (DiscreteCat_Functor f).
  Check (Indiscrete A).

  (* and, since the annotation, both donors also REACH these levels / 并且，自从注释以来，两位供体也都达到了这些水平 *)
  Check (DiscreteCat_Functor f : DiscreteCat@{uo uh uh} A ⟶ C).
  Check (Indiscrete@{uo uh uh} : Type@{uo} → Category@{uo uh uh}).

  (* as does the hand-written extension / 手写扩展也是如此 *)
  Check (disc_ext@{uo uh uh uo} f : DiscreteCat@{uo uh uh} A ⟶ C).
End SetPin.

(*
 SECOND: a DONOR identification, named and not repaired.  An object of
 [StrictCat] has its hom and proof universes identified -- the fourth
 and fifth universe arguments of [StrictCat] are the inner category's
 object and hom-and-proof levels -- so the rejection below reports
 “Cannot enforce cp = ch”.  Here the [Constraint] IS load-bearing:
 without it [cp] unifies with [ch] and the negative succeeds.  What is
 NOT identified is object against hom, which is what the following
 section's control shows, its homs sitting strictly BELOW its
 objects. 

 --------
 第二：一个捐赠者标识，已命名且未修复。[StrictCat] 的一个对象的同态和证明宇宙已被识别——[StrictCat] 的第四和第五个宇宙参数是内层范畴的对象层和同态及证明层——因此下面的拒绝报告“无法强制执行 cp = ch”。这里 [Constraint] 是承重的：没有它，[cp] 会与 [ch] 统一，而负条件会成功。未被识别的是对象与同态，这正是下一节控制所展示的，其同态严格位于其对象之下。
*)
Section StrictCatObjects.
  Universes co ch cp.
  Constraint ch < cp.
  Context (C : Category@{co ch cp}).
  Fail Check (C : obj[StrictCat]).
End StrictCatObjects.

Section StrictCatHomsBelow.
  Universes co ch.
  Constraint ch < co.
  Context (C : Category@{co ch ch}).
  Check (C : obj[StrictCat]).
End StrictCatHomsBelow.

(*
 THIRD, and this is the guard §5 promised: the identification visible
 in [Disc_Objects_Adjunction]'s BINDER is minimization and not content.
 The adjunction TYPE is formable with the inner categories' hom
 universe declared STRICTLY BELOW their object universe -- here the
 two functors run between [Coq@{e f f f}] and [StrictCat@{c f a f b}],
 whose objects are categories with objects at [f] and homs at [b].

 This is also where the comparison with Instance/Top/Forgetful.v
 belongs.  That file's [Discrete ⊣ Forget ⊣ Indiscrete] for [Top] is
 forced into transposition isomorphisms because [Top]'s homs sit
 strictly above its points, so no single [Sets] serves both directions
 and the packaged [Adjunction] record is unformable at every level.
 NO ANALOGUE OF THAT WALL ARISES HERE: the two functors of this file
 run between one [StrictCat] and one [Coq] in both directions, the record
 is built above, and the check below shows it is not even confined to
 a degenerate universe assignment.

 The [Constraint] here is neither inert nor load-bearing in the sense
 of the two sections above: the [Check] passes with or without it, and
 what the declaration buys is the CONTENT of the control -- without it
 the levels could collapse and the command would demonstrate nothing.
 Stated so that a later reader does not delete it as redundant. 

 --------
 第三，这就是 §5 所承诺的守护：在 [Disc_Objects_Adjunction] 的 BINDER 中可见的标识是最小化而非内容。附加的类型可以通过内部范畴的同态宇宙严格在其对象宇宙以下声明来形成——这里两个函子在 [Coq@{e f f f}] 和 [StrictCat@{c f a f b}] 之间运行，其对象是对象位于 [f]、同态位于 [b] 的范畴。这也是与 Instance/Top/Forgetful.v 比较的地方。该文件中 [Discrete ⊣ Forget ⊣ Indiscrete] 对 [Top] 的处理被迫进入置换同构，因为 [Top] 的同态严格位于其点之上，因此没有单一的 [Sets] 能够同时处理两个方向，并且打包的 [Adjunction] 记录在每一级都是不可形成的。在这里不会出现那种障碍：该文件的两个函子在两个方向上在一个 [StrictCat] 与一个 [Coq] 之间运行，记录是在上方构建的，并且下面的检查显示它甚至不局限于一个退化的宇宙分配。这里的 [Constraint] 既非惰性，也非承重，就上述两个部分的意义而言：无论是否有 [Check]，它都能通过，而声明所购买的是控制的内容——没有它，层级可能会崩溃，命令将无法展示任何内容。如此表述，以便后来的读者不会把它删除为多余内容。
*)
Section AdjunctionUniversesSeparated.
  Universes a b c e f.
  Constraint b < f.
  Check (StrictCat_Disc@{a b c f e f} ⊣ StrictCat_Objects@{a c f e f b}).
End AdjunctionUniversesSeparated.

(* * ** §9. The objects functor genuinely forgets / * ** §9. 对象函子真正地遗忘 *)

(*
 Sharpness for [StrictCat_Objects], proved rather than asserted: it is NOT
 faithful.  The witness is the delooping of the two-element xor monoid
 -- one object, [bool] as its hom-set, [false] as the identity -- which
 carries exactly two endomorphisms as a monoid, the identity and the
 constant.  Both are functors, both have the SAME object map (there is
 only one object), and they differ at the arrow [true]. 

 --------
 [StrictCat_Objects] 的尖锐性，已经被证明而非断言：它不是忠实的。证据是二元 xor 幺半群的 delooping —— 一个对象，[bool] 作为它的同态集合，[false] 作为恒等映射 —— 该单体恰好有两个自同态，恒等映射和常量映射。两者都是函子，且具有相同的对象映射（只有一个对象），而它们在箭头 [true] 上有所不同。
*)
#[local] Ltac bool_cases :=
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  reflexivity.

Program Definition BoolMon : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := @eq bool |};
  id      := fun _ => false;
  compose := fun _ _ _ f g => xorb f g
|}.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.

Program Definition ZeroF : BoolMon ⟶ BoolMon := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => false
|}.

(*
 [poly_unit] has decidable equality, so Hedberg applies and the
 transport in [Functor_StrictEq_Setoid]'s coherence field can be
 eliminated; the argument is axiom-free. 

 --------
 [poly_unit] 具有可判定的等式，因此 Hedberg 定理适用，并且可以消除 [Functor_StrictEq_Setoid] 的相干场中的传递；这个论证是无公理的。
*)
Lemma poly_unit_uip (p : @eq poly_unit ttt ttt) : p = eq_refl.
Proof.
  apply (Eqdep_dec.UIP_dec (fun x y : poly_unit => left
    (match x, y with ttt, ttt => eq_refl end))).
Qed.

Lemma Id_neq_ZeroF :
  @equiv _ (@homset StrictCat BoolMon BoolMon) (Id[BoolMon]) ZeroF → False.
Proof.
  intros [eo co].
  pose proof (co ttt ttt true) as H.
  rewrite (poly_unit_uip (eo ttt)) in H.
  simpl in H. discriminate.
Qed.

Example objects_merges :
  fmap[StrictCat_Objects] (Id[BoolMon]) ≈ fmap[StrictCat_Objects] ZeroF.
Proof. intro x; reflexivity. Qed.

Theorem Objects_not_Faithful : Faithful StrictCat_Objects → False.
Proof.
  intro F. exact (Id_neq_ZeroF (fmap_inj _ _ objects_merges)).
Qed.
