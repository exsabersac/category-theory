Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

(* * * Adjoints of the slice and coslice projections / * * 切片和余切片投影的伴随 *)

(*
 Reference: Saunders Mac Lane, "Categories for the Working
 Mathematician", 2nd ed., §IV.2, book p. 90, Exercise 11
 [maclane:IV.2:ex11]: if C has finite coproducts, the
 projection out of the coslice under an object a has a LEFT
 adjoint, sending c to the coproduct injection a ~> a + c,
 with the copairing as the transposition and the right
 injection as the unit.
 Reference: Steve Awodey, "Category Theory", 2nd ed., §9.9, Exercise 6
 (starred), printed p. 262 [awodey:9:ex6]: the slice-side
 dual.  The domain functor out of C/a has a RIGHT adjoint,
 sending y to the projection y × a ~> a; the starred half
 asks when it also has a LEFT one.
 nLab:      https://ncatlab.org/nlab/show/under+category
 nLab:      https://ncatlab.org/nlab/show/over+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Both exercises are one construction seen twice.  A morphism out of a
 coproduct is a pair of clauses, one per summand
 (Structure/Cocartesian.v's header says exactly this of [merge]); a
 morphism into a product is a pair of components.  An object of the
 coslice under a is an object x with a chosen arrow a ~> x, and the
 free way to produce one from a bare c is to adjoin a: take a + c with
 its left injection.  A coslice arrow out of that object is then a
 clause on a -- pinned by the coslice condition to be the target's own
 structure map -- plus a FREE clause on c, which is exactly an
 unconstrained arrow c ~> x.  That is the bijection, and every line
 below is bookkeeping around it.  Dually a slice arrow into y × a with
 the second projection as structure map is a free first component plus
 a second component pinned to the source's structure map.

 ** File placement: a departure from the issue's suggestion

 The issue suggests [Construction/Slice/Coslice.v] "(or an extension of
 Construction/Slice.v)".  This file is [Construction/Slice/Adjunction.v]
 instead, because it carries BOTH the coslice adjunction (Block A) and
 its slice dual (Block B) -- built directly, not transported -- plus the
 two settle results of Block C and the [Sets] witnesses of Block D.
 "Coslice.v" would misname more than half its content.  Extending
 Construction/Slice.v in place was also declined: that file is required
 by Construction/Comma/Special.v, Construction/Slice/Pullback.v,
 Construction/Slice/Terminal.v, Instance/Cat/Pullback.v and others, and
 the material below drags in Structure/Cartesian.v,
 Structure/Cocartesian.v, Structure/Terminal.v, Structure/Initial.v,
 Theory/Adjunction.v and three Instance/Sets modules, which would land
 on every one of them.  The module closure here is 31 (measured with
 coqdep).

 ** What is delivered, and at what strength

 Block A, over [{C} {CC : @Cocartesian C} (a : C)]:

 - [Coslice_Proj a : Coslice C a ⟶ C], the projection, as a
 three-line record whose object and arrow actions are the literal
 first projections and hence reduce.
 - [Coslice_Coprod a : C ⟶ Coslice C a], sending c to
 [(a + c; inl)] and f to [right f].  READ THE OBJECT PRECISELY: the
 coslice structure map of the value is [inl : a ~> a + c] -- the
 injection Mac Lane's own sentence names -- while the UNIT below is
 [inr : c ~> a + c], the right injection.  The exercise's arrow
 reading "id + f" is [cover id f], and [coslice_fmap_is_cover]
 records that the delivered [right f] is that morphism with the
 redundant [∘ id] removed.
 - **[Coslice_Projection_Adjunction a : Coslice_Coprod a ⊣
 Coslice_Proj a]**, the issue's pinned name, built through
 [Build_Adjunction'] (Theory/Adjunction.v) out of the hom-setoid
 isomorphism [coslice_adj] plus the two forward naturality clauses.
 The transposition is
 [Hom_{a/C}((a + c; inl), (x; g)) ≊ Hom_C(c, x)]: forward
 [(h; _) ↦ h ∘ inr], backward [k ↦ (g ▽ k; _)].  The [to ∘ from]
 round trip is the equation [inr_merge] states and is discharged by
 the default obligation tactic; the [from ∘ to] one is [merge_comp],
 [merge_inl_inr] and [id_right] after rewriting with the condition.
 - [coslice_projection_unit a c : c ~> a + c := inr] and
 [coslice_projection_counit a x := (`2 x ▽ id; _)], with their
 grades against the class-produced [unit]/[counit] measured
 strict-first (see the next section).

 Block B, over [{C} {CA : @Cartesian C} (a : C)], and COVARIANT:

 - [Slice_Proj a : Slice C a ⟶ C], the domain functor.
 - [Slice_Prod a : C ⟶ Slice C a], sending x to [(x × a; exr)] and f
 to [first f]; [slice_fmap_is_split] is the "f × id" reading.
 - **[Slice_Projection_Adjunction a : Slice_Proj a ⊣ Slice_Prod a]**,
 transposition [Hom_C(x, y) ≊ Hom_{C/a}((x; g), (y × a; exr))],
 forward [k ↦ (k △ g; _)], backward [(h; _) ↦ exl ∘ h].
 - [slice_projection_unit a x := (id △ `2 x; _)] and
 [slice_projection_counit a y := exl].

 Block C settles the starred question, in both handednesses and with NO
 (co)product hypothesis anywhere -- the section binds only [{C} (a : C)]:

 - **[slice_proj_left_adjoint_iff_terminal a :
 { L : C ⟶ Slice C a & L ⊣ Slice_Proj a } ↔ IsTerminalObj a]**
 - **[coslice_proj_right_adjoint_iff_initial a :
 { R : C ⟶ Coslice C a & Coslice_Proj a ⊣ R } ↔ IsInitialObj a]**

 Each direction is a separately named lemma, so a consumer projects
 by conversion rather than through the packaged [iffT]:
 [slice_left_adjoint_terminal] / [slice_terminal_left_adjoint] with
 [slice_terminal_left_adjoint_adj], and the initial mirrors.  The
 enabling facts are [slice_id_IsTerminalObj] -- [(a; id)] is terminal
 in [Slice C a] -- and [coslice_id_IsInitialObj], its dual; each has
 one hand-discharged obligation, the UNIQUENESS clause, a unit law
 after rewriting with the competitor's condition, while the sigma's
 own hole closes by the default obligation tactic.  Necessity reads
 the singleton across the adjunction's [Sets]-isomorphism, and
 sufficiency builds the adjoint whose transposition is the identity
 on underlying arrows, so all four naturality clauses close by
 [reflexivity].

 Construction/Slice/Terminal.v's [Slice_Terminal :
 Slice C 1 ≅[Cat] C] is the SPECIAL CASE at a bundled [Terminal].  It
 is cited, not consumed: the object-level [IsTerminalObj] statement is
 what the exercise asks to settle, and routing through the bundled
 class would have required unbundling it again, where the direct
 argument is about fifteen lines.

 Block D exercises all of it over [Sets].

 ** The unit is literally the coproduct injection, and the residue is
 exhibited rather than described

 The issue's reviewer check is that the unit be the coproduct injection.
 [coslice_projection_unit a c] is [inr] with no wrapper at all -- a
 [Definition] whose body is the constant.  What the CLASS produces is
 [⌊id⌋], and the forward transpose post-composes with [inr] while the
 identity of the coslice is carried by [id] of C, so the class value is
 [id ∘ inr].  Both grades are recorded:

 - [coslice_unit_strict], an [Example] closing at [eq_refl]:
 [unit = id ∘ coslice_projection_unit a c].  The residue is stated
 literally, so a later change that removed it would break this line
 rather than pass unnoticed.
 - [coslice_unit_is_inr], the [≈] form, one [id_left] away.

 The strict identity [unit = inr] does NOT hold, and it is pinned as
 CONVERSION negative 7 in Test/ProbeSliceAdjunction365.v.

 The four grades are NOT uniform across the two blocks, and the pattern
 is worth carrying because it is mirror-image:

 - coslice UNIT: residue [id ∘ -], on the LEFT.
 - coslice COUNIT: STRICT on the underlying morphism --
 [coslice_counit_strict] gives [`1 (counit x) = `2 x ▽ id] at
 [eq_refl] -- and [≈] as a coslice arrow by [reflexivity], the
 coslice hom-setoid comparing first projections only.  The WHOLE
 records are not equal, since [coslice_projection_counit] carries
 its own obligation proof.
 - slice UNIT: STRICT on the underlying morphism,
 [`1 (unit x) = id △ `2 x].
 - slice COUNIT: residue [- ∘ id], on the RIGHT
 ([slice_counit_strict]), with [slice_counit_is_exl] the [≈] form,
 one [id_right] away.  Pinned as CONVERSION negative 8.

 The cause of the asymmetry is structural rather than incidental: [⌊id⌋]
 feeds the identity into the FORWARD transpose and [⌈id⌉] into the
 BACKWARD one, and in each block exactly one of the two transposes
 touches its argument by composition.

 ** The slice side is built directly, and the "one Opposite transport
 away" claim is measured

 The issue's work item 4 says the slice statement "is one [Opposite]
 transport away".  That is true up to isomorphism and NOT on the nose,
 and the reviewer check -- no residual [^op] in any delivered type -- is
 what makes the distinction bite.  Unfolding, the opposite of the slice
 over C^op has homs [∃ f, f ∘ `2 x ≈ `2 y] where Construction/Slice.v's
 [Coslice] has [∃ f, `2 y ≈ f ∘ `2 x]: the same equation in the other
 ORIENTATION, hence a different type.  Construction/Slice/Terminal.v
 already records exactly this, as its reason for proving
 [Coslice_Initial] directly rather than transporting [Slice_Terminal].
 Here it is pinned as CONVERSION negative 9, against a control showing
 that the OBJECT types DO agree definitionally, so the obstruction is
 located at the hom equations and not at the encoding at large.

 Accordingly Block B is a direct construction.  The word [Opposite] and
 the token [^op] occur nowhere below, and [Structure/Cocartesian.v]'s
 own [Cocartesian C] notation -- which IS [Cartesian (C^op)] -- is the
 only place duality enters, in Block A, where it is the tree's own
 spelling for having coproducts.

 ** Prior art: three claims in the issue are stale, and one is its own

 (1) The issue's Awodey section says of the slice domain functor that
 "the functor itself does not exist".  It does, twice over.
 Instance/Cat/Pullback.v's [Slice_proj] and [Coslice_proj] are
 this very three-line record, with the same signature [{C} (c)];
 Construction/Slice/Terminal.v's [Slice_Forget] and
 [Coslice_Forget] are its specialisations to a terminal and an initial
 base.  The agreement is MEASURED, in the probe rather than here: both
 DATA fields of [Coslice_Proj]/[Coslice_proj] agree at [eq_refl] in
 both handednesses, while the WHOLE records do not, the three [Functor]
 law fields being each file's own opaque obligations (CONVERSION
 negative 10).  The record is rebuilt rather than imported because
 Instance/Cat/Pullback.v's module closure is 39 and requiring it would
 add 14 modules to this file's 31.

 (2) The same section says "The whole slice development is
 Construction/Slice.v's four definitions plus the two base-change
 functors in Construction/Slice/Pullback.v".  It omits
 Construction/Slice/Terminal.v, twelve declared results including the
 two forgetful functors just named.

 (3) The issue's Mac Lane section says "A search over slice, coslice and
 comma files for [⊣] finds only the commented-out slice base-change
 stub".  The stub was real when that was written; it has since been
 deleted and the theorem proved, as Construction/Slice/Pullback.v's
 [Base_Functor_Adjunction].  Even then,
 Construction/Comma/Adjunction.v carries live [⊣] results throughout,
 among them [Comma_Functor_F_Id_Id_G] and Lawvere's
 biconditional [Adjunction_Comma] -- as the issue's own
 preceding paragraph says.

 (4) What the issue gets exactly right, and what this file therefore
 does not dispute, is the central absence: no functor sending c to the
 injection [a ~> a + c], no adjunction for either projection, and no
 coproduct-injection unit existed anywhere.

 The issue's own suggested route -- transport [comma_proj2]
 (Construction/Comma.v) across [Comma_Coslice]
 (Construction/Slice.v) -- is a THIRD way, and it is measured
 instead of dismissed.  The composite typechecks and is built in the
 probe as [p365_via_comma].  But [Comma_Coslice] is a [Program Instance]
 whose [to] is written [{| fobj := _; fmap := _ |}], so BOTH data fields
 of the comparison functor are obligations: not even the OBJECT action
 of the transport returns [`1 x] on the nose (CONVERSION negative 12),
 where the direct record has it definitionally.  Its [≅[Cat]] strength
 is a second cost, [Cat]'s hom-setoid being natural isomorphism.

 ** Universes: the identification is in the BINDER, not the block

 Every headline constant here -- the four functors, the two adjunctions,
 the two biconditionals -- is over [C : Category@{u u0 u0}], hom
 IDENTIFIED with proof by reuse of one level variable in the BINDER,
 while its constraint block contains NO equation at all: only [<] and
 [<=].  Reading the block alone reports "no identification" and is
 wrong; both must be read.  Measured, flattening whitespace first,
 since [Print] wraps universe instances:

 [Coslice_Proj@{u u0 u1 u2}], and identically [Coslice_Coprod],
 [Slice_Proj], [Slice_Prod]: [u0 < u1] plus five bounds.
 [Coslice_Projection_Adjunction@{u u0 u1 u2 u3}] and
 [Slice_Projection_Adjunction]: [u0 < u2] plus seventeen bounds
 ([Basics.compose], [Logic_lemmas.equality], [Projections],
 [prod_rect], [projections], [ID]).
 [slice_proj_left_adjoint_iff_terminal@{u u0 u1 u2 u3 u4 u5}] and
 [coslice_proj_right_adjoint_iff_initial]: [u0 < u1] plus twenty
 bounds.

 What stays FREE is the OBJECT universe: [u] occurs in no equation, only
 in bounds, in every one of the eight.  And no [Set] occurs in any
 binder or block, in the general results OR in the [Sets] witnesses --
 which is why Block D builds its two-element object as the coproduct
 [1 + 1] in [Sets] rather than at [bool].

 The hom-is-proof identification is INHERITED, and FIVE donors each
 force it ALONE.  Under a section declaring [Constraint uh < up], with
 the category, its hom-sets and its identities all accepted as controls,
 each of [Slice], [Coslice], [Cartesian] (hence [Cocartesian], which is
 that class at the opposite category), [IsTerminalObj] and
 [IsInitialObj] is rejected, every one with "Cannot enforce up = uh
 because uh < up"; so is this file's own [Coslice_Proj], which inherits
 it from [Coslice] and adds nothing.  All six are FORMABILITY negatives
 1-6 in the probe.  Nothing here introduces the identification and none
 of the five donors is claimed unavoidable.

 ** Witnesses over Sets

 [Sets_Coslice_Projection_Adjunction] and
 [Sets_Slice_Projection_Adjunction] instantiate both adjunctions at an
 ARBITRARY object of [Sets].  The transposition COMPUTES:
 [sets_coslice_transpose_computes] evaluates the copairing at a
 right-summand element and gets the given map's value back, at
 [eq_refl]; [sets_slice_transpose_is_fork] and
 [sets_slice_transpose_computes] do the slice mirror through the first
 component of the pair.

 Non-degeneracy is proved rather than gestured at.
 [sets_coslice_unit_not_iso] shows the unit [inr : c ~> a + c] is not an
 isomorphism as soon as [a] is inhabited: a two-sided inverse would send
 [inl x] into the right summand, and the coproduct setoid identifies
 nothing across summands.  So the adjunction is not an equivalence.

 Non-vacuity of Block C runs in BOTH directions and at both ends.
 [sets_bipoint] is [1 + 1], with [sets_bipoint_distinct] proving its two
 points inequivalent; [sets_bipoint_not_terminal] and
 [sets_bipoint_not_initial] then give
 [sets_slice_proj_no_left_adjoint] and
 [sets_coslice_proj_no_right_adjoint] -- OUTRIGHT refutations, obtained
 by running the biconditionals forwards.  At the other end
 [sets_slice_proj_left_adjoint_at_terminal] and
 [sets_coslice_proj_right_adjoint_at_initial] exhibit the positive case
 at [Sets_Terminal]'s and [Sets_Initial]'s own objects, by running them
 backwards.  So both biconditionals are exercised in both directions
 over one concrete category.

 ** Negatives

 Twelve, of THREE KINDS kept lexically apart, all in
 Test/ProbeSliceAdjunction365.v rather than here -- an in-file
 negative command is renamed in lockstep with the constant it guards
 and so cannot detect a rename, and keeping them out of the library
 file leaves this one with zero [make todo] hits.  Six are
 FORMABILITY (the five donors plus this file's inherited
 [Coslice_Proj]), five are CONVERSION (the
 two unit/counit residues, the orientation refutation, the whole-record
 comparison with [Coslice_proj], and the transport route), one is
 TYPING (the reversed handedness).  Each was stripped one at a time and
 its whole error read.  The probe also carries a scope-free instrument
 check and a control for every constant its negatives name.

 ** What is NOT delivered

 No comparison of either adjunction with the [Comma_Coslice]/
 [Comma_Slice] readings beyond the object-action measurement above; no
 monad or comonad from either adjunction, and in particular no
 identification of the coslice one with the "writer"/coreader pair that
 Construction/Slice.v's header points at; no naturality of anything in
 [a], hence no statement that [C/(-)] or [(-)/C] is functorial here
 (Construction/Slice/Pullback.v's [Bang_Functor] is the relevant
 neighbour and is untouched); no uniqueness of the adjoints, so the two
 biconditionals assert EXISTENCE of an adjoint and not that it is the
 one named; no relation to [Slice_Terminal]/[Coslice_Initial] as an
 equivalence, only the pointwise object-level settle results; no
 composite [Σ_f ⊣ f* ⊣ Π_f] and nothing about base change; no infinite
 or indexed variants; no [Sets]-side computation of either adjoint
 functor's action beyond the transposition; and no proof that the
 [Cocartesian] hypothesis of Block A is NECESSARY -- what is proved
 there is a construction from coproducts, not a converse.

 ** Engineering findings

 Three, all about elaboration rather than mathematics.

 [(a; id)] does not elaborate to the intended sigma from context alone:
 with [id : a ~> a] the pair fits both [∃ x, x ~> a] and [∃ y, a ~> y],
 and Coq picks the coslice shape even where a slice object is expected,
 reporting "has type ∃ y, a ~> y while it is expected to have type
 obj[C ̸ a]".  [slice_id_obj] and [coslice_id_obj] therefore give the
 predicate explicitly with [existT], which is also what lets every use
 site below read as a name.

 A [Program Definition] whose body is a sigma with a hole -- the shape
 [{| morphism := fun k => (t k; _) |}] -- routes the [Proper] obligation
 through a goal whose [rewrite] is rejected with "build_signature: no
 constraint can apply on a dependent argument".  Elaborating the sigma
 as its own named [Program Definition] first ([coslice_transpose],
 [slice_transpose]) removes the dependency and leaves an ordinary
 two-argument respectfulness goal.  Note also which obligation the
 default tactic closes: [iso_to_from] of [coslice_adj], [iso_from_to] of
 [slice_adj], and the sigma hole of the two terminal/initial witnesses,
 leaving the other to [Next Obligation]; the order is the field order.

 Third, and the reason the [Sets] block is [Set]-free: a constant
 [Sets]-morphism written as a [Program Definition] leaves its
 [proper_morphism] certificate to instance resolution, which supplies
 [CMorphisms.reflexive_proper@{Set Set}] and thereby pins the carrier
 universe.  Measured here: written that way, [sets_point] came out at
 [@{u |= Set < u}].  Supplying the pointwise term
 [fun _ _ _ => reflexivity b] by hand -- as an ordinary [Definition],
 no [Program] -- removes it.  The tree records the same hazard at
 Theory/Universal/Element.v, with the same repair; this is a second
 sighting rather than a new finding. 

 --------
 参考文献：Saunders Mac Lane，《为在职数学家准备的范畴论》，第2版，§IV.2，第90页，练习11  [maclane:IV.2:ex11]：如果C有有限余积，则从某对象a下的余片中的投影具有一个左伴随，发送c到余积注入a ~> a + c，余配对作为转置，右注入作为单位。
 参考文献：Steve Awodey，《范畴论》，第2版，§9.9，练习6（带星号），第262页  [awodey:9:ex6]：切片侧的对偶。从C/a出的域函子有一个右伴随，发送y到投影y × a ~> a；带星号的部分询问它何时也有一个左伴随。
 nLab：https://ncatlab.org/nlab/show/under+category
 nLab：https://ncatlab.org/nlab/show/over+category
 维基百科：https://en.wikipedia.org/wiki/Comma_category这两个练习都是同一个构造的两次体现。从余积出的态射是一个子句对，每个加数一个子句（Structure/Cocartesian.v 的标题正是这样描述 [merge] 的）；进入积的态射是一个组成部分对。一个余切片下的对象是一个对象 x，带有一个选定的箭头 a ~> x，而从一个单独的 c 生成一个这样的对象的自由方法是附加 a：取 a + c 及其左注入。然后，从该对象射出的余切片箭头就是 a 上的一个子句——由余切片条件固定为目标自身的结构映射——加上 c 上的一个自由子句，这恰好是一个无约束的箭头 c ~> x。这就是双射，每一行下面都是围绕它的账簿工作。将一个切片箭头双重映射到 y × a，并以第二投影作为结构映射，是第一个分量自由加上第二个分量固定到源的结构映射。

 ** 文件放置：偏离了该问题的建议该问题指出 [Construction/Slice/Coslice.v] “（或 Construction/Slice.v 的扩展）”。然而，这个文件实际上是 [Construction/Slice/Adjunction.v]，因为它同时包含了余切附属（块 A）及其切片对偶（块 B）——是直接构建的，而非传递来的——此外还有块 C 的两个归纳结果和块 D 的 [Sets] 证据。“Coslice.v”将错误命名其一半以上的内容。在原地扩展 Construction/Slice.v 也被拒绝：该文件被 Construction/Comma/Special.v、Construction/Slice/Pullback.v、Construction/Slice/Terminal.v、Instance/Cat/Pullback.v 等文件所需要，而下面的内容还涉及 Structure/Cartesian.v、Structure/Cocartesian.v、Structure/Terminal.v、Structure/Initial.v、Theory/Adjunction.v 及三个 Instance/Sets 模块，这些都将影响到上述所有文件。这里的模块封闭是 31（使用 coqdep 测量）。

 ** 提供的内容，以及强度

 A 区块，位于 [{C} {CC : @Cocartesian C} (a : C)] 上：-  [Coslice_Proj a : Coslice C a ⟶ C]，投影，作为一个三行记录，其对象和箭头动作是字面上的第一次投影，因此可以约简。-  [Coslice_Coprod a : C ⟶ Coslice C a]，将 c 发送到 [(a + c; inl)]，将 f 发送到 [right f]。精确阅读对象：该值的余片结构映射是 [inl : a ~> a + c]——注入 Mac Lane 自己的句子名称——而下面的 UNIT 是 [inr : c ~> a + c]，右注入。练习中的箭头读作“id + f”是 [cover id f]，而 [coslice_fmap_is_cover] 记录了传递的 [right f] 是去除了冗余 [∘ id] 的那个态射。- **[Coslice_Projection_Adjunction a : Coslice_Coprod a ⊣ Coslice_Proj a]**，该问题的固定名称，通过 [Build_Adjunction']（Theory/Adjunction.v）构建，基于同态集等价 [coslice_adj] 以及两个正向自然而然性条款。换位是 [Hom_{a/C}((a + c; inl), (x; g)) ≊ Hom_C(c, x)]：正向 [(h; _) ↦ h ∘ inr]，反向 [k ↦ (g ▽ k; _)]。[to ∘ from] 往返是方程 [inr_merge] 所表示的，并由默认义务策略处理；[from ∘ to] 的是 [merge_comp]，[merge_inl_inr] 和 [id_right] 在根据条件重写后。- [coslice_projection_unit a c : c ~> a + c := inr] 和 [coslice_projection_counit a x := (`2 x ▽ id; _)]，其等级相对于类生成的 [unit] / [counit] 以严格优先测量（见下一节）。

 Block B，在 [{C} {CA : @Cartesian C} (a : C)] 上，以及协变:-  [Slice_Proj a : Slice C a ⟶ C]，域函子。
 -  [Slice_Prod a : C ⟶ Slice C a]，将 x 发送到 [(x × a; exr)]，
 将 f 发送到 [first f]；[slice_fmap_is_split] 是“f × id”的读法。
 - **[Slice_Projection_Adjunction a : Slice_Proj a ⊣ Slice_Prod a]**，
 置换 [Hom_C(x, y) ≊ Hom_{C/a}((x; g), (y × a; exr))]，
 前向 [k ↦ (k △ g; _)]，后向 [(h; _) ↦ exl ∘ h]。
 -  [slice_projection_unit a x := (id △ `2 x; _)] 和 [slice_projection_counit a y := exl]。

 C 块解决了带星号的问题，适用于两种手性，并且在任何地方都没有 (co)积假设——该部分只绑定 [{C} (a : C)]：

 - **[slice_proj_left_adjoint_iff_terminal a :
 { L : C ⟶ Slice C a & L ⊣ Slice_Proj a } ↔ IsTerminalObj a]**
 - **[coslice_proj_right_adjoint_iff_initial a :
 { R : C ⟶ Coslice C a & Coslice_Proj a ⊣ R } ↔ IsInitialObj a]**每个方向都是一个单独命名的引理，因此消费者通过转换而不是通过封装的 [iffT] 进行投影：[slice_left_adjoint_terminal] / [slice_terminal_left_adjoint] 搭配 [slice_terminal_left_adjoint_adj] 以及初始镜像。启用的事实是 [slice_id_IsTerminalObj] —— [(a; id)] 在 [Slice C a] 中是终结的 —— 以及 [coslice_id_IsInitialObj]，其双重；每个都有一个手动解除的义务，即唯一性条款，在用竞争条件重写后成为一个单位律，而 sigma 自身的孔通过默认义务策略闭合。必要性通过伴随的 [Sets]-同构读取单元素，而充分性构建其伴随，其换位在底层箭头上是恒等的，所以所有四个自然性条款都通过 [reflexivity] 闭合。Construction/Slice/Terminal.v 的 [Slice_Terminal :
 Slice C 1 ≅ [Cat]  C] 是在捆绑的 [Terminal] 上的特殊情况。 它被引用，而不是使用：练习要求解决的是对象级别的 [IsTerminalObj] 语句，通过捆绑类路径会需要再次解捆绑，而直接论证大约有十五行。

 Block D 对 [Sets] 上的所有内容进行了练习。

 ** 该单元字面意思就是余积注入，而残差是展示出来的，而不是描述的问题的审查检查是该单元是余积注入。[coslice_projection_unit a c] 是没有任何包装的 [inr] —— 一个 [Definition] 其主体是常数。CLASS 生成的是 [⌊id⌋]，而前向转置与 [inr] 后复合，同时余切片的恒等由 C 的 [id] 传递，因此类值是 [id ∘ inr]。两个等级都被记录：

 - [coslice_unit_strict]，一个在 [eq_refl] 闭合的 [Example]：[unit = id ∘ coslice_projection_unit a c]。残差是按字面陈述的，因此后续移除它的更改会破坏这一行，而不会被忽略。
 - [coslice_unit_is_inr]，[≈] 形式，离 [id_left] 只有一步。

 严格恒等 [unit = inr] 并不成立，并且在 Test/ProbeSliceAdjunction365.v 中被固定为 CONVERSION 负 7。这四个等级在两个区块之间并不统一，而且这个模式值得保留，因为它是镜像的：

 - coslice UNIT: 留数 [id ∘ -]，在左侧。
 - coslice COUNIT: 在底层态射上是严格的——
 [coslice_counit_strict] 在 [eq_refl] 处给出 [`1 (counit x) = `2 x ▽ id]——并且 [≈] 作为 coslice 箭头由 [reflexivity] 给出，
 coslice 同态集合仅比较第一投影。整个记录不相等，因为 [coslice_projection_counit] 有其自身的义务证明。
 - slice UNIT: 在底层态射上是严格的，[`1 (unit x) = id △ `2 x]。
 - slice COUNIT: 留数 [- ∘ id]，在右侧（[slice_counit_strict]），并且 [slice_counit_is_exl] 是 [≈] 形式，离 [id_right] 一个单位。固定为 CONVERSION 负 8。这种不对称的原因是结构性的，而不是偶然的：[⌊id⌋] 将恒等式输入到前向转置中，而 [⌈id⌉] 输入到后向转置中，在每个块中正好有一个转置通过组合作用于它的参数。

 ** 切片侧是直接构建的，而“一个相反的传输移开”的说法是经过测量的该问题的工作项 4 说切片语句“只是一个 [Opposite] 传输的距离”。在同构下这是正确的，但不是完全一样的，而审查员检查——在任何交付类型中都没有残余的 [^op] ——正是让这个区别起作用的原因。展开操作，即 C^op 上切片的相反操作，具有 [∃ f, f ∘ `2 x ≈ `2 y] 的同态，而 Construction/Slice.v 的 [Coslice] 拥有 [∃ f, `2 y ≈ f ∘ `2 x]：在另一个方向上的相同方程，因此是不同的类型。Construction/Slice/Terminal.v 已经准确记录了这一点，作为直接证明 [Coslice_Initial] 而不是传输 [Slice_Terminal] 的理由。这里它被标记为 CONVERSION 负 9，相对于一个显示 OBJECT 类型在定义上确实一致的控制，所以障碍位于同态方程而不是整个编码上。因此，B块是直接构造。单词 [Opposite] 和标记 [^op] 在下文中都不存在，而 [Structure/Cocartesian.v] 自己的 [Cocartesian C] 符号——即 [Cartesian (C^op)]——是二重性出现的唯一位置，在A块中，它是树自身表示具有余积的拼写。

 ** 现有技术：该问题中的三项权利要求已过时，其中一项是其自身的。(1) 该期刊的 Awodey 章节谈到切片域函子时说：“函子本身并不存在”。实际上它是存在的，而且存在两次。Instance/Cat/Pullback.v 中的 [Slice_proj] 和 [Coslice_proj] 就是这个三行记录，本身具有相同的签名 [{C} (c)]；Construction/Slice/Terminal.v 中的 [Slice_Forget] 和 [Coslice_Forget] 是其对终端和初始基对象的特化。在这里测量的一致性存在于探针中，而不是在这里：[Coslice_Proj] / [Coslice_proj] 的两个 DATA 字段在两种方向上在 [eq_refl] 上一致，而整个记录则不一致，三条 [Functor] 法则字段各自为文件自身的不透明义务（CONVERSION 负 10）。这个记录是重新构建的而不是导入的，因为 Instance/Cat/Pullback.v 模块封闭为 39，而导入它会给该文件的 31 个模块增加 14 个模块。(2) 同一节指出：“整个 slice 开发是 Construction/Slice.v 的四个定义加上 Construction/Slice/Pullback.v 中的两个基变函子”。它遗漏了 Construction/Slice/Terminal.v 以及十二个已声明的结果，包括前面提到的两个遗忘函子。

 (3) 本期的 Mac Lane 小节指出：“在 slice、coslice 和 comma 文件中搜索 [⊣] 仅找到被注释掉的 slice 基变存根”。当时该存根是存在的；后来它已被删除且定理已被证明，如 Construction/Slice/Pullback.v 中的 [Base_Functor_Adjunction] 所示。即便如此，Construction/Comma/Adjunction.v 在整个过程中仍保留着有效的 [⊣] 结果，其中包括 [Comma_Functor_F_Id_Id_G] 和 Lawvere 的双条件 [Adjunction_Comma]——正如本期前一段所述。(4) 该问题完全正确的地方，以及因此该文件并未争议的地方，是核心的缺失：没有将 c 发送到注入 [a ~> a + c] 的函子，没有用于任一投影的余adjunction，也没有任何地方存在余积-注入单位。该问题自身建议的路径——通过  [comma_proj2] (Construction/Comma.v) 传输到  [Comma_Coslice] (Construction/Slice.v)——是第三种方式，并且它是被测量而非被忽略的。复合类型通过类型检查并在探针中构建为  [p365_via_comma] 。但是  [Comma_Coslice] 是一个  [Program Instance] ，其  [to] 被写为  [{| fobj := _; fmap := _ |}]，因此比较函子的两个数据字段都是义务：即使传输的 OBJECT 动作也不能准确返回  [`1 x] （CONVERSION 负 12），而直接记录则在定义上包含它。其  [≅[Cat] 的强度是第二种成本，[Cat] 的同构集是自然同构。  

 ** 宇宙：识别在绑定器中，而不在块中这里的每个标题常量——四个函子、两个伴随、两个双条件——都是在 [C : Category@{u u0 u0}] 上的同态，通过在 BINDER 中重用一级变量的证明来标识，而其约束块中根本没有方程：只有 [<] 和 [<=]。仅读取该块会报告“未标识”，这是错误的；两者都必须读取。测量时，先展平空白，因为 [Print] 包装了宇宙实例：

 [Coslice_Proj@{u u0 u1 u2}]，并且同样的 [Coslice_Coprod]，
 [Slice_Proj]，[Slice_Prod]：[u0 < u1] 加上五个界限。
 [Coslice_Projection_Adjunction@{u u0 u1 u2 u3}] 和 [Slice_Projection_Adjunction]：[u0 < u2] 加上十七个界限
 ([Basics.compose]，[Logic_lemmas.equality]，[Projections]，
 [prod_rect]，[projections]，[ID])。
 [slice_proj_left_adjoint_iff_terminal@{u u0 u1 u2 u3 u4 u5}] 和 [coslice_proj_right_adjoint_iff_initial]：[u0 < u1] 加上二十个界限。保持免费的对象是对象宇宙：[u] 没有出现在任何方程中，只出现在界限中，在八个界限的每一个中都有。而且没有 [Set] 出现在任何绑定器或块中，无论是一般结果还是 [Sets] 证人中——这就是为什么 D 块将其两个元素的对象作为余积 [1 + 1] 在 [Sets] 中构建，而不是在 [bool] 中。同态证明识别是继承的，并且五个捐赠者各自单独强制它。在一个声明 [Constraint uh < up] 的部分下，其类别、同态集及其恒等式均被接受作为控制，每一个 [Slice]、[Coslice]、[Cartesian]（因此 [Cocartesian]，为相对类别的该类）、[IsTerminalObj] 和 [IsInitialObj] 都被拒绝，每个都有“无法强制 up = uh 因为 uh < up”；这个文件自身的 [Coslice_Proj] 也是如此，它从 [Coslice] 继承它且没有添加任何内容。这六个都是探测中的可形成性负面 1-6。在这里没有任何引入该识别，并且没有声称五个捐赠者是不可避免的。

 ** 集合上的见证[Sets_Coslice_Projection_Adjunction] 和 [Sets_Slice_Projection_Adjunction] 在 [Sets] 的任意对象上实例化了两个伴随。换位计算如下：[sets_coslice_transpose_computes] 在右求和元素上评估联合映射，并得到给定映射在 [eq_refl] 的值；[sets_slice_transpose_is_fork] 和 [sets_slice_transpose_computes] 通过对偶元组的第一个分量执行切片镜像。

 非退化性是被证明而不是仅仅指示的。[sets_coslice_unit_not_iso] 显示，一旦 [a] 被占用，单位 [inr : c ~> a + c] 就不是一个同构：双边逆会将 [inl x] 发送到右求和分量，而并集集合序列不会在分量之间识别任何东西。因此，该伴随不是一个等价。区块C的非空性在两个方向和两端都成立。[sets_bipoint] 是 [1 + 1]，[sets_bipoint_distinct] 证明了它的两个点不等价；[sets_bipoint_not_terminal] 和 [sets_bipoint_not_initial] 然后给出 [sets_slice_proj_no_left_adjoint] 和 [sets_coslice_proj_no_right_adjoint]——通过正向运行双条件语句获得的彻底反驳。在另一端，[sets_slice_proj_left_adjoint_at_terminal] 和 [sets_coslice_proj_right_adjoint_at_initial] 展示了 [Sets_Terminal] 和 [Sets_Initial] 自身对象的正面情况，通过反向运行它们。因此，这两个双条件语句在一个具体范畴中都在两个方向上被使用。** 否定十二个，三种类型，在词汇上保持分开，都在 Test/ProbeSliceAdjunction365.v 中，而不是在这里 —— 文件内的负命令会与它所保护的常量同步重命名，因此无法检测重命名，将它们保持在库文件之外使这个文件的 [make todo] 命中次数为零。六个是 FORMABILITY（五个捐赠者加上本文件继承的 [Coslice_Proj]），五个是 CONVERSION（两个单位/余单位残差，方向否定，整个记录与 [Coslice_proj] 的比较，以及传输路径），一个是 TYPING（反向手性）。每个都是一次剥离，然后读取其整个错误。探针还携带一个无作用域的工具检查，以及为其负值所命名的每个常量的控制。 

 ** 未交付的内容除了上述的对象-动作测量外，没有对任一附加的 [Comma_Coslice] / [Comma_Slice]  读数进行比较；没有从任一附加产生的 monad 或 comonad，特别是没有将 coslice 与 Construction/Slice.v 头部指向的“writer”/coreader 对进行识别；在 [a] 中没有任何自然性，因此没有说明 [C/(-)] 或 [(-)/C] 在此处是函子（Construction/Slice/Pullback.v 的 [Bang_Functor] 是相关的邻居，并未被触及）；没有伴随的唯一性，因此两个双重条件断言的是伴随的存在，而不是它是被命名的那个；与 [Slice_Terminal] / [Coslice_Initial] 作为等价的关系无关，仅有逐点对象层面的确定结果；没有复合 [Σ_f ⊣ f* ⊣ Π_f]，也没有关于基变换的内容；没有无限或索引变量巨人；没有对任一伴随函子的作用进行 [Sets] 方面的计算，超出换位之外；也没有证明 Block A 的 [Cocartesian] 假设是必要的——在那里证明的是从余积的构造，而不是逆命题。** 工程发现

 三、全部关于展开而非数学。

 [(a; id)] 单凭上下文无法展开到预期的 σ：
 使用 [id : a ~> a] 时，该对同时适用于 [∃ x, x ~> a] 和 [∃ y, a ~> y]，
 而 Coq 即使在期望切片对象的地方也会选择余切片（coslice）形状，
 报告“具有类型 ∃ y, a ~> y，而期望的类型是 obj [C ̸ a]”。[slice_id_obj] 和 [coslice_id_obj] 因此用 [existT] 显式给出了谓词，这也让下面每个使用场所都能作为一个名称读取。一个 [Program Definition]，其主体是带孔的 sigma —— 形状 [{| morphism := fun k => (t k; _) |}] —— 将 [Proper] 义务通过一个目标路由，该目标的 [rewrite] 被拒绝，显示“build_signature: no constraint can apply on a dependent argument”。首先将 sigma 作为其自身命名的 [Program Definition] 展开（[coslice_transpose], [slice_transpose]）会移除依赖性，并留下一个普通的两参数尊重性目标。还要注意默认策略关闭了哪一项义务：[iso_to_from] 的 [coslice_adj]，[iso_from_to] 的 [slice_adj]，以及两个终端/初始证人的 sigma 孔，留下另一个给 [Next Obligation]；顺序是字段顺序。第三，也是 [Sets] 模块没有 [Set] 的原因：一个常数 [Sets]-同态写成 [Program Definition] 的形式，将其 [proper_morphism] 证书留给实例解析，该解析提供 [CMorphisms.reflexive_proper@{Set Set}]，从而固定了承载宇宙。在这里测量：以这种方式写，[sets_point] 得出的结果是 [@{u |= Set < u}]。通过手工提供点值项 [fun _ _ _ => reflexivity b] —— 作为普通的 [Definition]，没有 [Program] —— 可以去掉它。树记录了 Theory/Universal/Element.v 中相同的风险，并附有相同的修复；这是第二次观察到，而不是新的发现。
*)


(* * ** Block A: the coslice projection and its left adjoint / * ** A 块：余切片投影及其左伴随 *)

Section CosliceAdjunction.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context (a : C).

Program Definition Coslice_Proj : @Coslice C a ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Definition Coslice_Coprod : C ⟶ @Coslice C a := {|
  fobj := fun c => (a + c; inl);
  fmap := fun _ _ f => (right f; _)
|}.
Next Obligation. symmetry; apply inl_right. Qed.
Next Obligation. proper; now rewrite X. Qed.
Next Obligation. apply right_id. Qed.
Next Obligation. apply right_comp. Qed.

Program Definition coslice_adj_to (c : C) (y : @Coslice C a) :
  {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
   ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |}
    ~{Sets}~>
  {| carrier   := c ~{C}~> Coslice_Proj y
   ; is_setoid := @homset C c (Coslice_Proj y) |} := {|
  morphism := fun h => `1 h ∘ inr
|}.

(*
 The exercise words the arrow action as "id + f"; the tree spells that
 [cover id f], and [right f] is the same morphism with the redundant
 [∘ id] removed. 

 --------
 练习将箭头动作表示为“id + f”；树形拼写为 [cover id f]，而 [right f] 是相同的同态，只是去掉了多余的 [∘ id]。
*)
Lemma coslice_fmap_is_cover (x y : C) (f : x ~> y) :
  `1 (fmap[Coslice_Coprod] f) ≈ cover id f.
Proof.
  simpl; unfold right, cover.
  apply merge_respects; [ now rewrite id_right | reflexivity ].
Qed.

Program Definition coslice_transpose (c : C) (y : @Coslice C a)
  (k : c ~> `1 y) : Coslice_Coprod c ~{@Coslice C a}~> y := (`2 y ▽ k; _).

Program Definition coslice_adj_from (c : C) (y : @Coslice C a) :
  {| carrier   := c ~{C}~> Coslice_Proj y
   ; is_setoid := @homset C c (Coslice_Proj y) |}
    ~{Sets}~>
  {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
   ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |} := {|
  morphism := coslice_transpose c y
|}.
Next Obligation. intros k1 k2 Hk; simpl; now rewrite Hk. Qed.

Program Definition coslice_adj (c : C) (y : @Coslice C a) :
  @Isomorphism Sets
    {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
     ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |}
    {| carrier   := c ~{C}~> Coslice_Proj y
     ; is_setoid := @homset C c (Coslice_Proj y) |} := {|
  to   := coslice_adj_to c y;
  from := coslice_adj_from c y
|}.
Next Obligation.
  rewrite X, merge_comp, merge_inl_inr.
  apply id_right.
Qed.

Definition Coslice_Projection_Adjunction : Coslice_Coprod ⊣ Coslice_Proj.
Proof.
  unshelve eapply (@Build_Adjunction' (@Coslice C a) C
                     Coslice_Coprod Coslice_Proj coslice_adj).
  - intros x y z f g; simpl.
    rewrite <- !comp_assoc.
    now rewrite inr_right.
  - intros x y z f g; simpl.
    now rewrite <- !comp_assoc.
Defined.

Definition coslice_projection_unit (c : C) : c ~> a + c := inr.

Program Definition coslice_projection_counit (x : @Coslice C a) :
  Coslice_Coprod (Coslice_Proj x) ~{@Coslice C a}~> x := (`2 x ▽ id; _).

Example coslice_unit_strict (c : C) :
  @unit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction c = id ∘ coslice_projection_unit c
  := eq_refl.

Lemma coslice_unit_is_inr (c : C) :
  @unit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction c ≈ coslice_projection_unit c.
Proof. apply id_left. Qed.

Example coslice_counit_strict (x : @Coslice C a) :
  `1 (@counit (@Coslice C a) C Coslice_Coprod Coslice_Proj
        Coslice_Projection_Adjunction x) = `2 x ▽ id := eq_refl.

Lemma coslice_counit_is_merge (x : @Coslice C a) :
  @counit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction x ≈ coslice_projection_counit x.
Proof. simpl; reflexivity. Qed.

End CosliceAdjunction.

(* * ** Block B: the slice projection and its right adjoint / * ** 块 B：切片投影及其右伴随 *)

Section SliceAdjunction.

Context {C : Category}.
Context {CA : @Cartesian C}.
Context (a : C).

Program Definition Slice_Proj : @Slice C a ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Definition Slice_Prod : C ⟶ @Slice C a := {|
  fobj := fun x => (x × a; exr);
  fmap := fun _ _ f => (first f; _)
|}.
Next Obligation. apply exr_first. Qed.
Next Obligation. proper; now rewrite X. Qed.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(*
 Dually, the slice arrow action is "f × id", spelled [split f id]; the
 [id ∘] on the second component is what [first f] omits. 

 --------
 同样，切片箭头操作是 "f × id"，拼写为 [split f id]；第二个分量上的 [id ∘] 是 [first f] 所省略的。
*)
Lemma slice_fmap_is_split (x y : C) (f : x ~> y) :
  `1 (fmap[Slice_Prod] f) ≈ split f id.
Proof.
  simpl; unfold first, split.
  apply fork_respects; [ reflexivity | now rewrite id_left ].
Qed.

Program Definition slice_transpose (x : @Slice C a) (y : C)
  (k : `1 x ~> y) : x ~{@Slice C a}~> Slice_Prod y := (k △ `2 x; _).

Program Definition slice_adj_to (x : @Slice C a) (y : C) :
  {| carrier   := Slice_Proj x ~{C}~> y
   ; is_setoid := @homset C (Slice_Proj x) y |}
    ~{Sets}~>
  {| carrier   := x ~{@Slice C a}~> Slice_Prod y
   ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |} := {|
  morphism := slice_transpose x y
|}.
Next Obligation. intros k1 k2 Hk; simpl; now rewrite Hk. Qed.

Program Definition slice_adj_from (x : @Slice C a) (y : C) :
  {| carrier   := x ~{@Slice C a}~> Slice_Prod y
   ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |}
    ~{Sets}~>
  {| carrier   := Slice_Proj x ~{C}~> y
   ; is_setoid := @homset C (Slice_Proj x) y |} := {|
  morphism := fun h => exl ∘ `1 h
|}.

Program Definition slice_adj (x : @Slice C a) (y : C) :
  @Isomorphism Sets
    {| carrier   := Slice_Proj x ~{C}~> y
     ; is_setoid := @homset C (Slice_Proj x) y |}
    {| carrier   := x ~{@Slice C a}~> Slice_Prod y
     ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |} := {|
  to   := slice_adj_to x y;
  from := slice_adj_from x y
|}.
Next Obligation.
  rewrite <- X, fork_comp, fork_exl_exr.
  apply id_left.
Qed.

Definition Slice_Projection_Adjunction : Slice_Proj ⊣ Slice_Prod.
Proof.
  unshelve eapply (@Build_Adjunction' C (@Slice C a)
                     Slice_Proj Slice_Prod slice_adj).
  - intros x y z f g; simpl.
    rewrite <- fork_comp.
    now rewrite (`2 g).
  - intros x y z f g; simpl.
    now rewrite first_fork.
Defined.

Program Definition slice_projection_unit (x : @Slice C a) :
  x ~{@Slice C a}~> Slice_Prod (Slice_Proj x) := (id △ `2 x; _).

Definition slice_projection_counit (y : C) :
  Slice_Proj (Slice_Prod y) ~> y := exl.

Example slice_unit_strict (x : @Slice C a) :
  `1 (@unit C (@Slice C a) Slice_Proj Slice_Prod
        Slice_Projection_Adjunction x) = id △ `2 x := eq_refl.

Lemma slice_unit_is_fork (x : @Slice C a) :
  @unit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction x ≈ slice_projection_unit x.
Proof. simpl; reflexivity. Qed.

Example slice_counit_strict (y : C) :
  @counit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction y = slice_projection_counit y ∘ id
  := eq_refl.

Lemma slice_counit_is_exl (y : C) :
  @counit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction y ≈ slice_projection_counit y.
Proof. apply id_right. Qed.

End SliceAdjunction.

(*
   * ** Block C: when do the projections have adjoints on the other side? 

   --------
   * ** 块 C：投影什么时候在另一侧有伴随？
*)

Section SliceSettle.

Context {C : Category}.
Context (a : C).

Definition slice_id_obj : @Slice C a :=
  existT (fun x : C => x ~> a) a id.
Definition coslice_id_obj : @Coslice C a :=
  existT (fun x : C => a ~> x) a id.

Program Definition slice_id_IsTerminalObj :
  @IsTerminalObj (@Slice C a) slice_id_obj := fun x => {|
  unique_obj := (`2 x; _);
  unique_property := I
|}.
Next Obligation. rewrite <- X; apply id_left. Qed.

Program Definition coslice_id_IsInitialObj :
  @IsInitialObj (@Coslice C a) coslice_id_obj := fun x => {|
  unique_obj := (`2 x; _);
  unique_property := I
|}.
Next Obligation. rewrite X; apply id_right. Qed.

Lemma slice_left_adjoint_terminal (L : C ⟶ @Slice C a)
  (A : L ⊣ Slice_Proj a) : IsTerminalObj a.
Proof.
  intro c.
  unshelve econstructor.
  - exact (to (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj)
             (unique_obj (slice_id_IsTerminalObj (L c)))).
  - exact I.
  - intros v _.
    transitivity
      (to (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj)
         (from (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj) v)).
    + apply proper_morphism.
      apply (uniqueness (slice_id_IsTerminalObj (L c)) _ I).
    + apply (iso_to_from
               (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj) v).
Qed.

Program Definition slice_terminal_left_adjoint (H : IsTerminalObj a) :
  C ⟶ @Slice C a := {|
  fobj := fun x => (x; is_terminal_one H);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply (is_terminal_unique H). Qed.

Program Definition slice_terminal_adj (H : IsTerminalObj a)
  (x : C) (y : @Slice C a) :
  @Isomorphism Sets
    {| carrier   := slice_terminal_left_adjoint H x ~{@Slice C a}~> y
     ; is_setoid :=
         @homset (@Slice C a) (slice_terminal_left_adjoint H x) y |}
    {| carrier   := x ~{C}~> Slice_Proj a y
     ; is_setoid := @homset C x (Slice_Proj a y) |} := {|
  to   := {| morphism := fun h => `1 h |};
  from := {| morphism := fun k => (k; _) |}
|}.
Next Obligation. apply (is_terminal_unique H). Qed.

Definition slice_terminal_left_adjoint_adj (H : IsTerminalObj a) :
  slice_terminal_left_adjoint H ⊣ Slice_Proj a.
Proof.
  unshelve eapply (@Build_Adjunction' (@Slice C a) C
                     (slice_terminal_left_adjoint H) (Slice_Proj a)
                     (slice_terminal_adj H)).
  - intros x y z f g; simpl; reflexivity.
  - intros x y z f g; simpl; reflexivity.
Defined.

Theorem slice_proj_left_adjoint_iff_terminal :
  { L : C ⟶ @Slice C a & L ⊣ Slice_Proj a } ↔ IsTerminalObj a.
Proof.
  split.
  - intros [L A]; exact (slice_left_adjoint_terminal L A).
  - intro H.
    exists (slice_terminal_left_adjoint H).
    exact (slice_terminal_left_adjoint_adj H).
Defined.

Lemma coslice_right_adjoint_initial (R : C ⟶ @Coslice C a)
  (A : Coslice_Proj a ⊣ R) : IsInitialObj a.
Proof.
  intro c.
  unshelve econstructor.
  - exact (from (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c)
             (unique_obj (coslice_id_IsInitialObj (R c)))).
  - exact I.
  - intros v _.
    transitivity
      (from (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c)
         (to (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c) v)).
    + apply proper_morphism.
      apply (uniqueness (coslice_id_IsInitialObj (R c)) _ I).
    + apply (iso_from_to
               (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c) v).
Qed.

Program Definition coslice_initial_right_adjoint (H : IsInitialObj a) :
  C ⟶ @Coslice C a := {|
  fobj := fun x => (x; is_initial_zero H);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply (is_initial_unique H). Qed.

Program Definition coslice_initial_adj (H : IsInitialObj a)
  (x : @Coslice C a) (y : C) :
  @Isomorphism Sets
    {| carrier   := Coslice_Proj a x ~{C}~> y
     ; is_setoid := @homset C (Coslice_Proj a x) y |}
    {| carrier   := x ~{@Coslice C a}~> coslice_initial_right_adjoint H y
     ; is_setoid :=
         @homset (@Coslice C a) x
           (coslice_initial_right_adjoint H y) |} := {|
  to   := {| morphism := fun k => (k; _) |};
  from := {| morphism := fun h => `1 h |}
|}.
Next Obligation. apply (is_initial_unique H). Qed.

Definition coslice_initial_right_adjoint_adj (H : IsInitialObj a) :
  Coslice_Proj a ⊣ coslice_initial_right_adjoint H.
Proof.
  unshelve eapply (@Build_Adjunction' C (@Coslice C a)
                     (Coslice_Proj a) (coslice_initial_right_adjoint H)
                     (coslice_initial_adj H)).
  - intros x y z f g; simpl; reflexivity.
  - intros x y z f g; simpl; reflexivity.
Defined.

Theorem coslice_proj_right_adjoint_iff_initial :
  { R : C ⟶ @Coslice C a & Coslice_Proj a ⊣ R } ↔ IsInitialObj a.
Proof.
  split.
  - intros [R A]; exact (coslice_right_adjoint_initial R A).
  - intro H.
    exists (coslice_initial_right_adjoint H).
    exact (coslice_initial_right_adjoint_adj H).
Defined.

End SliceSettle.

(* * ** Block D: witnesses over [Sets] / * ** D区：关于 [Sets] 的证人 *)

Definition Sets_Coslice_Projection_Adjunction (a : Sets) :
  Coslice_Coprod a ⊣ Coslice_Proj a := Coslice_Projection_Adjunction a.

Definition Sets_Slice_Projection_Adjunction (a : Sets) :
  Slice_Proj a ⊣ Slice_Prod a := Slice_Projection_Adjunction a.

Definition sets_bipoint : Sets :=
  @Coprod Sets Sets_Cocartesian
    (@terminal_obj Sets Sets_Terminal)
    (@terminal_obj Sets Sets_Terminal).

Definition sets_bipoint_l : carrier sets_bipoint := Datatypes.inl ttt.
Definition sets_bipoint_r : carrier sets_bipoint := Datatypes.inr ttt.

Lemma sets_bipoint_distinct : sets_bipoint_l ≈ sets_bipoint_r → False.
Proof. intro H; exact H. Qed.

(*
 The [proper_morphism] certificate is written out as a POINTWISE TERM
 rather than left to instance resolution.  Resolution finds
 [CMorphisms.reflexive_proper@{Set Set}] here and thereby pins the
 carrier universe of [Sets] to [Set]; the tree records the same hazard
 at Theory/Universal/Element.v.  With the term supplied by hand both
 constants stay polymorphic. 

 --------
 [proper_morphism] 证书被写成一个逐点项，而不是留给实例解析。解析在这里找到 [CMorphisms.reflexive_proper@{Set Set}]，从而将 [Sets] 的承载宇宙固定在 [Set]；树在 Theory/Universal/Element.v 中记录了相同的危险。通过手工提供的项，两个常量都保持多态。
*)
Definition sets_point (b : carrier sets_bipoint) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> sets_bipoint :=
  {| morphism        := fun _ => b
   ; proper_morphism := fun _ _ _ => reflexivity b |}.

Definition sets_bipoint_const (b : carrier sets_bipoint) :
  sets_bipoint ~{Sets}~> sets_bipoint :=
  {| morphism        := fun _ => b
   ; proper_morphism := fun _ _ _ => reflexivity b |}.

Lemma sets_bipoint_not_terminal : IsTerminalObj sets_bipoint → False.
Proof.
  intro H.
  exact (is_terminal_unique H (sets_point sets_bipoint_l)
           (sets_point sets_bipoint_r) ttt).
Qed.

Lemma sets_bipoint_not_initial : IsInitialObj sets_bipoint → False.
Proof.
  intro H.
  exact (is_initial_unique H id (sets_bipoint_const sets_bipoint_l)
           sets_bipoint_r).
Qed.

Theorem sets_slice_proj_no_left_adjoint :
  { L : Sets ⟶ @Slice Sets sets_bipoint & L ⊣ Slice_Proj sets_bipoint } → False.
Proof.
  intro X.
  exact (sets_bipoint_not_terminal
           (fst (slice_proj_left_adjoint_iff_terminal sets_bipoint) X)).
Qed.

Theorem sets_coslice_proj_no_right_adjoint :
  { R : Sets ⟶ @Coslice Sets sets_bipoint & Coslice_Proj sets_bipoint ⊣ R }
    → False.
Proof.
  intro X.
  exact (sets_bipoint_not_initial
           (fst (coslice_proj_right_adjoint_iff_initial sets_bipoint) X)).
Qed.

Definition sets_slice_proj_left_adjoint_at_terminal :
  { L : Sets ⟶ @Slice Sets (@terminal_obj Sets Sets_Terminal)
      & L ⊣ Slice_Proj (@terminal_obj Sets Sets_Terminal) } :=
  snd (slice_proj_left_adjoint_iff_terminal
         (@terminal_obj Sets Sets_Terminal))
    (IsTerminalObj_from_Terminal Sets_Terminal).

Definition sets_coslice_proj_right_adjoint_at_initial :
  { R : Sets ⟶ @Coslice Sets (@initial_obj Sets Sets_Initial)
      & Coslice_Proj (@initial_obj Sets Sets_Initial) ⊣ R } :=
  snd (coslice_proj_right_adjoint_iff_initial
         (@initial_obj Sets Sets_Initial))
    (IsInitialObj_from_Initial Sets_Initial).

Example sets_coslice_transpose_computes (a c : Sets)
  (y : @Coslice Sets a) (k : c ~{Sets}~> Coslice_Proj a y)
  (z : carrier c) :
  `1 (coslice_transpose a c y k) (Datatypes.inr z) = k z := eq_refl.

Example sets_slice_transpose_is_fork (a : Sets) (x : @Slice Sets a)
  (y : Sets) (k : `1 x ~{Sets}~> y) :
  `1 (slice_transpose a x y k) = k △ `2 x := eq_refl.

Example sets_slice_transpose_computes (a : Sets) (x : @Slice Sets a)
  (y : Sets) (k : `1 x ~{Sets}~> y) (z : carrier (`1 x)) :
  Datatypes.fst ((k △ `2 x) z) = k z := eq_refl.

Lemma sets_coslice_unit_not_iso (a c : Sets) (x : carrier a) :
  IsIsomorphism (@coslice_projection_unit Sets Sets_Cocartesian a c)
    → False.
Proof.
  intros [g Hr Hl].
  exact (Hr (Datatypes.inl x)).
Qed.
