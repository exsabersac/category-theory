Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(* * * The fork C² ⇉ C → 1 in Cat, split by a terminal object of C / * * 范畴 Cat 中的分叉 C² ⇉ C → 1，由 C 的一个终对象分裂 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, §VI.6, the example of a fork in Cat,
 printed p. 150 (PDF p. 159) — maclane:VI.6:remark1; the
 definitions of fork and split fork open the section, printed
 p. 149 (PDF p. 158)
 nLab: https://ncatlab.org/nlab/show/split+coequalizer
 nLab: https://ncatlab.org/nlab/show/arrow+category
 nLab: https://ncatlab.org/nlab/show/terminal+category

 WHAT THE BOOK SAYS, read from the page images.  On p. 149: "By a fork
 in a category C we mean a diagram a ⇉ b → c (1) in C with e∂₀ = e∂₁",
 and "A split fork in C is a fork (1) with two more arrows a ← b ← c
 (2)", t and s, "which satisfy with the arrows (1) the conditions
 e∂₀ = e∂₁, es = 1, ∂₀t = 1, ∂₁t = se. (3)".  On p. 150: "Since a
 split fork is defined by equations involving only composites and
 identities, it remains a split fork under the application of any
 functor.  Hence, Corollary.  In every split fork, e is an absolute
 coequalizer of ∂₀ and ∂₁."  Then: "Here is an example of a fork in
 Cat, for C any category: C² ⇉ C → 1", the pair ∂₀, ∂₁ and the arrow
 e.  "C² is the category whose objects are the arrows of C; ∂₀ and ∂₁
 are the functors assigning to each arrow its domain and its codomain,
 respectively, while e is the functor which sends every object of C
 to the unique object of 1.  If C has a terminal object a₀, this fork
 is split by the functor s which sends the unique object of 1 to a₀,
 and the functor t which sends each c ∈ C to the unique arrow
 c → a₀."

 THE DATA: FOUR PIECES REUSED, ONE NEW.  C² is Construction/Arrow.v's
 [Arrow C], the comma (Id ↓ Id).  ∂₀ and ∂₁ are
 Construction/Comma/Diagram.v's [Arrow_dom] and [Arrow_cod], Mac Lane's
 ∂0 and ∂1 of §II.6, the comma projections at S = T = Id.  e is
 Instance/One.v's [Erase C], which is the terminal map of [Cat] and of
 [StrictCat] at [eq_refl] ([arrow_fork_e_one],
 [arrow_fork_e_one_strict]).  s is [Diagonal _1 a₀], the constant
 functor of Functor/Diagonal.v out of 1, i.e. the functor 1 ⟶ C picking
 out a₀, which is how Instance/One/Diagonal.v reads it and the term
 Instance/Cat/Pullback.v uses as a cospan leg; it sends the object of
 1 to a₀ at [eq_refl] ([arrow_fork_s_obj]).  The new functor is t,
 [arrow_fork_t]: Construction/Arrow/Functor.v's [Arrow_intro], Mac
 Lane's Exercise II.4.7 reading of a natural transformation as a
 functor into C², applied to the unique arrow from Id[C] to the
 terminal object of the functor category [C, C], the constant functor
 at a₀ (Instance/Fun/Terminal.v's [Functor_Category_Terminal], by that
 file's account Mac Lane's Exercise III.5.5 in the nullary case).  So
 t c is the unique arrow c → a₀ ([arrow_fork_t_obj]) and t f is the
 square (f, 1) ([arrow_fork_t_map]), both at [eq_refl].

 NAMES.  Construction/Arrow/Functor.v, required for [Arrow_intro], has
 an [Arrow_dom H] and an [Arrow_cod H] of its own, the boundaries of a
 functor H into C².  Construction/Comma/Diagram.v is required after it,
 so the short names below are Diagram.v's; the two pairs have
 different types, so a mix-up would be a type error and could not
 change a statement's meaning silently.

 THE FOUR LAWS.  The split fork is Structure/Coequalizer/Split.v's
 record [SplitCoequalizer] with f := ∂₀ and g := ∂₁, whose four laws
 are Mac Lane's (3) in his order.  They are proved in [StrictCat], the
 strict category of categories of the textbooks, which identifies two
 functors by equalities of their values at every object along which
 their arrow maps agree up to ≈ ([Functor_StrictEq_Setoid]): laws 1
 and 2 because any two functors into 1 are strictly equal
 (Instance/StrictCat/Terminal.v's [StrictCat_Terminal]), laws 3 and 4
 with the object component [fun _ => eq_refl] and reflexivity on
 arrows; their proofs end [Defined], and those components read back
 at [eq_refl] ([arrow_fork_law3_strict_component],
 [arrow_fork_law4_strict_component]).  Law 1 needs no terminal object,
 so C² ⇉ C → 1 is a fork for every C, as the book says
 ([arrow_fork_law1_strict]; in [Cat], [arrow_fork_law1], from
 Instance/One.v's [Cat_Terminal]).  The split fork in [StrictCat] is
 [arrow_fork_split_strict].  The one in [Cat], [arrow_fork_split], is
 that one pushed along Instance/StrictCat/ToCat.v's comparison functor
 [StrictCat_to_Cat] by Split.v's [functor_preserves_split]: the remark
 on p. 150 that a split fork, being defined by equations, remains one
 under any functor.  The comparison is the identity on objects and on
 arrows, so the split fork in [Cat] has Mac Lane's e, s and t at
 [eq_refl] ([arrow_fork_split_e], [arrow_fork_split_s],
 [arrow_fork_split_t]).
 A second split fork in [Cat], [arrow_fork_split_direct], is proved
 there directly: laws 2 to 4 hold in [Cat] with identity isomorphisms
 for components ([arrow_fork_law2_direct], [arrow_fork_law3_direct],
 [arrow_fork_law4_direct]), and law 1 is [arrow_fork_law1].  It has the
 same e, s and t ([arrow_fork_split_direct_e],
 [arrow_fork_split_direct_s], [arrow_fork_split_direct_t]), so the two
 differ only in their law fields, and that is where they differ in
 strength (STRENGTHS).  The pushed one is kept as the primary one,
 being the book's remark; the direct one is the one whose components
 compute.

 CONSEQUENCES, through Split.v and Absolute.v.  e is a coequalizer of
 ∂₀ and ∂₁ in [StrictCat] and in [Cat]
 ([arrow_fork_coequalizer_strict], [arrow_fork_coequalizer], by
 [split_coequalizer_is_coequalizer], the Lemma of p. 149).  The
 Corollary of p. 150 is stated at this fork through issue #477's
 predicate [AbsoluteCoequalizer] (Structure/Coequalizer/Absolute.v),
 which quantifies over the functors out of the category: e is an
 absolute coequalizer in [StrictCat] and in [Cat]
 ([arrow_fork_absolute_strict], [arrow_fork_absolute], by
 [split_coequalizer_absolute]).  Where Mac Lane's definition takes
 "any category X whatever", the targets here are the categories
 X : Category@{xo xh xh}, whose hom and proof levels coincide, as
 [IsCoequalizer] requires, with o <= xh (UNIVERSES).  At one target D
 and functor F, the Corollary says that F carries e to a coequalizer,
 which the file also states through Split.v's
 [split_coequalizer_preserved], for every functor out of either
 category into a D : Category@{do dh dh} with o <= dh
 ([arrow_fork_preserved_strict], [arrow_fork_preserved]); the two
 readings agree at [eq_refl] ([arrow_fork_preserved_absolute_strict],
 [arrow_fork_preserved_absolute]).  These are the first coequalizers
 stated in [Cat] or [StrictCat]: no other file states an
 [IsCoequalizer], a [SplitCoequalizer] or an [AbsoluteCoequalizer] at
 either (a grep of the tree), and Instance/Cat/Limit.v scopes
 coequalizers out.

 NOT EVERY SUCH FORK IS A COEQUALIZER.  This is not the book's; it
 shows that the hypothesis is not idle.  If C has no objects, e is not
 a coequalizer of ∂₀ and ∂₁ in [Cat] ([arrow_fork_not_coequalizer]):
 C² has no objects either, so the identity of C coforks the pair, and
 it would descend through e to a functor 1 ⟶ C, whose value is an
 object of C.  The empty category is such a C
 ([arrow_fork_not_coequalizer_0]).

 STRENGTHS, measured.  The two sides of laws 1, 3 and 4 agree at
 [eq_refl] on every object and every arrow ([arrow_fork_law1_obj],
 [arrow_fork_law1_map], [arrow_fork_law3_obj], [arrow_fork_law3_map],
 [arrow_fork_law4_obj], [arrow_fork_law4_map]), which by eta is to
 say that their object maps and their arrow maps are convertible as
 functions (six such equalities at [eq_refl], in a scratch compile).
 Those of law 2 agree at [eq_refl] at the object of 1 and at its
 identity arrow ([arrow_fork_law2_obj], [arrow_fork_law2_map]); at a
 variable object or arrow of 1 [eq_refl] is refused (R1 and R2 of
 Test/ProbeSplitFork478.v), and a case analysis is needed, [poly_unit]
 being an inductive type with no eta rule.  None of the four laws
 holds as a Leibniz equality of the two composite [Functor] records at
 [eq_refl] (R3 to R6): where their actions agree, their law fields are
 still different proof terms.  As equalities of functors, then, the
 laws are proved in the stricter of the tree's two setoids on
 functors, Theory/Functor.v's [Functor_StrictEq_Setoid], which is
 [StrictCat]'s ≈, against its [Functor_Setoid], natural isomorphism,
 which is [Cat]'s; the readbacks above say more, of the actions alone.
 In [Cat] it is the components of the isomorphisms that can
 compute, and in [arrow_fork_split] they do not: R8 refuses law 3's
 component as [id] at [eq_refl].  Its laws are the strict ones pushed
 along [StrictCat_to_Cat] by [functor_preserves_split], and [Eval cbv]
 of that component (in a scratch file) stops at opaque constants: the
 ones the setoid rewriting in [functor_preserves_split] goes through,
 the standard library's [CMorphisms] obligation
 [trans_co_eq_inv_arrow_morphism_obligation_1] and Theory/Functor.v's
 [Functor_Setoid_obligation_1], and the three obligations of
 [StrictCat_to_Cat], whose respects obligation calls
 Instance/StrictCat/ToCat.v's [strict_equiv_implies_fun_equiv].  That
 lemma does not occur in the normal form, so making it transparent
 would not make the components compute.  In [arrow_fork_split_direct]
 the components of laws 3 and 4 are [id] at [eq_refl] at every object
 ([arrow_fork_law3_direct_component],
 [arrow_fork_law4_direct_component]; C27 is R8's twin there), and law
 2's at the object of 1 (in a scratch compile); law 1's is not,
 [arrow_fork_law1] being closed with [Qed].  That lemma, the fork law
 in [Cat] for every C, is not read through [StrictCat] at all: it is
 [Cat_Terminal]'s [one_unique].
 Four proofs end [Qed]: [arrow_fork_law1], [arrow_fork_law1_strict],
 [arrow_fork_law2_strict] and [arrow_fork_not_coequalizer]; every
 other name is a transparent term.  The hypothesis of the splitting is
 met in the tree, by [Cat] itself among others (control C25 of the
 probe).

 UNIVERSES, read off [About] for all forty-five names, by script.
 Every name but [arrow_fork_not_coequalizer_0] binds o and h first,
 with C : Category@{o h h}: [Cat] and [StrictCat] take their objects
 at one hom and proof level (a scratch [Definition] of the coercion of
 a Category@{a b c} into [obj[Cat]] carries b = c).  Twenty-eight
 names carry h <= o: those with a binder C whose statements make C²
 and C objects of one [Cat] or [StrictCat] instance.  C² is then at
 the object level o, and its objects carry arrows of C, so o is at
 least h ([Arrow]'s own block bounds its object level below by its
 argument's hom level).  The other seventeen do not carry it; among
 them [arrow_fork_not_coequalizer_0], whose C is [_0], at hom level
 [Set], where the bound holds trivially.  R7 of the probe pins the
 bound: the fork cannot be stated at o < h.  The binders [@{o h +}]
 are load-bearing: with them removed, law 1 minimizes to
 C : Category@{u u u}, one level for objects, homs and proofs
 (measured in a scratch copy).  Only [arrow_fork_not_coequalizer_0]'s
 block mentions [Set], the hom level of Instance/Zero.v's [_0], which
 is a Category@{u Set Set}.  No block carries an equation.
 [arrow_fork_preserved] and [arrow_fork_preserved_strict] name the
 levels do and dh of the target D in their binders and carry o <= dh:
 Split.v's [split_coequalizer_preserved], whose binders #477 wrote
 out, lets the target's hom level sit above the source's, and the
 source here is [Cat] or [StrictCat], whose hom level is o.  Left
 unwritten, D's binders let minimization put D's hom level at o (D a
 Category@{u o o}, measured in a scratch compile).  Likewise
 [arrow_fork_absolute] and [arrow_fork_absolute_strict] name the
 target levels xo and xh and carry o <= xh, through the explicit
 universe instance [AbsoluteCoequalizer@{_ _ xo xh _}] in their
 statements, an instance of an existing constant and the only one the
 file writes outside its binders: left to Rocq, minimization sets the
 target's hom level to o ([AbsoluteCoequalizer@{u o u0 o u1}],
 measured in a scratch compile), as Absolute.v records for its
 [split_coequalizer_absolute].  No explicit universe instance of a new
 constant is written.

 STALE PREMISE.  Issue #478 (filed 2026-07-23) says that no
 construction assembles the pair dom, cod : C² ⇉ C, the fork to 1, or
 the splitting.  For the pair, that was accurate when filed and has
 been stale since PR #1134 (merged 2026-08-17), which named it
 [Arrow_dom] and [Arrow_cod] in Construction/Comma/Diagram.v; the pair
 is reused here.  The fork to 1 and its splitting were absent, as the
 issue says.

 CLOSURE.  The [Require]s load eighty-five [Category] modules
 ([Print Libraries]): thirty of them for Instance/Fun/Terminal.v,
 whose [Functor_Category_Terminal] supplies the transformation t
 classifies, and eleven for Structure/Coequalizer/Absolute.v, whose
 predicate states the Corollary, each figure being what dropping that
 one [Require] saves.  The cheapest variant not taken is a local
 transformation Id[C] ⟹ s ◯ e with components [one] and its two
 naturality squares by [one_unique], which compiles, every name
 closed, in a scratch copy without Instance/Fun/Terminal.v, at
 fifty-five modules.  CORRECTION (#480): eighty-six, thirty, twelve
 and fifty-six by the same counts, since Structure/Coequalizer/
 Absolute.v requires Structure/Coequalizer/Contractible.v.

 NOT DELIVERED.  Mac Lane's example in Grp and Exercise 1 are issue
 #479's.  Whether e is a coequalizer for some C that has objects but
 no terminal object is not examined; only categories without objects
 are shown to fall short.  A law 1 in [Cat] whose components compute:
 [arrow_fork_split_direct] reuses [arrow_fork_law1] rather than
 restate it. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，Springer GTM 5, 1998，第VI.6节，Cat中的叉例子，印刷版第150页（PDF第159页）—— maclane:VI.6:remark1；叉和分叉的定义在该节开头，印刷版第149页（PDF第158页）
 nLab: https://ncatlab.org/nlab/show/split+coequalizer
 nLab: https://ncatlab.org/nlab/show/arrow+category
 nLab: https://ncatlab.org/nlab/show/terminal+category书中所说的内容，从页面图像中阅读。在第149页："在一个范畴 C 中，叉（fork）是指如下图 a ⇉ b → c (1) 在 C 中的图，并且满足 e∂₀ = e∂₁"，以及 "在 C 中的分裂叉（split fork）是一个叉（1），并带有另外两个箭头 a ← b ← c (2)"，t 和 s，“它们与箭头 (1) 满足以下条件：e∂₀ = e∂₁、es = 1、∂₀t = 1、∂₁t = se。 (3)”。在第150页："由于分裂叉是由仅涉及复合和恒等映射的方程定义的，因此在应用任何函子时仍然是分裂叉。因此，推论：在每个分裂叉中，e 是 ∂₀ 和 ∂₁ 的绝对余等化子（absolute coequalizer）"。然后："这是一个在 Cat 中的叉的例子，对于任意范畴 C：C² ⇉ C → 1"，以及这一对 ∂₀、∂₁ 和箭头 e。C² 是一个范畴，其对象是 C 的箭头；∂₀ 和 ∂₁ 是函子，分别将每个箭头分配到它的定义域和陪域，而 e 是将 C 的每个对象映射到 1 的唯一对象的函子。如果 C 有终对象 a₀，则该叉由函子 s 分裂，s 将 1 的唯一对象映射到 a₀，以及函子 t，将每个 c ∈ C 映射到唯一的箭头 c → a₀。数据：重复使用四个部分，新增一个部分。C² 是 Construction/Arrow.v 的 [Arrow C]，逗号 (Id ↓ Id)。∂₀ 和 ∂₁ 是 Construction/Comma/Diagram.v 的 [Arrow_dom] 和 [Arrow_cod]，Mac Lane 在 §II.6 中的 ∂0 和 ∂1，在 S = T = Id 时的逗号投影。e 是 Instance/One.v 的 [Erase C]，它是 [Cat] 和 [StrictCat] 在 [eq_refl]（[arrow_fork_e_one]，[arrow_fork_e_one_strict]）处的终端映射。s 是 [Diagonal _1 a₀]，是 Functor/Diagonal.v 中从 1 出发的常值函子，即将 1 映射到 C 的函子挑选出 a₀，这就是 Instance/One/Diagonal.v 的读取方式，也是 Instance/Cat/Pullback.v 作为余抽取边使用的术语；它将 1 的对象映射到 [eq_refl]（[arrow_fork_s_obj]）处的 a₀。新的函子是 t，[arrow_fork_t]：Construction/Arrow/Functor.v 中的 [Arrow_intro]，Mac Lane 的练习 II.4.7 将自然变换解读为一个到 C² 的函子，应用于从 Id [C] 到函子范畴 [C, C] 的终对象的唯一箭头，常值函子在 a₀（Instance/Fun/Terminal.v 中的 [Functor_Category_Terminal]，根据该文件的描述，即 Mac Lane 的练习 III.5.5 在零元情形下）。因此 t c 是唯一的箭头 c → a₀（[arrow_fork_t_obj]），t f 是方格 (f, 1)（[arrow_fork_t_map]），两者都在 [eq_refl]。名称。Construction/Arrow/Functor.v，是 [Arrow_intro] 所需的，它有自己的 [Arrow_dom H] 和 [Arrow_cod H]，分别是函子 H 映入 C² 的边界。Construction/Comma/Diagram.v 在它之后被需要，因此下面的简写名称是 Diagram.v 的；这两对有不同的类型，所以混淆会导致类型错误，并且不能悄无声息地改变陈述的含义。四条定律。分叉是 Structure/Coequalizer/Split.v 的记录 [SplitCoequalizer]，其中 f := ∂₀，g := ∂₁，其四条定律是 Mac Lane 按其顺序的定律 (3)。它们在 [StrictCat] 中被证明，即教科书中的严格范畴的范畴，该范畴通过在每个对象处取值的等式来识别两个函子，其箭头映射在 ≈ ([Functor_StrictEq_Setoid]) 下是一致的：定律 1 和 2 因为任意两个映入 1 的函子严格相等（Instance/StrictCat/Terminal.v 的 [StrictCat_Terminal]），定律 3 和 4 则使用对象分量 [fun _ => eq_refl] 和箭头的自反性；它们的证明结尾于 [Defined]，这些分量在 [eq_refl] ([arrow_fork_law3_strict_component], [arrow_fork_law4_strict_component]) 被读回。定律 1 不需要终端对象，所以对每个 C，C² ⇉ C → 1 都是一个分叉，正如书中所说（[arrow_fork_law1_strict]；在 [Cat]、[arrow_fork_law1] 中，从 Instance/One.v 的 [Cat_Terminal]）。[StrictCat] 中的分裂分叉是 [arrow_fork_split_strict]。[Cat]、[arrow_fork_split] 中的那个，是通过 Split.v 的 [functor_preserves_split] 将 Instance/StrictCat/ToCat.v 的比较函子 [StrictCat_to_Cat] 推过来的：第 150 页的备注指出，分裂分叉由方程定义，在任何函子下仍然是分叉。这个比较函子在对象和箭头上是恒等的，所以 [Cat] 中的分裂分叉在 [eq_refl]（[arrow_fork_split_e]、[arrow_fork_split_s]、[arrow_fork_split_t]）处拥有 Mac Lane 的 e、s 和 t。一个在 [Cat] 中的第二个分叉 [arrow_fork_split_direct]，在那里直接被证明：在 [Cat] 中定律 2 到 4 成立，其分量（[arrow_fork_law2_direct]、[arrow_fork_law3_direct]、[arrow_fork_law4_direct]）为恒等同构，定律 1 是 [arrow_fork_law1]。它有相同的 e、s 和 t（[arrow_fork_split_direct_e]、[arrow_fork_split_direct_s]、[arrow_fork_split_direct_t]），因此两者仅在定律字段上不同，这就是它们在强度（STRENGTHS）上的差异。被推进的那个被保持为主要的，即书中的注释；直接的那个是其分量进行计算的那个。通过 Split.v 和 Absolute.v 得到的结果。e 是 [StrictCat] 和 [Cat] 中 ∂₀ 和 ∂₁ 的余等化子（[arrow_fork_coequalizer_strict]、[arrow_fork_coequalizer]，通过 [split_coequalizer_is_coequalizer]，第149页的引理）。第150页的推论在此分支中通过问题 #477 的谓词 [AbsoluteCoequalizer]（Structure/Coequalizer/Absolute.v）陈述，它对来自该范畴的函子进行量化：e 是 [StrictCat] 和 [Cat] 中的绝对余等化子（[arrow_fork_absolute_strict]、[arrow_fork_absolute]，通过 [split_coequalizer_absolute]）。在 Mac Lane 的定义中采用 "任何范畴 X"，这里的目标是范畴 X : Category@{xo xh xh}，其同态和证明等级一致，正如 [IsCoequalizer] 所要求的，其中 o <= xh（UNIVERSES）。在一个目标 D 和函子 F 上，推论指出 F 将 e 映射到一个余等化器，文件也通过 Split.v 的 [split_coequalizer_preserved] 说明了这一点，对于从任一范畴到 D : Category@{do dh dh} 且 o <= dh 的每个函子（[arrow_fork_preserved_strict], [arrow_fork_preserved]）；两种读法在 [eq_refl]（[arrow_fork_preserved_absolute_strict], [arrow_fork_preserved_absolute]）处一致。这些是在 [Cat] 或 [StrictCat] 中陈述的第一个余等化器：没有其他文件在任一处（通过树的 grep）陈述 [IsCoequalizer]、[SplitCoequalizer] 或 [AbsoluteCoequalizer]，并且 Instance/Cat/Limit.v 的作用域导出余等化器。并非每个这样的叉都是共等化器。这不是书上的内容；它表明该假设并非无用。如果 C 没有对象，那么 e 就不是 ∂₀ 和 ∂₁ 在 [Cat] ([arrow_fork_not_coequalizer]) 中的共等化器：C² 也没有对象，因此 C 的恒等函子叉化了这一对，并且它会通过 e 下行到一个函子 1 ⟶ C，其值是 C 的一个对象。空范畴就是这样的 C ([arrow_fork_not_coequalizer_0])。优势，已测量。定律 1、3 和 4 的两边在 [eq_refl] 上对每一个对象和每一个箭头（[arrow_fork_law1_obj], [arrow_fork_law1_map], [arrow_fork_law3_obj], [arrow_fork_law3_map], [arrow_fork_law4_obj], [arrow_fork_law4_map]）都一致，这通过 eta 表示它们的对象映射和箭头映射作为函数是可转换的（在 [eq_refl] 上有六个这样的等式，在一次临时编译中）。定律 2 的在 [eq_refl] 上对对象 1 及其恒等箭头（[arrow_fork_law2_obj], [arrow_fork_law2_map]）一致；在对象或箭头 1 的变量 [eq_refl] 上被拒绝（Test/ProbeSplitFork478.v 的 R1 和 R2），需要进行情况分析，[poly_unit] 是一个没有 eta 规则的归纳类型。这四条定律都不作为两个复合 [Functor] 记录在 [eq_refl]（R3 到 R6）处的莱布尼茨等式成立：即使它们的动作一致，它们的定律字段仍然是不同的证明项。作为函子等式，这些定律在树的两个函子集族中较严格的一个上被证明，即 Theory/Functor.v 的 [Functor_StrictEq_Setoid]，它是 [StrictCat] 的 ≈，与其 [Functor_Setoid] 的自然同构比较，其自然同构是 [Cat]；上面提到的回读仅说明动作本身。在 [Cat] 中，可以进行计算的是同构的分量，而在 [arrow_fork_split] 中则不行：R8 拒绝将定律 3 的分量作为 [id] 应用于 [eq_refl]。它的定律是由 [functor_preserves_split] 推动的严格定律 [StrictCat_to_Cat]，而该组件（在一个临时文件中）的 [Eval cbv] 在不透明常量处停止：即 [functor_preserves_split] 中集合重写所经过的那些常量，标准库的 [CMorphisms] 义务 [trans_co_eq_inv_arrow_morphism_obligation_1] 以及 Theory/Functor.v 的 [Functor_Setoid_obligation_1]，还有 [StrictCat_to_Cat] 的三个义务，其相关义务调用了 Instance/StrictCat/ToCat.v 的 [strict_equiv_implies_fun_equiv]。这个引理在正规形式中不存在，所以使其透明并不会让组件进行计算。在 [arrow_fork_split_direct] 中，第 3 和第 4 条定律的组成部分在每个对象（[arrow_fork_law3_direct_component], [arrow_fork_law4_direct_component]；C27 是 R8 在那里的对应）处都是 [id]，在 1 的对象处则是第 2 条定律（在临时编译中）；第 1 条定律则不是，[arrow_fork_law1] 被 [Qed] 关闭。这个引理，即在 [Cat] 中对于每个 C 的分叉律，完全没有通过 [StrictCat] 来阅读：它是 [Cat_Terminal] 的 [one_unique]。四个证明以 [Qed] 结束：[arrow_fork_law1]、[arrow_fork_law1_strict]、[arrow_fork_law2_strict] 和 [arrow_fork_not_coequalizer]；其他每个名字都是透明项。分裂的假设在树中得以满足，其中包括 [Cat] 自身（探针的控制 C25）。宇宙，请通过脚本读取 [About] 的全部四十五个名称。除了 [arrow_fork_not_coequalizer_0] 之外，每个名称首先绑定 o 和 h，使用 C ：Category@{o h h}：[Cat] 和 [StrictCat] 在同一个同态和证明层次上获取它们的对象（一个 [Definition] 的抓痕表示将 Category@{a b c} 强制转换为 [obj[Cat] 时 b = c）。二十八个名称承载 h <= o：那些拥有绑定器 C 且其陈述使得 C² 和 C 成为同一个 [Cat] 或 [StrictCat] 实例的对象。此时 C² 位于对象层 o，并且它的对象承载 C 的箭头，因此 o 至少为 h（[Arrow] 自身的块通过其参数的同态层将其对象层界定在更低处）。其他十七个名称不承载它；其中包括 [arrow_fork_not_coequalizer_0]，其 C 为 [_0]，位于同态层 [Set]，其中约束条件显然成立。探针的 R7 固定了绑定：叉子不能在 o < h 时被陈述。绑定器 [@{o h +}] 是承重的：移除它们后，定律 1 最小化为 C：Category@{u u u}，对象、homs 和证明各有一个层级（在临时拷贝中测量）。只有 [arrow_fork_not_coequalizer_0] 的区块提到了 [Set]，即 Instance/Zero.v 的 [_0] 的 hom 层级，它是 Category@{u Set Set}。没有区块携带方程。[arrow_fork_preserved] 和 [arrow_fork_preserved_strict] 在其绑定器中命名目标 D 的层级 do 和 dh，并携带 o <= dh：Split.v 的 [split_coequalizer_preserved]，其绑定器 #477 已经写出，让目标的 hom 层级位于源的上方，这里的源是 [Cat] 或 [StrictCat]，其 hom 层级为 o。未写出的情况下，D 的绑定器让最小化将 D 的 hom 层级设为 o（D 是 Category@{u o o}，在临时编译中测量）。同样地，[arrow_fork_absolute] 和 [arrow_fork_absolute_strict] 命名了目标级别 xo 和 xh，并通过它们声明中的显式宇宙实例 [AbsoluteCoequalizer@{_ _ xo xh _}] 载入 o <= xh，一个现有常量的实例，也是文件在其绑定器之外写入的唯一实例：留给 Rocq，最小化将目标的同调级别设置为 o（[AbsoluteCoequalizer@{u o u0 o u1}]，在临时编译中测量），正如 Absolute.v 为其 [split_coequalizer_absolute] 记录的那样。没有写入新常量的显式宇宙实例。过时的前提。第 478 号问题（提交于 2026-07-23）指出，没有任何构造可以组装对 dom, cod : C² ⇉ C、到 1 的叉或拆分。对于该对，提交时这是正确的，并且自 PR #1134（合并于 2026-08-17）以来一直过时，该 PR 在 Construction/Comma/Diagram.v 中将其命名为 [Arrow_dom] 和 [Arrow_cod]；这里再次使用该对。如问题所述，到 1 的叉及其拆分不存在。闭包。[Require] 加载了八十五个 [Category] 模块 ([Print Libraries])：其中三十个用于 Instance/Fun/Terminal.v，其 [Functor_Category_Terminal] 提供了转换 t 的分类，还有十一个位于 Structure/Coequalizer/Absolute.v，其中谓词陈述了推论，每个数字表示省略那个 [Require] 所节省的数量。未采用的最便宜变体是局部转换 Id [C] ⟹ s ◯ e，其组件为 [one] 及其由 [one_unique] 定义的两个自然性方格，该变体可以编译，每个名称都闭合，在没有 Instance/Fun/Terminal.v 的临时副本中，共五十五个模块。更正（#480）：八十六、三十、十二和五十六，按同样的计数，因为 Structure/Coequalizer/Absolute.v 需要 Structure/Coequalizer/Contractible.v。未交付。Mac Lane 在 Grp 中的例子和练习 1 是问题 #479。是否存在某个有对象但没有终对象的 C 的 e 是共同等化子尚未被考察；仅展示了没有对象的范畴会不足。一条在 [Cat] 中的定律，其组件计算：[arrow_fork_split_direct] 复用 [arrow_fork_law1]，而不是重新陈述它。
*)

(** ** The fork, for C any category / ** 叉子，对于 C 的任何类别 *)

(*
 e, the unique functor C ⟶ 1, is the terminal map of [Cat] and of
 [StrictCat] alike. 

 --------
 e，即从 C 到 1 的唯一函子，是 [Cat] 和 [StrictCat] 的终端映射。
*)
Example arrow_fork_e_one@{o h +} (C : Category@{o h h}) :
  Erase C = @one Cat Cat_Terminal C := eq_refl.

Example arrow_fork_e_one_strict@{o h +} (C : Category@{o h h}) :
  Erase C = @one StrictCat StrictCat_Terminal C := eq_refl.

(*
 Law 1, e ∂₀ = e ∂₁: both sides are functors into 1, so they agree in
 either category of categories. 

 --------
 定律 1，e ∂₀ = e ∂₁：两边都是到 1 的函子，因此它们在任一范畴的范畴中都相等。
*)
Lemma arrow_fork_law1@{o h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod.
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma arrow_fork_law1_strict@{o h +} (C : Category@{o h h}) :
  Erase C ∘[StrictCat] Arrow_dom ≈[StrictCat] Erase C ∘[StrictCat] Arrow_cod.
Proof. apply (@one_unique StrictCat StrictCat_Terminal). Qed.

(* ... and on the nose, on objects and on arrows. / ... 在鼻子上，物体上，以及箭上。 *)
Example arrow_fork_law1_obj@{o h +} (C : Category@{o h h}) (x : @Arrow C) :
  fobj[Erase C ◯ Arrow_dom] x = fobj[Erase C ◯ Arrow_cod] x := eq_refl.

Example arrow_fork_law1_map@{o h +} (C : Category@{o h h})
  {x y : @Arrow C} (f : x ~> y) :
  fmap[Erase C ◯ Arrow_dom] f = fmap[Erase C ◯ Arrow_cod] f := eq_refl.

(* * ** The splitting, given a terminal object a₀ of C / * ** 给定 C 的终对象 a₀ 的分解 *)

(* s, the functor 1 ⟶ C sending the object of 1 to a₀. / s，将单元素范畴 1 的对象发送到 a₀ 的函子 1 ⟶ C。 *)
Example arrow_fork_s_obj@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  (x : _1) :
  fobj[Diagonal _1 (@terminal_obj C T)] x = @terminal_obj C T := eq_refl.

(*
 t, the functor C ⟶ C² sending c to the unique arrow c → a₀: the
 classifying functor of the unique arrow from Id[C] to the terminal
 object of [C, C], the constant functor at a₀. 

 --------
 t，函子 C ⟶ C² 将 c 发送到唯一箭头 c → a₀：从 Id [C] 到 [C, C] 终对象的唯一箭头的分类函子，即常值函子 a₀。
*)
Definition arrow_fork_t@{o h +} {C : Category@{o h h}} `{T : @Terminal C} :
  C ⟶ @Arrow C :=
  Arrow_intro (Id[C]; (Constant_Terminal_Functor T;
                        @one _ (Functor_Category_Terminal T) Id[C])).

Example arrow_fork_t_obj@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  (c : C) :
  fobj[arrow_fork_t] c = ((c, @terminal_obj C T); @one C T c) := eq_refl.

Example arrow_fork_t_map@{o h +} {C : Category@{o h h}} `{T : @Terminal C}
  {c d : C} (f : c ~> d) :
  `1 (fmap[arrow_fork_t] f) = (f, @id C (@terminal_obj C T)) := eq_refl.

(* Law 2, e s = 1: two functors into 1 again. / 定律 2, e s = 1：两个函子再一次映射到 1。 *)
Lemma arrow_fork_law2_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[StrictCat] Diagonal _1 (@terminal_obj C T)
    ≈[StrictCat] @id StrictCat _1.
Proof. apply (@one_unique StrictCat StrictCat_Terminal). Qed.

(* Law 3, ∂₀ t = 1, with the object component [eq_refl]. / 定律3，∂₀ t = 1，物体分量 [eq_refl] 。 *)
Lemma arrow_fork_law3_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[StrictCat] arrow_fork_t ≈[StrictCat] @id StrictCat C.
Proof. exists (fun _ => eq_refl). intros; simpl; reflexivity. Defined.

(* Law 4, ∂₁ t = s e, with the object component [eq_refl]. / 定律 4, ∂₁ t = s e，带有对象组件 [eq_refl]。 *)
Lemma arrow_fork_law4_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[StrictCat] arrow_fork_t
    ≈[StrictCat] Diagonal _1 (@terminal_obj C T) ∘[StrictCat] Erase C.
Proof. exists (fun _ => eq_refl). intros; simpl; reflexivity. Defined.

(* ... and those object components, read back. / ... 并且那些对象组件，回读。 *)
Example arrow_fork_law3_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law3_strict C T) = fun _ => eq_refl := eq_refl.

Example arrow_fork_law4_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law4_strict C T) = fun _ => eq_refl := eq_refl.

(*
 Law 2 on the nose at the object of 1 and its arrow; for a variable
 object or arrow of 1 it needs a case analysis (see the header). 

 --------
 规律2准确针对1的对象及其箭头；对于1的可变对象或箭头，需要进行情况分析（见标题）。
*)
Example arrow_fork_law2_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] ttt = fobj[Id[_1]] ttt
  := eq_refl.

Example arrow_fork_law2_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] (@id _1 ttt)
    = fmap[Id[_1]] (@id _1 ttt) := eq_refl.

(* Laws 3 and 4 on the nose, on objects and on arrows. / 第3条和第4条，关于鼻子、关于物体以及关于箭头。 *)
Example arrow_fork_law3_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  fobj[Arrow_dom ◯ arrow_fork_t] c = fobj[Id[C]] c := eq_refl.

Example arrow_fork_law3_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} {c d : C} (f : c ~> d) :
  fmap[Arrow_dom ◯ arrow_fork_t] f = fmap[Id[C]] f := eq_refl.

Example arrow_fork_law4_obj@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  fobj[Arrow_cod ◯ arrow_fork_t] c
    = fobj[Diagonal _1 (@terminal_obj C T) ◯ Erase C] c := eq_refl.

Example arrow_fork_law4_map@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} {c d : C} (f : c ~> d) :
  fmap[Arrow_cod ◯ arrow_fork_t] f
    = fmap[Diagonal _1 (@terminal_obj C T) ◯ Erase C] f := eq_refl.

(* The split fork in StrictCat: Split.v's record, f := ∂₀ and g := ∂₁. / StrictCat 中的分叉叉子：Split.v 的记录，f := ∂₀ 和 g := ∂₁。 *)
Definition arrow_fork_split_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer StrictCat (@Arrow C) C Arrow_dom Arrow_cod :=
  @Build_SplitCoequalizer StrictCat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) (Diagonal _1 (@terminal_obj C T)) arrow_fork_t
    (arrow_fork_law1_strict C) arrow_fork_law2_strict
    arrow_fork_law3_strict arrow_fork_law4_strict.

(*
 The split fork in Cat: the one in StrictCat, pushed along the
 comparison functor StrictCat ⟶ Cat, which is the identity on objects
 and on arrows. 

 --------
 在 Cat 中的分叉：在 StrictCat 中的那个，通过比较函子 StrictCat ⟶ Cat 推动，该函子在对象和箭头上都是恒等的。
*)
Definition arrow_fork_split@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod :=
  functor_preserves_split StrictCat_to_Cat _ _ arrow_fork_split_strict.

(* ... whose e, s and t are Mac Lane's. / ... 其 e、s 和 t 是麦克莱恩的。 *)
Example arrow_fork_split_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e arrow_fork_split = Erase C := eq_refl.

Example arrow_fork_split_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s arrow_fork_split = Diagonal _1 (@terminal_obj C T) := eq_refl.

Example arrow_fork_split_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t arrow_fork_split = arrow_fork_t := eq_refl.

(* * ** The split fork in Cat, directly / * ** 猫的分叉，直接 *)

(*
 Laws 2 to 4 proved in Cat itself, each natural isomorphism having
 identities for components; law 1 is [arrow_fork_law1]. 

 --------
 第2到第4条定律已在Cat本身中得到证明，每个自然同构都有分量的恒等式；第1条定律是[arrow_fork_law1]。
*)
Lemma arrow_fork_law2_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[Cat] Diagonal _1 (@terminal_obj C T) ≈[Cat] @id Cat _1.
Proof.
  unshelve eexists.
  - intros []; exact iso_id.
  - intros [] [] []; simpl; reflexivity.
Defined.

Lemma arrow_fork_law3_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[Cat] arrow_fork_t ≈[Cat] @id Cat C.
Proof. exists (fun _ => iso_id). intros; simpl; cat. Defined.

Lemma arrow_fork_law4_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[Cat] arrow_fork_t
    ≈[Cat] Diagonal _1 (@terminal_obj C T) ∘[Cat] Erase C.
Proof. exists (fun _ => iso_id). intros; simpl; cat. Defined.

(* The components of laws 3 and 4 are identities on the nose. / 法律3和4的组成部分完全是相同的。 *)
Example arrow_fork_law3_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law3_direct C T) c) = id := eq_refl.

Example arrow_fork_law4_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law4_direct C T) c) = id := eq_refl.

(* The split fork they make, with the same e, s and t. / 他们制造的分叉，与相同的 e、s 和 t。 *)
Definition arrow_fork_split_direct@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod :=
  @Build_SplitCoequalizer Cat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) (Diagonal _1 (@terminal_obj C T)) arrow_fork_t
    (arrow_fork_law1 C) arrow_fork_law2_direct
    arrow_fork_law3_direct arrow_fork_law4_direct.

Example arrow_fork_split_direct_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e arrow_fork_split_direct = Erase C := eq_refl.

Example arrow_fork_split_direct_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s arrow_fork_split_direct = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

Example arrow_fork_split_direct_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t arrow_fork_split_direct = arrow_fork_t := eq_refl.

(* * ** Consequences, through Structure/Coequalizer/Split.v and Absolute.v / * ** 通过 Structure/Coequalizer/Split.v 和 Absolute.v 的结果 *)

(* e is a coequalizer of ∂₀ and ∂₁: the Lemma of §VI.6. / e 是 ∂₀ 和 ∂₁ 的余等化子：见 §VI.6 的引理。 *)
Definition arrow_fork_coequalizer_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @IsCoequalizer StrictCat _ _ Arrow_dom Arrow_cod _1 (Erase C) :=
  split_coequalizer_is_coequalizer _ _ arrow_fork_split_strict.

Definition arrow_fork_coequalizer@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase C) :=
  split_coequalizer_is_coequalizer _ _ arrow_fork_split.

(*
 ... and every functor out of StrictCat or out of Cat into a
 D : Category@{do dh dh} with o <= dh carries it to a coequalizer. 

 --------
 ... 并且从 StrictCat 或从 Cat 到一个 D : Category@{do dh dh}（其中 o <= dh）的每个函子都会将其映射到一个余等化器。
*)
Definition arrow_fork_preserved_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  IsCoequalizer (fmap[F] Arrow_dom) (fmap[F] Arrow_cod)
    (F _1) (fmap[F] (Erase C)) :=
  split_coequalizer_preserved F _ _ arrow_fork_split_strict.

Definition arrow_fork_preserved@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  IsCoequalizer (fmap[F] Arrow_dom) (fmap[F] Arrow_cod)
    (F _1) (fmap[F] (Erase C)) :=
  split_coequalizer_preserved F _ _ arrow_fork_split.

(* The Corollary of p. 150, "In every split fork, e is an absolute coequalizer of ∂₀ and ∂₁", at this fork: Absolute.v's predicate. / 第150页的推论，“在每个分裂叉中，e 是 ∂₀ 和 ∂₁ 的绝对共同等化子”，在这个叉：Absolute.v 的谓词。 *)
Definition arrow_fork_absolute_strict@{o h xo xh +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @AbsoluteCoequalizer@{_ _ xo xh _} StrictCat (@Arrow C) C Arrow_dom
    Arrow_cod _1 (Erase C) :=
  split_coequalizer_absolute arrow_fork_split_strict.

Definition arrow_fork_absolute@{o h xo xh +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  @AbsoluteCoequalizer@{_ _ xo xh _} Cat (@Arrow C) C Arrow_dom Arrow_cod
    _1 (Erase C) :=
  split_coequalizer_absolute arrow_fork_split.

(* The two corollaries above are the Corollary, applied to D and F. / 上述两个推论是推广到 D 和 F 的推论。 *)
Example arrow_fork_preserved_absolute_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  @arrow_fork_preserved_strict C T D F = @arrow_fork_absolute_strict C T D F
  := eq_refl.

Example arrow_fork_preserved_absolute@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  @arrow_fork_preserved C T D F = @arrow_fork_absolute C T D F := eq_refl.

(* * ** Not every such fork is a coequalizer / * ** 并非每一个这样的叉都是余等化子 *)

(*
 If C has no objects, neither has C², so the identity of C coforks ∂₀
 and ∂₁; were e a coequalizer, it would descend through e to a functor
 1 ⟶ C, whose value is an object of C. 

 --------
 如果 C 没有对象，那么 C² 也没有对象，因此 C 的恒等函子共同分叉 ∂₀ 和 ∂₁；如果 e 是一个共等化器，它将通过 e 下行到一个函子 1 ⟶ C，其取值是 C 的一个对象。
*)
Lemma arrow_fork_not_coequalizer@{o h +} (C : Category@{o h h})
  (empty : C → False) :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase C) → False.
Proof.
  intros E.
  assert (H : @id Cat C ∘[Cat] Arrow_dom ≈[Cat] @id Cat C ∘[Cat] Arrow_cod).
  { unshelve eexists.
    - intros [[x y] f]. contradiction (empty x).
    - intros [[x y] f]. contradiction (empty x). }
  destruct (coeq_desc E (@id Cat C) H) as [u _ _].
  exact (empty (fobj[u] ttt)).
Qed.

(* The empty category is such a C. / 空类别就是这样的 C。 *)
Example arrow_fork_not_coequalizer_0 :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase _0) → False :=
  arrow_fork_not_coequalizer _0 (fun x => match x with end).
