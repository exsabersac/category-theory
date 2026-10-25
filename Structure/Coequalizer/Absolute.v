Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Absolute.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Contractible.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Lift.

Generalizable All Variables.

(** * Absolute coequalizers / * 绝对共等化器 *)

(*
 Book:   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §VI.6 "Split Coequalizers", book p. 149 (PDF p. 158), item
 maclane:VI.6:def2, read from the page image
 Paper:  Paré, "On absolute colimits", J. Algebra 19 (1971) 80-95
 nLab:   https://ncatlab.org/nlab/show/absolute+colimit
 nLab:   https://ncatlab.org/nlab/show/split+coequalizer

 WHAT THE BOOK SAYS.  "An arrow e is called an absolute coequalizer of
 ∂₀ and ∂₁ in C if for any functor T: C → X (to any category X
 whatever) the resulting fork Ta ⇉ Tb → Tc still has Te a coequalizer
 (of T∂₀ and T∂₁).  In particular, an absolute coequalizer is
 automatically a coequalizer."  A split fork adds s : c → b and
 t : b → a with e∂₀ = e∂₁, es = 1, ∂₀t = 1 and ∂₁t = se, and the
 Lemma: "In every split fork, e is the coequalizer of ∂₀ and ∂₁", by
 f' = fs, unique since f = ke gives fs = kes = k.

 WHAT IS HERE.
 - [AbsoluteCoequalizer f g q e]: for every category X and functor
 T : C ⟶ X, [IsCoequalizer (fmap[T] f) (fmap[T] g) (T q)
 (fmap[T] e)].  Mac Lane's definition over the tree's elementary
 [IsCoequalizer] (Structure/Coequalizer.v), the form the tree
 consumes: before #477, 27 files outside doc/ and Test/ name it
 (git grep -lw), Monad/Monadicity's Beck.v, BeckObjects.v and
 Crude.v among them, against 2 that name the bundled
 [Coequalizer (APair f g)].  Like the
 issue's statement it quantifies only; Mac Lane's presupposed fork
 is the [cofork] field of the T := Id instance.
 - [AbsoluteCoequalizer_IsCoequalizer]: "automatically a
 coequalizer", the instance T := Id, whose type is
 [IsCoequalizer f g q e] by conversion.
 - The instances are ordered: through Construction/Lift.v's
 [LiftCat], which re-reads a category at higher universe levels,
 an instance at target levels (yo, yh) implies the instance at
 every (xo, xh) below them ([AbsoluteCoequalizer_down]), and an
 instance at any levels at or above C's own is a coequalizer in C,
 its cofork included ([AbsoluteCoequalizer_IsCoequalizer_up]), so
 "automatically a coequalizer" holds from every such instance.
 - Mac Lane's Lemma is Structure/Coequalizer/Split.v's
 [split_coequalizer_is_coequalizer], whose proof is the book's:
 the descent is h ∘ s, and e ∘ s ≈ id makes it unique (Split.v's
 laws are Mac Lane's (3) with f, g for ∂₀, ∂₁).
 [split_coequalizer_absolute]: every split fork is absolute,
 Split.v's [split_coequalizer_preserved] read as the predicate.
 - The image bridge, per functor: [image_coequalizer_colimit] and
 [image_colimit_coequalizer] turn an elementary coequalizer of the
 image pair into a colimiting image cocone over [T ◯ APair f g]
 and back.  Both are Structure/Coequalizer.v's diagram-general
 conversions ([parallel_coequalizer_colimit],
 [parallel_colimit_coequalizer], #477) at [K := T ◯ APair f g]:
 the second by conversion, the first through a cone isomorphism
 whose apex map is the identity.  The tree records three times
 (Monad/Monadicity/Crude.v, Monad/Eilenberg/Moore/Limit.v,
 Adjunction/Continuity/Equalizer.v) that [T ◯ APair f g] is not
 identified with [APair (fmap[T] f) (fmap[T] g)]; the general
 conversions make that identification unnecessary on the
 coequalizer side, by case analysis on the two objects of
 [Parallel], and Continuity/Equalizer.v's equalizer side is not
 met.
 - The agreement: for a cofork [H : e ∘ f ≈ e ∘ g],
 [AbsoluteCoequalizer_AbsoluteColimitCocone] and
 [AbsoluteColimitCocone_AbsoluteCoequalizer] carry the predicate
 to Structure/Limit/Absolute.v's [AbsoluteColimitCocone] of the
 cofork cocone [cofork_cocone f g e H] and back, so the absolute
 coequalizer IS the cofork-shaped absolute colimit, instance by
 instance at the cocone side's hom level (UNIVERSES).
 - Split forks at cone level: [split_cofork_AbsoluteColimitCocone],
 and [split_coequalizer_PreservesColimitCocone]: every functor
 preserves, in the cone sense, EVERY coequalizer of a pair that
 has a split coequalizer, not just the given one.
 - Contractible pairs (#480): [contractible_coequalizer_absolute],
 every coequalizer of a contractible pair is absolute, by
 [split_coequalizer_absolute] applied to Structure/Coequalizer/
 Contractible.v's [contractible_coequalizer_split], which splits
 it; on Rocq 9.1.1 its [About] block is that of
 [split_coequalizer_absolute].  It is stated here, this file
 requiring Contractible.v, so that Contractible.v does not load
 this file's closure.

 STRENGTHS.  The image cocone's injections are [fmap[T] (e ∘ f)] over
 [ParX] and [fmap[T] e] over [ParY] at [eq_refl]
 ([image_cofork_inj_ParX], [image_cofork_inj_ParY]); over [ParX] it is
 not [fmap[T] e ∘ fmap[T] f] at [eq_refl] (refused in the probe), which
 is the [fmap_comp] step of [image_coequalizer_colimit]'s cone
 isomorphism.  The descent built by [image_colimit_coequalizer] IS the
 colimit's mediator at the cofork cocone of the coforking map
 ([image_colimit_coequalizer_desc], [eq_refl]).  The three [Example]s
 are restated in the probe.

 UNIVERSES, by [About] on every constant.  [AbsoluteCoequalizer@{co ch
 xo xh u}] is over [C : Category@{co ch ch}] and quantifies over
 [X : Category@{xo xh xh}] with "ch <= xh" and no equation: every
 target whose hom level is at or above C's, a universe-polymorphic
 family with the predicate's sort [u] strictly above [xo] and [xh].
 That is as general as [Functor] allows in the hom level; the target's
 proof level is its hom level, as [IsCoequalizer@{u u0}], over
 [Category@{u u0 u0}], requires, where [Functor] would allow it above.
 It is more general than the cone-level predicate, whose targets share
 C's hom level by three carriers that Structure/Limit/Absolute.v
 names: Preservation.v's [cone_leg] and [IsLimitCone], [Compose], and
 for cocones [Opposite_Functor].
 Two consequences were measured.  First, Split.v's
 [functor_preserves_split] and [split_coequalizer_preserved] read
 [@{u u0 u1 u2}] over [C : Category@{u1 u2 u2}] and
 [D : Category@{u u2 u2}], one hom level for both, so absoluteness of
 a split fork reached only targets at C's hom level; the same proofs
 compile with the target's hom level strictly above, and #477 writes
 their binders out ([@{co ch do dh u}], "ch <= dh").  Second, with
 that done, [split_coequalizer_absolute] still came out at
 [AbsoluteCoequalizer@{co ch u0 ch u}]: minimization set the target
 hom level, bounded below by [ch] alone, to [ch].  So its statement
 names the instance, [AbsoluteCoequalizer@{co ch xo xh _}]; it now
 reads "ch <= xh", and the probe accepts it with "ch < xh" strict.
 [AbsoluteCoequalizer_IsCoequalizer_up@{co ch xo xh u}] carries
 "co <= xo" and "ch <= xh", and
 [AbsoluteCoequalizer_down@{co ch xo xh yo yh …}] "xo <= yo" and
 "xh <= yh", with no equation, and their statements name the instances
 they consume and produce for the same reason: four explicit universe
 instances of a new constant in this file, in three constants.
 (CORRECTION (#480): five, in four constants, since #480's
 [contractible_coequalizer_absolute] names its instance for the same
 reason.)
 [AbsoluteCoequalizer_IsCoequalizer] consumes the instance
 [@{co ch co ch u}], X at C's own levels: "take T := Id".  The probe
 refuses it from a target hom level above C's at C's own object level
 (R6), a pin of that lemma's signature and not of what the predicate
 yields: R6's statement is accepted through
 [AbsoluteCoequalizer_IsCoequalizer_up] (C26) and through
 [AbsoluteCoequalizer_down] (C27).  The agreement lemmas pair
 [AbsoluteCoequalizer@{co ch u ch u0}] with the cocone predicate at
 the same target object level [u]: at a target hom level above C's the
 cone-level side does not exist, and through
 [AbsoluteCoequalizer_down] any elementary instance at or above
 (u, ch) feeds them.  They take the cofork [H] as an argument because
 their target object level [u] is unrelated to C's and may lie below
 it, where no instance returns the cofork; at or above C's levels
 [AbsoluteCoequalizer_IsCoequalizer_up] does.

 STALE PREMISES, dated from gh.  The issue (filed 2026-07-23, Riehl's
 box appended 2026-07-31) says that a grep for [Absolute*] declarations
 returns nothing and that no [Absolute*] identifier exists: accurate
 when written, stale since PR #1229 (merged 2026-08-31, for #356),
 whose Structure/Limit/Constant.v declares the apex-only
 [AbsoluteLimit] and [AbsoluteColimit].  Its optional [AbsoluteColimit]
 is delivered at cone level as [AbsoluteColimitCocone], those names
 being taken.  Its line citations are replaced by names here.  "Beck's
 condition (ii) cannot be phrased" was accurate until this change; it
 can now be phrased, and issue #484 (open) is to phrase it.

 NOT DELIVERED.  An elementary [AbsoluteEqualizer]: the limit side is
 [AbsoluteLimitCone] at the walking parallel pair, and Mac Lane names
 only the coequalizer.  The equalizer twin of Structure/Coequalizer.v's
 diagram-general conversions.  Paré's converse direction (an absolute
 coequalizer is split in his generalized sense).  A concrete absolute
 coequalizer that is not split, and a concrete coequalizer that is not
 absolute (the non-vacuity witnesses of Structure/Limit/Absolute.v are
 of the empty shape).  Beck's theorem with the absolute condition
 (issue #484) and Riehl's split idempotents (issue #957). 

 --------
 书籍：Mac Lane, 《为在职数学家准备的范畴论》，第二版，
 §VI.6 “拆分的余等化子”，书中第149页（PDF第158页），条目
 maclane:VI.6:def2，从页面图像阅读
 论文：Paré, 《关于绝对余极限》，J. Algebra 19 (1971) 80-95
 nLab：https://ncatlab.org/nlab/show/absolute+colimit 
 nLab：https://ncatlab.org/nlab/show/split+coequalizer 

 书中内容：“如果对于任何函子 T: C → X（至任意类别 X）产生的叉形 Ta ⇉ Tb → Tc 仍然有 Te 是 T∂₀ 和 T∂₁ 的余等化子，那么箭头 e 称为 C 中 ∂₀ 和 ∂₁ 的绝对余等化子。特别地，绝对余等化子自动是一个余等化子。” 拆分叉形增加了 s : c → b 和 t : b → a，使得 e∂₀ = e∂₁，es = 1，∂₀t = 1 和 ∂₁t = se，并且引理：“在每个拆分叉形中，e 是 ∂₀ 和 ∂₁ 的余等化子”，由 f' = fs 给出，唯一性因为 f = ke 得到 fs = kes = k。这里是什么。- [AbsoluteCoequalizer f g q e]：对于每个范畴 X 和函子 T : C ⟶ X，[IsCoequalizer (fmap[T] f) (fmap [T] g) (T q) (fmap [T] e)]。根据 Mac Lane 对树的基本 [IsCoequalizer] (Structure/Coequalizer.v) 的定义，树消耗的形式：在 #477 之前，doc/ 和 Test/ 之外的 27 个文件使用它来命名 (git grep -lw)，包括 Monad/Monadicity 的 Beck.v、BeckObjects.v 和 Crude.v，在这 2 个之外命名捆绑的 [Coequalizer (APair f g)]。如问题陈述所述，它仅量化；Mac Lane 假设的分叉是 T := Id 实例的 [cofork] 字段。- [AbsoluteCoequalizer_IsCoequalizer]：“自动的一个等变子”，实例 T := Id，其类型通过转换为 [IsCoequalizer f g q e]。- 实例的排列顺序是：通过 Construction/Lift.v 的 [LiftCat]，它在更高的宇宙层级重新读取一个范畴，在目标层级 (yo, yh) 的实例意味着在每个低于它们的层级 (xo, xh) 中都有该实例 ([AbsoluteCoequalizer_down])，而在 C 自身或以上任意层级的实例是 C 中的余等化子，其余分岔包含在内 ([AbsoluteCoequalizer_IsCoequalizer_up])，因此“自动余等化子”从每个此类实例中成立。 - Mac Lane 的引理是 Structure/Coequalizer/Split.v 的 [split_coequalizer_is_coequalizer]，其证明与书本一致：下降映射是 h ∘ s，且 e ∘ s ≈ id 使其唯一 (Split.v 的公理是 Mac Lane 的 (3)，对 ∂₀, ∂₁ 用 f, g)。[split_coequalizer_absolute]：每个分裂分叉都是绝对的，Split.v 的 [split_coequalizer_preserved] 被读取为谓词。- 图像桥，对于函子：[image_coequalizer_colimit] 和 [image_colimit_coequalizer]，将图像对的基本共同等化器转化为 [T ◯ APair f g] 上的余极限图像锥，反之亦然。两者都是 Structure/Coequalizer.v 中的图示通用转换（[parallel_coequalizer_colimit]，[parallel_colimit_coequalizer]，#477）在 [K := T ◯ APair f g] 处：第二个通过转换，第一个通过一个顶点映射为恒等映射的锥同构。该树记录了三次
 (Monad/Monadicity/Crude.v, Monad/Eilenberg/Moore/Limit.v,
 Adjunction/Continuity/Equalizer.v)，表明 [T ◯ APair f g] 并未被识别为 [APair (fmap[T] f) (fmap [T] g)；一般的转换使得在等价子器（coequalizer）一侧无需进行该识别，通过对 [Parallel] 的两个对象进行情况分析，而 Continuity/Equalizer.v 的等值器一侧未被满足。- 一致性：对于一个共叉（cofork） [H : e ∘ f ≈ e ∘ g]，[AbsoluteCoequalizer_AbsoluteColimitCocone] 和 [AbsoluteColimitCocone_AbsoluteCoequalizer] 将谓词传递到 Structure/Limit/Absolute.v 的 [AbsoluteColimitCocone] 的共叉余圆（cofork cocone） [cofork_cocone f g e H] 并返回，因此绝对等价子器（absolute coequalizer）确实是共叉形状的绝对余极限（absolute colimit），在余圆一侧的同态（hom）水平（UNIVERSES）上实例逐一进行。- 在锥层面上分裂叉：[split_cofork_AbsoluteColimitCocone] 和 [split_coequalizer_PreservesColimitCocone]：每个函子在锥意义上保持每一对具有分裂余等化子的对的所有余等化子，而不仅仅是给定的那个。  
 - 可收缩的对（#480）：[contractible_coequalizer_absolute]，每个可收缩对的余等化子都是绝对的，通过将 [split_coequalizer_absolute] 应用于 Structure/Coequalizer/Contractible.v 的 [contractible_coequalizer_split]，它将其分裂；在 Rocq 9.1.1 上，它的 [About] 块是 [split_coequalizer_absolute]。这里声明了这一点，本文件需要 Contractible.v，因此 Contractible.v 不会加载本文件的闭包。优势。图像余锥的注入是  [fmap[T]  (e ∘ f)] 在 [ParX] 上以及 [fmap[T] e] 在 [ParY] 于 [eq_refl] ([image_cofork_inj_ParX], [image_cofork_inj_ParY])；在 [ParX] 上它不是 [fmap[T] e ∘ fmap [T] f] 于 [eq_refl]（在探针中被拒绝），这是 [fmap_comp] 步骤的 [image_coequalizer_colimit] 锥同构。由 [image_colimit_coequalizer] 构建的下降确实是余叉映射（[image_colimit_coequalizer_desc], [eq_refl]）的余叉锥上余极限的中介。三个 [Example] 已在探针中重述。UNIVERSES，由 [About] 关于每个常数。 [AbsoluteCoequalizer@{co ch xo xh u}] 位于 [C : Category@{co ch ch}] 之上，并且量化 [X : Category@{xo xh xh}]，条件为“ch <= xh”，且没有等式：每个同伦级别在或高于 C 的目标，一个带谓词的 universe 多态族，其谓词的类型 [u] 严格高于 [xo] 和 [xh]。在同伦级别上，这与 [Functor] 所允许的一样通用；目标的证明级别即其同伦级别，正如 [IsCoequalizer@{u u0}] 所要求的那样，在 [Category@{u u0 u0}] 之上，其中 [Functor] 会允许它更高。它比锥级谓词更通用，锥级谓词的目标通过由 Structure/Limit/Absolute.v 命名的三个载体共享 C 的同伦级别：Preservation.v 的 [cone_leg] 和 [IsLimitCone]、[Compose]，以及对于余锥的 [Opposite_Functor]。测量了两个结果。首先，Split.v 的 [functor_preserves_split] 和 [split_coequalizer_preserved] 读取 [@{u u0 u1 u2}] 通过 [C : Category@{u1 u2 u2}] 和 [D : Category@{u u2 u2}] ，两者的同质级别相同，因此分叉的绝对性仅在 C 的同质级别处达到目标；相同的证明在目标的同质级别严格高于时也能编译，且 #477 将它们的绑定器写出（[@{co ch do dh u}]，“ch <= dh”）。其次，在完成这些之后，[split_coequalizer_absolute] 仍然结果为 [AbsoluteCoequalizer@{co ch u0 ch u}] ：最小化设置了目标同质级别，仅以 [ch] 为下界，至 [ch] 。因此它的声明命名为实例 [AbsoluteCoequalizer@{co ch xo xh _}]；现在它读取为“ch <= xh”，探针接受它，并为“ch < xh”严格要求。[AbsoluteCoequalizer_IsCoequalizer_up@{co ch xo xh u}] 包含 “co <= xo” 和 “ch <= xh”，而 [AbsoluteCoequalizer_down@{co ch xo xh yo yh …}] 包含 “xo <= yo” 和 “xh <= yh”，没有方程，它们的声明命名了它们消耗和生成的实例，原因相同：在该文件中的三个位点的一个新常量的四个显式宇宙实例。（更正 (#480)：五个，在四个常量中，因为 #480 的 [contractible_coequalizer_absolute] 也出于相同原因命名其实例。）[AbsoluteCoequalizer_IsCoequalizer] 在 C 自己的层级消耗实例 [@{co ch co ch u}], X：“take T := Id”。探针拒绝它来自高于 C 自己对象层级的目标 hom 层级（R6），这是该引理签名的一个锚点，而不是谓词输出的内容：R6 的声明通过 [AbsoluteCoequalizer_IsCoequalizer_up]（C26）和 [AbsoluteCoequalizer_down]（C27）被接受。该协议引理将 [AbsoluteCoequalizer@{co ch u ch u0}] 与同一目标对象级别上的余锥谓词配对 [u]：在高于 C 的目标同伦级别上，锥级别一侧不存在，并且通过 [AbsoluteCoequalizer_down]，任何位于 (u, ch) 或以上的基本实例都能为它们提供数据。它们将余叉 [H] 作为参数，因为它们的目标对象级别 [u] 与 C 的无关，并且可能位于其下方，在那里没有实例返回余叉；在 C 的级别或其之上 [AbsoluteCoequalizer_IsCoequalizer_up] 会返回。过期的前提，起始于 gh。该问题（提交于 2026-07-23，Riehl 的箱子附加于 2026-07-31）指出对 [Absolute*] 声明的 grep 返回为空，并且不存在 [Absolute*] 标识符：撰写时准确，自 PR #1229（合并于 2026-08-31，为 #356）以来已经过时，其 Structure/Limit/Constant.v 声明了仅限顶点的 [AbsoluteLimit] 和 [AbsoluteColimit]。其可选的 [AbsoluteColimit] 在圆锥层级以 [AbsoluteColimitCocone] 交付，这些名字已被使用。这里将其行引用替换为名称。“Beck 的条件 (ii) 无法表述”在此更改之前是准确的；现在可以表述该条件，且问题 #484（未解决）是用于表述它。未交付。一个初等的 [AbsoluteEqualizer]：极限侧是 [AbsoluteLimitCone] 在行走平行对，Mac Lane 只命名余等化器。Structure/Coequalizer.v 的图形一般转换的等化器孪生。Paré 的逆方向（在他广义的意义下，绝对余等化器是可分的）。一个具体的绝对余等化器，它不是可分的，以及一个具体的余等化器，它不是绝对的（Structure/Limit/Absolute.v 的非空性证据是空形状的）。带有绝对条件的 Beck 定理（问题 #484）和 Riehl 的可分幂等（问题 #957）。
*)

(* * ** The predicate, and Mac Lane's two remarks / * ** 谓词，以及麦克·莱恩的两条评论 *)

Definition AbsoluteCoequalizer@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} (f g : x ~> y) (q : C) (e : y ~> q) :
  Type :=
  ∀ (X : Category@{xo xh xh}) (T : C ⟶ X),
    IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e).

Definition AbsoluteCoequalizer_IsCoequalizer@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer f g q e) : IsCoequalizer f g q e :=
  A C Id.

(* The instance is named: left to Rocq, minimization sets the target's hom level [xh] to [ch], its only lower bound. / 该实例命名为：left to Rocq，最小化将目标的 hom 水平 [xh] 设置为 [ch]，这是它唯一的下界。 *)

Definition split_coequalizer_absolute@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) :
  AbsoluteCoequalizer@{co ch xo xh _} f g (scoeq_obj S) (scoeq_e S) :=
  fun X T => split_coequalizer_preserved T f g S.

(* * ** Every instance at or above C's levels: the lift / * ** 每个达到或高于C级别的实例：提升 *)

(*
 An absolute coequalizer at ANY target level at or above C's is a
 coequalizer in C, its cofork included: C is read at that level by
 Construction/Lift.v's [LiftCat], and [Lift_in C] plays the part of
 [Id].  The instance of the hypothesis is named, its target levels
 being bounded below by C's alone. 

 --------
 在任何等于或高于 C 的目标层次上的绝对共等化器是 C 中的共等化器，其共分叉包含在内：在 Construction/Lift.v 中的 [LiftCat] 在该层次读取 C，而 [Lift_in C] 扮演 [Id] 的角色。假设的实例已命名，其目标层次仅受 C 的下界限制。
*)

Definition AbsoluteCoequalizer_IsCoequalizer_up@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer@{co ch xo xh _} f g q e) :
  IsCoequalizer f g q e.
Proof.
  pose (E := A (LiftCat C) (Lift_in C)).
  unshelve econstructor.
  - exact (cofork E).
  - intros z h Hh.
    pose (U := coeq_desc E (z := z) h Hh).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U).
    + intros v Hv. exact (uniqueness U v Hv).
Defined.

(*
 Each instance implies every lower one: a target X below the
 hypothesis' levels is read at them, and [Lift_after T] replaces T. 

 --------
 每个实例都意味着每个低层次：位于假设层次以下的目标 X 在它们上面被读取，[Lift_after T] 替换 T。
*)

Definition AbsoluteCoequalizer_down@{co ch xo xh yo yh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (A : AbsoluteCoequalizer@{co ch yo yh _} f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e.
Proof.
  intros X T.
  pose (E := A (LiftCat X) (Lift_after T)).
  unshelve econstructor.
  - exact (cofork E).
  - intros z h Hh.
    pose (U := coeq_desc E (z := z) h Hh).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U).
    + intros v Hv. exact (uniqueness U v Hv).
Defined.

(* * ** The image of a cofork: elementary and cocone-level readings agree / * ** 共叉的图像：初等和余圆锥层次的读法一致 *)

Example image_cofork_inj_ParX@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g) :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParX = fmap[T] (e ∘ f)
  := eq_refl.

Example image_cofork_inj_ParY@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g) :
  cocone_inj (FCocone T (cofork_cocone f g e H)) ParY = fmap[T] e
  := eq_refl.

(*
 Both directions are Structure/Coequalizer.v's diagram-general
 conversions at [K := T ◯ APair f g], whose pair is [fmap[T] f] and
 [fmap[T] g] by conversion.  Over [ParX] the cofork cocone of the image
 pair has the injection [fmap[T] e ∘ fmap[T] f] and the image cocone
 [fmap[T] (e ∘ f)], equal at ≈ by [fmap_comp]; so the first direction
 transports along a cone isomorphism whose apex map is the identity,
 and the second is the conversion itself. 

 --------
 两个方向都是 Structure/Coequalizer.v 在 [K := T ◯ APair f g] 上的图-一般转换，其对应对分别是 [fmap[T]  f] 和 [fmap[T]  g] 的转换。在 [ParX] 上，像对的共叉锥的注入为 [fmap[T]  e ∘ fmap [T]  f]，像锥为 [fmap[T]  (e ∘ f)]，通过 [fmap_comp] 在 ≈ 处相等；因此第一个方向沿着顶点映射为恒等映射的锥同构传输，第二个方向就是转换本身。
*)

Definition image_coequalizer_colimit@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (E : IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e)) :
  IsColimitCocone (FCocone T (cofork_cocone f g e H)).
Proof.
  refine (limitcone_transport _
            (parallel_coequalizer_colimit (T ◯ APair f g) E)).
  exists (@iso_id (X^op) (T q)).
  intro p; destruct p; simpl.
  - rewrite id_left.
    exact (fmap_comp e f).
  - apply id_left.
Defined.

Definition image_colimit_coequalizer@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H))) :
  IsCoequalizer (fmap[T] f) (fmap[T] g) (T q) (fmap[T] e) :=
  parallel_colimit_coequalizer (T ◯ APair f g) _ HC.

Example image_colimit_coequalizer_desc@{co ch xo +}
  {C : Category@{co ch ch}} {X : Category@{xo ch ch}} (T : C ⟶ X)
  {x y : C} {f g : x ~> y} {q : C} {e : y ~> q} (H : e ∘ f ≈ e ∘ g)
  (HC : IsColimitCocone (FCocone T (cofork_cocone f g e H)))
  {z : X} (h : T y ~{X}~> z) (Hh : h ∘ fmap[T] f ≈ h ∘ fmap[T] g) :
  unique_obj (coeq_desc (image_colimit_coequalizer T H HC) h Hh)
    = unique_obj (HC (parallel_cofork_cocone (T ◯ APair f g) h Hh))
  := eq_refl.

(* * ** The absolute coequalizer is the cofork-shaped absolute colimit / * **绝对共等化子是共叉形绝对余极限 *)


Definition AbsoluteCoequalizer_AbsoluteColimitCocone@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (H : e ∘ f ≈ e ∘ g) (A : AbsoluteCoequalizer f g q e) :
  AbsoluteColimitCocone (cofork_cocone f g e H) :=
  fun D T => image_coequalizer_colimit T H (A D T).

Definition AbsoluteColimitCocone_AbsoluteCoequalizer@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y} {q : C} {e : y ~> q}
  (H : e ∘ f ≈ e ∘ g) (A : AbsoluteColimitCocone (cofork_cocone f g e H)) :
  AbsoluteCoequalizer f g q e :=
  fun D T => image_colimit_coequalizer T H (A D T).

(* * ** Split coequalizers, at cone level / * ** 在锥体层面拆分余等化器 *)

Definition split_cofork_AbsoluteColimitCocone@{co ch +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) :
  AbsoluteColimitCocone (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)) :=
  AbsoluteCoequalizer_AbsoluteColimitCocone (scoeq_law1 S)
    (split_coequalizer_absolute S).

(*
 The cofork cocone of a split fork is colimiting by Mac Lane's Lemma,
 through Structure/Coequalizer.v's [is_coequalizer_cocone_ump]. 

 --------
 通过 Mac Lane 引理，分叉的共叉锥是余极限，由 Structure/Coequalizer.v 的 [is_coequalizer_cocone_ump] 给出。
*)

Definition split_coequalizer_PreservesColimitCocone@{co ch do +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) (D : Category@{do ch ch}) (F : C ⟶ D) :
  PreservesColimitCocone (APair f g) F :=
  AbsoluteColimitCocone_preserves
    ((fun N => is_coequalizer_cocone_ump f g
                 (split_coequalizer_is_coequalizer f g S) N)
       : IsColimitCocone (cofork_cocone f g (scoeq_e S) (scoeq_law1 S)))
    (split_cofork_AbsoluteColimitCocone S) D F.

(** ** Contractible pairs (#480) / ** 可缩对 (#480) *)

(*
 Every coequalizer of a contractible pair is absolute: Structure/
 Coequalizer/Contractible.v's [contractible_coequalizer_split] splits
 it.  The instance is named, as for [split_coequalizer_absolute]. 

 --------
 每一个可收缩对的共同化等化器都是绝对的：Structure/Co​equalizer/Contractible.v 的 [contractible_coequalizer_split] 将其分解。该实例被命名，如同 [split_coequalizer_absolute] 一样。
*)

Definition contractible_coequalizer_absolute@{co ch xo xh +}
  {C : Category@{co ch ch}} {x y : C} {f g : x ~> y}
  (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  AbsoluteCoequalizer@{co ch xo xh _} f g q e :=
  split_coequalizer_absolute (contractible_coequalizer_split P E).
