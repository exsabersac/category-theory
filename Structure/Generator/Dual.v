Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Adjunction.SAFT.

Generalizable All Variables.

(*
 Separating and coseparating families are one notion read twice

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/cogenerator

 Riehl, "Category Theory in Context", 2nd ed., Definition 4.7.7
 (printed p. 177, PDF p. 197), defines a COSEPARATING set to be a
 separating set in the opposite category, and Mac Lane's §V.7 (book
 p. 127) pairs the two the same way.  This file is that sentence,
 discharged in both directions, plus the joint-faithfulness reading
 that Adjunction/SAFT.v states as prose and proves nowhere.

 WHY A SEPARATE FILE.  Adjunction/SAFT.v sits high in the tree: it
 requires Structure/Complete.v, Structure/Limit/Product.v,
 Construction/Comma/Limit.v and Adjunction/GAFT.v.  Structure/
 Generator.v is a definition file and must stay near the bottom, so
 the bridge to [Cogenerator] lives here instead, and nothing that
 wants only the covariant notion pays for SAFT's closure.

 THE DATA IS THE SAME, THE QUANTIFIERS ARE SWAPPED.  Construction/
 Opposite.v gives [hom x y := hom y x] and
 [compose f g := g ∘ f], both DEFINITIONALLY, so a [Cogenerator
 (C^op)] holds exactly a [Generator C]'s three fields: an index Type,
 the same objects, and a separation clause whose hypothesis
 [∀ j (k : y ~{C^op}~> cog_obj j), k ∘[C^op] f ≈ k ∘[C^op] g] IS
 [∀ j (k : cog_obj j ~> y), f ∘ k ≈ g ∘ k] in C.  What does NOT match
 up on its own is the NAMING of the two object variables: the
 cogenerating clause quantifies (x, y) where the generating clause
 quantifies (y, x), so the bridge must apply the field with the two
 arguments exchanged.  With the exchange, both directions are terms,
 and both round trips hold at [eq_refl] -- record eta with primitive
 projections (Lib.v's flag), plus function eta on the separation
 field, is enough, and no tactic is used.

 TWO SPELLINGS THAT ARE REFUSED, both measured in this worktree with
 the same requirement list.  (1) The naive bridge, without the
 exchange:
 Definition gen_of_cog_naive (G : Cogenerator (C^op)) : Generator C
 := @Build_Generator C (cog_index G) (cog_obj G)
 (@cog_separates (C^op) G).
 is rejected with
 "(cannot unify "x ~{ C }~> y" and "x ~{ C^op }~> y")",
 a CONVERSION refusal: the field is applied at the objects in the
 order the record declares them, and that order is the opposite one.
 (2) The record-builder syntax without an explicit category:
 {| gen_index := cog_index G; gen_obj := cog_obj G; ... |}
 infers [Generator]'s implicit category from the first field that
 fixes it -- [gen_obj := cog_obj G] has type [cog_index G -> C^op] --
 and so builds a [Generator (C^op)], after which every remaining
 field is checked in the wrong category and the separation field is
 rejected with
 "The term "f" has type "x ~{ C^op }~> y" while it is expected to
 have type "y ~{ C^op }~> x"".
 Hence [@Build_Generator C] and [@Build_Cogenerator (C^op)] are
 written out explicitly below.  (This is the same builder trap the
 tree has met before, and the fix is the same: name the record's
 parameter rather than letting a [C^op]-typed field choose it.)

 THE TYPES ARE NOT EQUAL, AND THE ROUND TRIPS DO NOT SAY THEY ARE.
 [Generator C] and [Cogenerator (C^op)] are two distinct inductives
 carrying the same data; [Generator C = Cogenerator (C^op)] at
 [eq_refl] is REFUSED --
 "The term "eq_refl" has type "Generator C = Generator C" while it
 is expected to have type "Generator C = Cogenerator C^op"
 (cannot unify "Generator C" and "Cogenerator C^op")" --
 which is why this file carries a pair of maps and the two [eq_refl]
 round trips rather than one equation of types.  That is the strongest
 statement available here, and it is stronger than an isomorphism: the
 composites are the identity on the nose, not up to anything.

 THE DUAL CHARACTERIZATION.  [cogenerator_jointly_faithful] and
 [jointly_faithful_cogenerator] discharge the SAFT header's prose,
 "equivalently the representables C(-, cog_obj j) are jointly
 faithful", in both directions.  The functors are Functor/Hom.v's
 [Curried_CoHom C], written [Hom ─, A]; each is a functor C^op ⟶ Sets,
 so [JointlyFaithful] is instantiated at C^op and its two arrow
 variables are C^op arrows -- which is exactly why the proof term
 applies [cog_separates] with the objects exchanged, the same
 bookkeeping as the [Generator] bridge above.  Like the covariant
 characterization in Structure/Generator.v, both directions are terms:
 the Sets hom-setoid is pointwise (Instance/Sets.v) and the
 [fmap] of a contravariant representable is precomposition, so the
 two hypotheses are the same statement.

 UNIVERSES, measured with [Set Printing Universes. About ...].  The
 four bridges are free of constraints: [gen_of_cog], [cog_of_gen],
 [gen_op_of_cog] and [cog_of_gen_op] each print an EMPTY block, which
 is the universe-level statement that no data moves.  The two
 characterizations carry the block that Instance/Sets.v's
 [Sets@{o so} : Category@{so o o}] carries -- the strict [u0 < u2]
 ([u0 < u3] for [jointly_faithful_cogenerator], where the level is
 numbered differently) together with [u0 <= compose.u0/u1/u2] and
 [u0 <= ID.u0] -- inherited through the hom-functor, plus the ≤-bounds
 [JointlyFaithful] and [Cogenerator] contribute themselves, the same
 shape as their covariant counterparts in Structure/Generator.v (an
 earlier revision of this sentence said "exactly the Sets block", which
 an audit measured as short by those inherited bounds).  Every
 constant here binds its category as [Category@{_ u0 u0}], the hom
 level identified with the proof level, and none is pinned to [Set].

 NOT DELIVERED.  No cogenerating example: this file exhibits no
 [Cogenerator] of any concrete category, and SAFT.v's consumers all
 take one as data.  (CORRECTION, #452: the second clause no longer
 holds.  Adjunction/SAFT/InitialObject/Examples.v, a consumer of
 SAFT.v since #452, constructs [Cogenerator]s at the powerset lattice
 [Subsets X] and at an indiscrete category; both are thin, so every
 family cogenerates them.  Instance/Sets/Cogenerator.v, which also
 requires SAFT.v, builds three at [Sets]: [Sets_Cogenerator_untruncate]
 and [Sets_Cogenerator_IEM], small and conditional, and the
 unconditional large [Sets_Cogenerator_large].  And
 Instance/Sets/SpecialInitial.v's [setsop_cog] is [cog_of_gen
 Sets_Generator], a cogenerator of [Sets^op]: a grep for [cog_of_gen]
 over the .v files outside Test/ finds it applied to a concrete
 generator there and nowhere else.)  No transport lemmas on the dual side -- the
 [separator_iso] / [gen_family_mono] / [gen_extend] trio of
 Structure/Generator.v is NOT mirrored for [Cogenerator], although
 each mirror is one line through the two bridges below.  No change to
 Adjunction/SAFT.v beyond a pointer in its header comment: the record,
 its [Arguments], and [cogenerator_canonical_monic] are untouched, and
 in particular [Cogenerator] is NOT redefined as [Generator (C^op)],
 which would have altered a file with live consumers. 

 --------
 分离族和共分离族是重复阅读的一种概念

 nLab:   https://ncatlab.org/nlab/show/separator 
 nLab:   https://ncatlab.org/nlab/show/cogenerator 

 Riehl，《上下文中的范畴论》，第2版，第4.7.7定义
 （印刷版第177页，PDF第197页）将共分离集合定义为在对偶范畴中的分离集合，而Mac Lane的§V.7（书本第127页）以相同方式配对这两者。该文件是该句子，在两个方向上都解除，并且加上Adjunction/SAFT.v以散文方式陈述并未证明的联合忠实性解读。为什么要单独一个文件。Adjunction/SAFT.v 位于树的高层：它依赖于 Structure/Complete.v、Structure/Limit/Product.v、Construction/Comma/Limit.v 和 Adjunction/GAFT.v。Structure/Generator.v 是一个定义文件，必须保持在底层附近，因此到 [Cogenerator] 的桥梁反而放在这里，而任何只想要协变概念的东西都不需要承担 SAFT 闭包的代价。数据是相同的，但量词交换了。Construction/Opposite.v 给出了 [hom x y := hom y x] 和 [compose f g := g ∘ f]，两者在定义上都是如此，因此一个 [余生成器 (C^op)] 精确地包含 [Generator C] 的三个字段：一个索引类型，相同的对象，以及一个分离条款，其假设 [∀ j (k : y ~{C^op}~> cog_obj j), k ∘[C^op]  f ≈ k ∘ [C^op]  g] 在 C 中是 [∀ j (k : cog_obj j ~> y), f ∘ k ≈ g ∘ k]。不匹配的地方是两个对象变量的命名：余生成条款对 (x, y) 量化，而生成条款对 (y, x) 量化，因此桥必须应用交换了两个参数的字段。通过交换，两个方向都是项，两个来回在 [eq_refl] 上都成立——使用原始投影的记录 eta（Lib.v 的标志），加上对分离字段的函数 eta 就足够了，并且没有使用任何策略。两个拼写被拒绝，都在这个工作树中通过相同的需求列表进行测量。(1) 天真的桥接，不含交换：
 定义 gen_of_cog_naive (G : Cogenerator (C^op)) : Generator C
 := @Build_Generator C (cog_index G) (cog_obj G)
 (@cog_separates (C^op) G)。被拒绝，提示
 "(无法统一 'x ~{ C }~> y' 和 'x ~{ C^op }~> y')"，
 一种转换拒绝：字段按记录声明的对象顺序应用，而该顺序是相反的。(2) 没有显式类别的记录构建语法：
 {| gen_index := cog_index G; gen_obj := cog_obj G; ... |}|}
 从第一个固定它的字段推断 [Generator] 的隐式类别 —— [gen_obj := cog_obj G] 的类型是 [cog_index G -> C^op] ——
 然后构建一个 [Generator (C^op)] ，之后每个剩余字段都会在错误的类别中被检查，并且分离字段被拒绝，提示
 “术语 'f' 的类型为 'x ~{ C^op }~> y'，而期望类型为 'y ~{ C^op }~> x'”。因此 [@Build_Generator C] 和 [@Build_Cogenerator (C^op)] 在下面被显式写出。（这是树之前遇到的同一个构建器陷阱，解决方法也相同：给记录的参数命名，而不是让类型为 [C^op] 的字段选择它。）类型不相等，而且往返转换并没有说它们相等。
 [Generator C] 和 [Cogenerator (C^op)] 是两个不同的归纳类型，
 携带相同的数据；[Generator C = Cogenerator (C^op)] 在
 [eq_refl] 被拒绝——
 “术语 'eq_refl' 的类型是 'Generator C = Generator C'，而它
 期望的类型是 'Generator C = Cogenerator C^op'
 （无法统一 'Generator C' 和 'Cogenerator C^op'）”——
 这就是为什么该文件包含一对映射以及两个 [eq_refl] 
 往返转换，而不是一个类型等式。这是这里可用的最强语句，并且它比同构更强：
 复合映射在本质上是恒等映射，而不是“某种意义上的”恒等映射。双重表征。[cogenerator_jointly_faithful] 和 [jointly_faithful_cogenerator] 兑现了 SAFT 头的措辞，“同样地，可表示对象 C(-, cog_obj j) 在两个方向上都是联合忠实的”。这些函子是 Functor/Hom.v 中的 [Curried_CoHom C]，记作 [Hom ─, A]；每个都是 C^op ⟶ Sets 的函子，因此 [JointlyFaithful] 在 C^op 上实例化，其两个箭头变量是 C^op 的箭头——这正是证明项应用 [cog_separates] 时交换对象的原因，与上面的 [Generator] 桥的记账方法相同。像 Structure/Generator.v 中的协变表征一样，两个方向都是项：Sets 的同构集是逐点的（Instance/Sets.v），而一个逆变可表示对象的 [fmap] 是预组合，因此两个假设是相同的陈述。宇宙，通过 [Set Printing Universes. About ...] 测量。四座桥梁没有约束：[gen_of_cog]、[cog_of_gen]、[gen_op_of_cog] 和 [cog_of_gen_op] 各自打印一个空块，这是宇宙级别的声明，表示没有数据移动。两个特征携带 Instance/Sets.v 的 [Sets@{o so} : Category@{so o o}] 所携带的块——严格的 [u0 < u2]（[u0 < u3] 对于 [jointly_faithful_cogenerator]，其中级别编号不同）以及 [u0 <= compose.u0/u1/u2] 和 [u0 <= ID.u0]——通过同态函子继承，并且 ≤-界限 [JointlyFaithful] 和 [Cogenerator] 自身也贡献出去，其形状与 Structure/Generator.v 中它们的协变对应物相同（这句话的早期版本说“正是 Sets 块”，审核中发现由于那些继承的界限而显得简短）。这里的每个常量都将其类别绑定为 [Category@{_ u0 u0}]，即与证明级别相对应的同类级别，并且没有一个固定为 [Set]。未交付。没有共生的例子：该文件没有表现出任何具体范畴的 [Cogenerator]，并且 SAFT.v 的所有使用者都将其作为数据使用。（更正，#452：第二条不再成立。Adjunction/SAFT/InitialObject/Examples.v，自 #452 起作为 SAFT.v 的使用者，在幂集格 [Subsets X] 和一个无分离范畴中构造 [Cogenerator]；两者都是稀薄的，所以每个族都能共生它们。Instance/Sets/Cogenerator.v，同样需要 SAFT.v，在 [Sets] 中构造了三个：[Sets_Cogenerator_untruncate] 和 [Sets_Cogenerator_IEM]，小的且有条件的，以及无条件的大 [Sets_Cogenerator_large]。并且
 Instance/Sets/SpecialInitial.v 的 [setsop_cog] 是 [cog_of_gen
 Sets_Generator]，是 [Sets^op] 的余生成元：在 Test/ 以外的 .v 文件中对 [cog_of_gen] 的搜索发现，它只应用于那里一个具体的生成元，而在其他地方没有应用。） 双侧没有传输引理——
 Structure/Generator.v 的 [separator_iso] / [gen_family_mono] / [gen_extend] 三重组合没有为 [Cogenerator] 镜像，尽管每个镜像通过下面的两个桥接只占一行。对 Adjunction/SAFT.v 没有更改，除了其头部注释中的一个指针：记录、它的 [Arguments] 和 [cogenerator_canonical_monic] 未被修改，特别是 [Cogenerator] 并没有被重新定义为 [Generator (C^op)]，这将会改变一个有实际使用者的文件。
*)

Section Dual.

Context {C : Category}.

(*
   * ** A cogenerating family of C^op IS a generating family of C 

   --------
   * ** C^op 的一个协生成族是 C 的一个生成族
*)

Definition gen_of_cog (G : Cogenerator (C^op)) : Generator C :=
  @Build_Generator C (cog_index G) (cog_obj G)
    (fun x y f g H => @cog_separates (C^op) G y x f g H).

Definition cog_of_gen (G : Generator C) : Cogenerator (C^op) :=
  @Build_Cogenerator (C^op) (gen_index G) (gen_obj G)
    (fun x y f g H => @gen_separates C G y x f g H).

(* Both round trips are the identity on the nose. / 两个往返都是严格的恒等映射。 *)
Example gen_of_cog_of_gen (G : Generator C) :
  gen_of_cog (cog_of_gen G) = G := eq_refl.

Example cog_of_gen_of_cog (G : Cogenerator (C^op)) :
  cog_of_gen (gen_of_cog G) = G := eq_refl.

(*
   * ** The reading the SAFT header states as prose, proved both ways 

   --------
   * ** 阅读 SAFT 头部以散文形式陈述，已两种方式证明
*)

Definition cogenerator_jointly_faithful (G : Cogenerator C) :
  JointlyFaithful (fun j : cog_index G => [Hom ─, cog_obj G j]) :=
  fun x y f g H => cog_separates G f g (fun j k => H j k).

Definition jointly_faithful_cogenerator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom ─, F j])) : Cogenerator C :=
  @Build_Cogenerator C J F (fun x y f g Hk => H y x f g (fun j k => Hk j k)).

End Dual.

(*
 The same pair of bridges read at the other orientation, which costs
 nothing because C^op^op is C by conversion (Construction/Opposite.v,
 the duality discipline CLAUDE.md describes).  These sit OUTSIDE the
 section above: inside it the category is a section variable and the
 two bridges cannot be instantiated at C^op until it is discharged. 

 --------
 相同的一对桥在另一种方向上读取，这不花任何成本，因为 C^op^op 通过转换就是 C（Construction/Opposite.v，双重性规范 CLAUDE.md 所描述）。这些位于上面章节之外：在章节内部，该范畴是一个章节变量，这两座桥不能在 C^op 上实例化，直到它被释放。
*)
Definition gen_op_of_cog {C : Category} (G : Cogenerator C) :
  Generator (C^op) := @gen_of_cog (C^op) G.

Definition cog_of_gen_op {C : Category} (G : Generator (C^op)) :
  Cogenerator C := @cog_of_gen (C^op) G.
