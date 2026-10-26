Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Structure.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * Connected components: π₀ of a category / * 连通分支：一个范畴的 π₀ *)

(*
nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/connected+component
   nLab:      https://ncatlab.org/nlab/show/full+subcategory
   Wikipedia: https://en.wikipedia.org/wiki/Connected_category
   Book:      Riehl, “Category Theory in Context”, Dover 2016, §1.5,
              printed p. 35 (the running definition of a connected
              category) and Proposition 1.5.13, printed pp. 35-36
   Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              GTM 5, §I.5, printed p. 20 (the remark following Definition 9)

   A category is CONNECTED when any two of its objects are joined by a
   finite zig-zag of morphisms.  The relation “there is a zig-zag from x to
   y” is an equivalence relation on the objects, and the quotient by it is
   the SET OF CONNECTED COMPONENTS, written π₀.  Classically every category
   is the disjoint union of its components, each of which is connected;
   that is the sense in which connectedness is not a restriction but a
   decomposition.  Only the second half of that sentence is proved below
   ([Component_Connected]); see the NOT-delivered list for the first.

   This file builds π₀ and the components.  It does NOT build the zig-zag
   relation: that already exists.

--------
nLab：      https://ncatlab.org/nlab/show/connected+category
   nLab：      https://ncatlab.org/nlab/show/connected+component
   nLab：      https://ncatlab.org/nlab/show/full+subcategory
   维基百科： https://en.wikipedia.org/wiki/Connected_category
   书籍：      Riehl，《背景下的范畴论》，Dover 2016，第1.5节，
              印刷页 35（连通范畴的运行定义）以及命题 1.5.13，
              印刷页 35-36
   书籍：      Mac Lane，《面向工作数学家的范畴》，第2版，
              GTM 5，第I.5节，印刷页 20（定义9后的备注）

当一个范畴的任意两个对象都可以通过有限的态射之锯齿链相连时，该范畴是连通的。关系“存在从 x 到 y 的锯齿链”在对象上是一个等价关系，其商集就是连通分量集合，记作 π₀。按照经典定义，每个范畴都是其各个分量的互不相交的并集，每个分量都是连通的；这就是连通性不是一个限制而是一个分解的意义。下文只证明了该句的后半部分 ([Component_Connected])；有关前半部分，请参阅未完成列表。

此文件构建 π₀ 和各个组件。它不构建之字形关系：那已经存在。
*)

(**
** What is consumed, and the correction that goes with it

   [ZigZag], [Connected] and the whole zig-zag calculus are CONSUMED from
   Structure/Groupoid/Connected.v.  Nothing below redeclares them.  What is
   there, checked against that file rather than taken on report:

     [ZigZag]          the inductive chain, with constructors
                       [zz_nil], [zz_fwd] and [zz_bwd]
     [Connected]       ∀ x y : C, ZigZag x y
     [hom_zigzag]      a single arrow as a one-step chain
     [arrow_connected] the one-arrow form implies the zig-zag form
     [zigzag_trans]    chains compose end to end
     [zigzag_sym]      chains reverse
     [Fence]           the strictly alternating form, with
                       [fence_zigzag] and [zigzag_fence] converting
                       both ways
     [zigzag_hom]      collapse to one arrow in a groupoid
     [connected_arrow] and [connected_iso]
     [WideDeloop]      with [WideDeloop_Connected]
     [Roof_Connected]  a connected category that is not a groupoid
     [Two_Discrete_zigzag_endpoints] and
     [Two_Discrete_not_connected]

   Three further files consume [Connected] already:
   Structure/Groupoid/Basepoint.v (as a section hypothesis),
   Construction/Deloop/Transform.v and
   Instance/Top/FundamentalGroupoid.v, which declares [PathConnected]
   and [pathconnected_Connected].

   THE SOURCE ISSUE'S “Current state” IS STALE, AND IN THE STRONGEST WAY:
   it reports that a whole-tree search for the identifier [Connected]
   returns no hits and that “there is no π₀, no zig-zag relation on
   objects”, and proposes building the relation together with its
   reflexivity, symmetry and transitivity from scratch.  Searching the `.v`
   files: [ZigZag] occurs in exactly ONE, the file that declares it; the
   word [Connected] occurs in FIVE, of which one declares it, three use it
   in statements (Structure/Groupoid/Basepoint.v,
   Construction/Deloop/Transform.v,
   Instance/Top/FundamentalGroupoid.v) and one —
   Structure/Groupoid.v — matches only because the file PATH
   `Structure/Groupoid/Connected.v` appears in a comment there.  So the
   issue's item 1, and the reflexivity/symmetry/transitivity HALF of its
   item 2, were already discharged before this file was written, and
   re-declaring them here would have produced a second, incompatible
   zig-zag type.  Item 2's OTHER half — “and that it is preserved by every
   functor” — was NOT discharged, and is [zigzag_fmap] below; the next
   paragraph says exactly that, and an earlier draft of this one claimed
   the whole of item 2 was already done, contradicting it.

   What that same search shows to be genuinely ABSENT is narrower and is
   what this file supplies:

     - no action of a functor on zig-zags: [ZigZag] is named nowhere
       outside its own file, so no such action can exist under any name
       that mentions it, and no statement of the shape “F carries a chain
       to a chain” occurs;
     - no π₀ OF A CATEGORY, and no components construction on a category.
       The nearest prior art is Instance/FinSet/Pushout.v's
       [components], a union-find fold over a LIST OF EDGES on [Fin.t N]
       computing the connected components of a finite graph, used to build
       pushouts in skeletal FinSet.  Its input is an edge list and not a
       category, its output is an idempotent labelling — a chosen
       representative per class, whose fibres are the components — rather
       than a coarsened setoid, and it decides class membership through
       [fin_eqb], which nothing below can do.  The other declared names in
       the tree matching `component` are the components of natural
       transformations and of isomorphisms, together with
       Instance/Comp.v's [Component] and that file's [component_id] and
       [component_compose], and the [components_*] lemmas about the fold
       just described; none of them is π₀;
     - no subcategory spanned by a zig-zag class.

--------
** 消耗的东西，以及随之而来的纠正

[ZigZag]、[Connected] 以及整个之字形演算都来自 Structure/Groupoid/Connected.v。下面没有重新声明它们。这里的内容是根据该文件检查，而不是根据报告获取的：

[ZigZag]          归纳链，带有构造函数
                       [zz_nil]、[zz_fwd] 和 [zz_bwd]
     [Connected]       对任意 x y : C，有 ZigZag x y
     [hom_zigzag]      单箭头作为一步链
     [arrow_connected] 单箭头形式推出之字形形式
     [zigzag_trans]    链按端到端组合
     [zigzag_sym]      链反转
     [Fence]           严格交替形式，带有
                       [fence_zigzag] 和 [zigzag_fence] 进行互相转换
     [zigzag_hom]      在群范畴中折叠为一个箭头
     [connected_arrow] 和 [connected_iso]
     [WideDeloop]      伴随 [WideDeloop_Connected]
     [Roof_Connected]  一个连通范畴但不是群范畴
     [Two_Discrete_zigzag_endpoints] 和
     [Two_Discrete_not_connected]

另外三个文件已经使用了 [Connected]：
   Structure/Groupoid/Basepoint.v（作为一个章节假设），
   Construction/Deloop/Transform.v 和
   Instance/Top/FundamentalGroupoid.v，它声明了 [PathConnected]
   和 [pathconnected_Connected]。

源问题的“当前状态”已经严重过时：它报告说，对标识符 [Connected] 进行全树搜索没有找到任何结果，并且“没有 π₀，也没有对象上的锯齿关系”，并建议从零开始构建该关系及其自反性、对称性和传递性。在搜索 `.v` 文件时：[ZigZag] 恰好出现在一个文件中，即声明它的文件；单词 [Connected] 出现在五个文件中，其中一个声明它，三个在语句中使用它（Structure/Groupoid/Basepoint.v、Construction/Deloop/Transform.v、Instance/Top/FundamentalGroupoid.v），一个 —— Structure/Groupoid.v —— 只是因为那里的文件路径 `Structure/Groupoid/Connected.v` 出现在注释中而匹配。
所以问题的第1项，以及第2项中的自反性/对称性/传递性的一半，在本文件编写之前已经解决，而在这里重新声明它们会生成第二种不兼容的之字形类型。第2项的另一半——“并且它被每个函子保持”——尚未解决，在下面的[zigzag_fmap]中；下一段正是这么说的，而这一段的早期草稿声称第2项的全部内容已经完成，与之矛盾。

同样的搜索显示真正缺失的是更狭窄的内容，而这个文件提供的正是这些内容：

- 对锯齿形图的函子没有作用：[ZigZag] 在它自己的文件以外没有被命名，所以在任何提到它的名称下都不可能存在这样的作用，也没有形如“F 将链映射为链”的陈述；
- 没有π₀的范畴，也没有范畴上的分量构造。最近的现有工作是 Instance/FinSet/Pushout.v 中的 [components]，它是在 [Fin.t N] 上对一组边的 LIST 进行的并查集折叠，用于计算有限图的连通分量，进而在骨架 FinSet 中构建推挤。它的输入是边列表而不是范畴，它的输出是一个幂等标记——每个类选一个代表，其纤维是各分量——而不是粗化的等价类集合，并且通过 [fin_eqb] 决定类的归属，而下面的内容都无法做到这一点。
在与 `component` 匹配的树中声明的其他名称是自然变换和同构的组成部分，以及 Instance/Comp.v 的 [Component] 及该文件的 [component_id] 和 [component_compose]，以及刚才描述的关于 fold 的 [components_*] 引理；它们都不是 π₀；
- 由之字形类生成的子范畴。
*)

(*
Why the principal construction is called [pi0]

   The quotient built below is a SET — an object of [Sets], one point per
   component.  Calling it [Components] would suggest a collection of
   subcategories, which is a different object and is what
   [ConnectedComponent] names in the fourth section.  π₀ is the universal
   name for the set, is unambiguous, and keeps the two apart.  There is no
   in-tree collision: before this file no `pi0`, `Pi0` or
   [ConnectedComponent] was declared anywhere.  [Instance/Comp.v] does
   declare a [Component] — a SOFTWARE component, a map from required
   interfaces to provided ones — which is
   why the category below is [ConnectedComponent] and not [Component]; the
   two would otherwise collide in the single scope the [print-assumptions]
   target audits in.

--------
为什么主要结构被称为 [pi0]

下面构建的商集是一个集合 —— 一个 [Sets] 对象，每个组件一个点。称它为 [Components] 会暗示一个子范畴的集合，这是一个不同的对象，也是 [ConnectedComponent] 在第四部分中命名的。π₀ 是集合的通用名称，没有歧义，并且将两者区分开。树内没有冲突：在此文件之前，没有在任何地方声明过 `pi0`、`Pi0` 或 [ConnectedComponent]。[Instance/Comp.v] 确实声明了一个 [Component] —— 一个软件组件，从所需接口映射到提供接口 —— 这就是为什么下面的范畴是 [ConnectedComponent] 而不是 [Component] 的原因；否则这两者会在 [print-assumptions] 目标审核的单个作用域中发生冲突。
*)

(*
Universes, measured in the constraint blocks

   THE EXPLICIT BINDERS ARE LOAD-BEARING IN THREE PLACES, and in each the
   measurement is discriminating: the same body without them is strictly
   worse and nothing else about it changes.

   (1) [zigzag_fmap].  Written unannotated the fixpoint elaborates at
   [∀ {C : Category@{u0 u1 u1}} {D : Category@{u u1 u1}}] — the two
   categories' HOM universes IDENTIFIED, on an empty constraint block, so
   reading the block alone would report no identification at all.  The
   annotated form's block is literally [hc <= hd], which is [Functor]'s
   own constraint, and it applies to a functor between categories whose hom
   universes are declared strictly apart.  The identification was
   minimization, not content, and it propagates: with it [pi0_fmap] carries
   [hc = hd]; without it, [hc <= hd] together with [hc <= o] and [hd <= o] —
   those being the constraints that bear on the point rather than the whole
   block, which also carries [o < so] and five bounds against stdlib
   donors.

   (2) [pi0_proj].  Unannotated the same body elaborates at
   [∀ C : Category@{u u u}] — ALL THREE of C's universes identified — and
   is then rejected at a category declared with its homs strictly below its
   objects, with “Cannot enforce vh = vo”.  Annotated, [h <= o] is the only
   constraint relating C's own two levels that
   survives, and [pi0_proj Sets] is formable: [Sets@{o so}] IS
   [Category@{so o o}] and so has exactly the shape the unannotated form
   rejects.

   (3) [ObjSetoid] takes FOUR binders rather than three, so that the
   setoid's relation universe is not C's proof universe.  Two comparisons,
   both with an otherwise identical body: taking the setoid packaged from
   Lib/Setoid.v's [eq_Setoid] returns [SetoidObject@{o o}] — carrier and
   relation identified — because [eq_Setoid@{u}] carries one binder and
   returns [Setoid@{u u}], where Lib/Setoid.v's [eq_equivalence@{o q}]
   carries two; and reusing C's own proof universe in place of the fresh
   fourth one makes [pi0_coarser] elaborate with [o = h] where the shipped
   form leaves [h <= o].  So the binder, not merely the annotation on
   [pi0_proj], is doing the work.

   THE SAME CAUSE FORCES AN IDENTIFICATION, AND IT HIDES IN A BINDER — the
   very trap this block names two paragraphs up, met here by this file's own
   [pi0_fmap].  Its binder reads
   [{C : Category@{o hc hc}} {D : Category@{o hd hd}}]: the level [o] is
   written TWICE, so the two categories' OBJECT universes are IDENTIFIED,
   while its constraint block contains no equation at all — a reader who
   checks only the block concludes there is none and is wrong.  [Pi0]
   inherits it.  It is FORCED rather than a minimization accident, and that
   is measured rather than assumed: restating the same body with the object
   universes declared apart puts [oc = od] INTO the constraint block.  The
   cause is the one named next.

   WHAT DOES NOT GO AWAY, and is not this file's doing: both endpoints of a
   morphism of [Sets] live in [obj[Sets@{o so}]], which is
   [SetoidObject@{o o}] — a setoid's carrier universe identified with its
   relation universe.  [ZigZag@{o h}] lands at [Type@{max(o, h)}], so every
   [Sets]-level statement here — [pi0_proj], [pi0_fmap], [Pi0] — carries
   [h <= o]: the homs of the categories it speaks about sit at or below
   their objects.  That is [Sets]' own object type, the restriction
   Structure/Kernel/Universal.v records from the other side, and no route
   around it is attempted here.  It is a BOUND and not an identification,
   and [pi0] itself, which never mentions [Sets], restricts C not at all:
   [pi0@{u u0 u1 u2} : Category@{u u2 u2} → SetoidObject@{u u0}] with
   [u <= u0] and [u2 <= u0] and no equation.

   TWO INHERITED IDENTIFICATIONS are named rather than repaired, and
   neither is claimed unavoidable.  [ZigZag@{u u0}] is declared over
   [Category@{u u0 u0}], identifying C's hom and proof universes; that is
   the donor's, and everything below inherits it.  And [eso_connected]
   keeps [hc = hd] even annotated, which is [EssentiallySurjective]'s
   doing — its instance there is [EssentiallySurjective@{od oc hc}], using
   C's hom universe where D's arrows live.  By contrast
   [connected_image@{k oc od hc hd}] IDENTIFIES neither object universe with
   anything — its whole block is [oc <= k], [hc <= k], [hc <= hd], so one
   object universe is BOUNDED and the other unconstrained; “free of any
   identification” is the accurate reading, not “bounds the homs only” —
   and neither [zigzag_fmap], [ConnectedComponent]
   nor [ConnectedNonempty] contains a universe equation.

--------
宇宙，以约束块为单位测量

显式绑定器在三个地方承重，并且在每个地方其测量都是有区别的：没有它们的相同主体严格来说更差，而且关于它的其他任何方面都没有改变。

(1) [zigzag_fmap]。未加注释的情况下，fixpoint 在 [∀ {C : Category@{u0 u1 u1}} {D : Category@{u u1 u1}}] 上展开——两个范畴的 HOM 宇宙被识别，在一个空的约束块上，因此单独读取该块不会报告任何识别。带注释的形式的块字面上是 [hc <= hd]，这是 [Functor] 自身的约束，并且它适用于那些 Hom 宇宙严格分开的范畴之间的函子。该识别是最小化，而不是内容，并且它会传播：有了它，[pi0_fmap] 承载 [hc = hd]；没有它，[hc <= hd] 连同 [hc <= o] 和 [hd <= o]——这些约束作用于点而不是整个块，整个块也承载 [o < so] 以及针对 stdlib 捐赠者的五个边界。

(2) [pi0_proj]。未加注释的同一主体在 [∀ C : Category@{u u u}] 处详细说明——C 的三个宇宙都已识别——随后在一个范畴中被拒绝，该范畴声明其同类严格低于其对象，并显示“无法强制执行 vh = vo”。加注释后，[h <= o] 是唯一与 C 自身两个层级相关且存活的约束，而 [pi0_proj Sets] 是可形成的：[Sets@{o so}] 即 [Category@{so o o}]，因此具备未加注释形式所拒绝的确切形状。

(3) [ObjSetoid] 使用四个绑定器而不是三个，因此该集合等价关系的宇宙并不是 C 的证明宇宙。做两个比较，两个例子除了主体完全相同之外：从 Lib/Setoid.v 中打包的集合等价的 [eq_Setoid] 返回 [SetoidObject@{o o}]——承载类型和关系被识别——因为 [eq_Setoid@{u}] 携带一个绑定器并返回 [Setoid@{u u}]，而 Lib/Setoid.v 的 [eq_equivalence@{o q}] 携带两个绑定器；并且在原本新的第四个绑定器的位置重用 C 自己的证明宇宙，会使 [pi0_coarser] 在 [o = h] 上展开，而原始的发布形式则保持 [h <= o]。因此，是绑定器，而不仅仅是 [pi0_proj] 上的注释在起作用。

同样的原因强制了标识，并且它隐藏在一个绑定器中——正是这个代码块在上面两个段落中提到的陷阱，在这里由这个文件自身的 [pi0_fmap] 遇到。它的绑定器写着
[{C : Category@{o hc hc}} {D : Category@{o hd hd}}]：级别 [o] 被写了两次，因此这两个范畴的 OBJECT 宇宙被识别，而它的约束块根本不包含任何方程——一个只检查该块的读者会得出没有方程的结论，这是错误的。[Pi0] 继承它。它是被强制的，而不是最小化的偶然，并且这是经过测量而不是假设的：用分别声明对象宇宙的相同主体重述，会将 [oc = od] 放入约束块。原因是下一个被命名的因素。

不会消失的东西，并且这不是这个文件的作用：[Sets] 的一个态射的两个端点都在 [obj[Sets@{o so}] 中]，而 [obj[Sets@{o so}] 是 [SetoidObject@{o o}]——一个集合族的载体宇宙与其关系宇宙相同。[ZigZag@{o h}] 落在 [Type@{max(o, h)}]，因此这里每一个 [Sets] 级的陈述——[pi0_proj]、[pi0_fmap]、[Pi0]——携带 [h <= o]：它所述范畴的同态位于它们的对象上或以下。那就是 [Sets] 自己的对象类型，Structure/Kernel/Universal.v 从另一侧记录，并且这里没有尝试绕过它。它是一个绑定而不是认同，并且 [pi0] 本身，从未提及 [Sets]，完全不限制 C：[pi0@{u u0 u1 u2} : Category@{u u2 u2} → SetoidObject@{u u0}] 与 [u <= u0] 和 [u2 <= u0] 并且没有方程式。

两个继承的标识是被命名而不是修复的，并且都不被认为是不可避免的。[ZigZag@{u u0}] 在 [Category@{u u0 u0}] 上声明，标识了 C 的同构和证明宇宙；那是捐赠者的宇宙，下面的一切都继承它。而 [eso_connected] 即使在注释中也保留 [hc = hd]，这是 [EssentiallySurjective] 的行为——它的实例在 [EssentiallySurjective@{od oc hc}]，使用 D 的箭头所在的 C 的同构宇宙。相比之下，[connected_image@{k oc od hc hd}] 并没有用任何东西标识对象宇宙——它的整个块是 [oc <= k]、[hc <= k]、[hc <= hd]，所以一个对象宇宙是有界的，另一个是不受约束的；“没有任何标识”是准确的解读，而不是“只限制同构”——并且 [zigzag_fmap]、[ConnectedComponent] 或 [ConnectedNonempty] 都不包含宇宙方程。
*)

(*
Strengths, measured [eq_refl] first

   HELD — nine here, and two more with the connected-diagram section at the
   end of the file ([connected_diagram_is_index] and
   [connected_nonempty_diagram_is_index], each naming the new constant
   against the donor predicate applied to the index), so eleven in all.
   None is [t = t] with a notation expanded on one side.  Nine name
   the constant they are about against a DONOR constant; the other two,
   [pi0_proj_at] and [pi0_fmap_at], name it against a bound variable
   (applied, in the second case), which is equally not a tautology but is a
   different shape that the earlier blanket phrasing did not cover:

     [zigzag_fmap_hom]     the image of a one-step chain is the one-step
                           chain on the image arrow
     [pi0_carrier]         carrier (pi0 C) = obj[C]
     [pi0_equiv]           the quotient's `≈` IS [ZigZag]
     [pi0_proj_at]         the projection is the identity on objects
     [pi0_fmap_at]         the induced map IS the object action of F
     [Pi0_obj]             fobj[Pi0] C = pi0 C
     [component_sobj]      the selected objects ARE the zig-zag class
     [component_obj_type]  obj[ConnectedComponent C x] = ∃ y, ZigZag x y
     [Component_Incl_obj]  the inclusion IS the first projection

   MEASURED AND REJECTED, not guarded here — this file carries no [Fail],
   a probe being the place for that:

     [zigzag_fmap Id[C] s = s] at a VARIABLE chain [s].  [zigzag_fmap]
     recurses on the chain, so at a variable it is stuck and rebuilds
     nothing.  The conversion [fobj[Id[C]] x = x] DOES hold and the
     statement DOES close by [eq_refl] at [zz_nil x], which locates the
     failure at the recursion rather than at [Id].  Proved by induction as
     [zigzag_fmap_id].

     [zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s)] likewise: at
     a variable chain rejected, at [zz_nil x] accepted, proved by induction
     as [zigzag_fmap_compose].

     The [proper_morphism] field of [pi0_fmap] supplied as a record-literal
     assignment [proper_morphism := @zigzag_fmap C D F].  The two types are
     CONVERTIBLE and the very same certificate is accepted when supplied by
     a one-step script, so what is rejected is unification through [Proper]
     and [respectful], not the term — the shape
     Instance/Sets/Quotient.v records at [sets_quot_proj].

--------
优势，先测量 [eq_refl]

HELD — 这里有九个，另外两个在文件末尾的连线图部分（[connected_diagram_is_index] 和 [connected_nonempty_diagram_is_index]，每个都将新常量命名为应用于索引的 donor 谓词），所以总共有十一 个。没有一个是 [t = t]，带有在一侧展开的符号。九个是将它们所涉及的常量命名为 DONOR 常量；另外两个，[pi0_proj_at] 和 [pi0_fmap_at]，则是将它命名为绑定变量（在第二种情况下为应用的），这同样不是重言式，但它是一个不同的形态，以前的笼统表述没有涵盖。

[zigzag_fmap_hom]     一步链的像是像箭头上的一步链
                           [pi0_carrier]         载体 (pi0 C) = obj[C]
     [pi0_equiv]           商的 `≈` 是 [ZigZag]
     [pi0_proj_at]         投影在对象上是恒等映射
     [pi0_fmap_at]         诱导映射是 F 的对象作用
     [Pi0_obj]             fobj[Pi0] C = pi0 C
     [component_sobj]      所选对象是曲折类
     [component_obj_type]  obj[ConnectedComponent C x] = 存在 y, ZigZag x y
     [Component_Incl_obj]  包含映射是第一个投影

已测量并被拒绝，这里没有防护——这个文件没有 [Fail]，探针是放置它的地方：

[zigzag_fmap Id[C] s = s] 在变量链 [s] 上。[zigzag_fmap] 对链进行递归，所以在变量处它被卡住并且什么都不重建。转换 [fobj[Id[C]] x = x] 确实成立，并且该语句确实在 [zz_nil x] 的 [eq_refl] 处结束，这将错误定位在递归而不是 [Id] 处。通过归纳法证明如 [zigzag_fmap_id]。

[zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s)] 同样：在一个可变链处被拒绝，在 [zz_nil x] 被接受，通过归纳法证明为 [zigzag_fmap_compose]。

[pi0_fmap] 的 [proper_morphism] 字段作为记录文本赋值提供 [proper_morphism := @zigzag_fmap C D F]。两种类型都是可转换的，并且当通过一步脚本提供时同一证书也被接受，所以被拒绝的是通过 [Proper] 和 [respectful] 的统一，而不是术语——在 [sets_quot_proj] 的形状 Instance/Sets/Quotient.v 记录。
*)

(*
STATUS: axiom-free.  105 constants — 90 named, 12 [Program] obligations,
   the two projections [cn_obj] and [cn_zigzag], and the constructor
   [Build_ConnectedNonempty] — each measured separately by [Print
   Assumptions] at its fully qualified name, all 105 reporting “Closed under
   the global context”.  READ THE GRADE: that is a ONE-TIME measurement of
   all 105; the [make print-assumptions] gate carries FIFTY of them
   permanently, the other 55 being measured once here.  [Print Module] lists
   104 of them, omitting only the constructor, and renders the [Qed] results
   as opaque declarations, a display convention and not an axiom.  Note
   that it WRAPS the [Record] line, so a line-anchored sweep of its output
   reports 103 and misses [ConnectedNonempty] — the counting hazard this
   tree records elsewhere for universe instances, met here at a record.

--------
状态：无公理。105 个常量 — 90 个已命名，12 个 [Program] 义务，两个投影 [cn_obj] 和 [cn_zigzag]，以及构造器 [Build_ConnectedNonempty] — 每个在其完全限定名称下由 [Print Assumptions] 单独测量，所有 105 个均报告“在全局上下文下关闭”。读取分数：这是对所有 105 个的一次性测量；[make print-assumptions] 门永久携带其中的 50 个，其他 55 个仅在此处测量一次。[Print Module] 列出了其中的 104 个，仅省略了构造器，并将 [Qed] 结果呈现为不透明声明，这是一种显示约定，而不是公理。请注意，它将 [Record] 行包装，所以对其输出进行行锚定扫查会报告 103 个并遗漏 [ConnectedNonempty] — 这个计数风险由此树在其他地方记录用于宇宙实例，这里在记录中出现。
*)

(*
What is NOT delivered

     - NO DECISION PROCEDURE.  [ZigZag] is proof-relevant data, and nothing
       here decides whether two objects are joined; the negative results
       below each go through an invariant of the ambient category, never
       through an analysis of chains.

     - NO NORMAL FORM for zig-zags.  [zigzag_fmap_id] and
       [zigzag_fmap_compose] are proved by induction and not by any
       canonical-form argument, and no two chains between the same pair of
       objects are ever identified.

     - NO DISJOINT-UNION THEOREM.  Every object lies in the component of
       itself and every component is connected ([Component_Connected]), but
       nothing here exhibits C as a coproduct of its components in the
       sense of Construction/Coproduct/Indexed.v: that would need the
       components indexed by [carrier (pi0 C)], which is a family of
       categories over a setoid, and no such indexing is built.

     - NO π₀ OF A GROUPOID as a set of isomorphism classes, and no
       comparison with Theory/Skeleton.v.

     - NO LEFT ADJOINT.  [Pi0 : Cat ⟶ Sets] is built, but the discrete
       functor [Sets ⟶ Cat] and the adjunction π₀ ⊣ discrete are not.

     - NO CONNECTED LIMITS.  The reason connected index categories matter —
       that a connected limit of a diagram of a certain shape is computed
       from any one component — is not touched.

     - NO REFLECTION.  Nothing says that a functor with any property
       carries [Connected D] back to [Connected C]; only the forward
       direction is treated.  And the surjectivity hypothesis of
       [eso_connected] is not merely convenient: dropping it makes the
       statement FALSE, which [image_connected_not_connected] witnesses.
       Whether some weaker hypothesis than essential surjectivity suffices
       is neither proved nor refuted.

     - NO ISOMORPHISM OF COMPONENTS.  [Component_reindex_equiv] relates the
       components at two joined representatives by an EQUIVALENCE only, and
       the obstruction is described where it is built; no statement in
       [StrictCat] is attempted.

     - NO NATURALITY OF THE PROJECTION.  [pi0_proj] is built pointwise in
       C; [ObjSetoid] is not exhibited as a functor [Cat ⟶ Sets], so the
       projection is not a natural transformation to [Pi0].

     - NO INVARIANCE OF π₀ UNDER EQUIVALENCE.  [equivalence_connected]
       transports CONNECTEDNESS along an equivalence, but nothing here
       states [C ≃ D → pi0 C ≅ pi0 D], which is the first thing a reader
       handed [Pi0 : Cat ⟶ Sets] will look for.  Nor is [pi0 C] compared
       with [pi0 (C^op)], and the [DiscreteCat bool] witness gets only
       [pi0_bool_separates] (two points are distinct) rather than “exactly
       two components”.

     - NO [Fence] ANALOGUE.  Everything below is stated with [ZigZag]; the
       alternating form is never used, though the donor's conversions make
       every statement transportable to it.

--------
未交付的内容是什么

- 无决策程序。[ZigZag] 是与证明相关的数据，这里没有任何内容可以决定两个对象是否连接；下面的每个负面结果都通过环境范畴的不变量，而从不通过链的分析。

- 对于之字形没有普通形式。[zigzag_fmap_id] 和 [zigzag_fmap_compose] 是通过归纳法而不是任何标准形式的论证来证明的，而且在同一对对象之间的两条链从未被认定为相同。

- 没有不相交并定理。每个对象都位于它自身的分量中，并且每个分量都是连通的（[Component_Connected]），但是这里没有任何内容将 C 表现为其分量的余积（coproduct），如 Construction/Coproduct/Indexed.v 所定义的那样：那将需要由 [carrier (pi0 C)] 索引的分量，这是一组集合上的范畴族，但没有建立这样的索引。

- 不使用作为同构类集合的群体的 π₀，也不与 Theory/Skeleton.v 进行比较。

- 没有左伴随。[Pi0 : Cat ⟶ Sets] 已构建，但离散函子 [Sets ⟶ Cat] 和伴随 π₀ ⊣ 离散尚未构建。

- 没有连接极限。有关连接指数范畴为何重要的原因——即某种形状的图的连接极限是从任意一个分量计算得出的——未被涉及。

- 无反射。没有任何内容表明具有任意性质的函子会将 [Connected D] 映射回 [Connected C]；只处理正向方向。而且 [eso_connected] 的满射性假设不仅仅是方便：去掉它会使该命题为假，[image_connected_not_connected] 证明了这一点。是否存在比本质满射性更弱的假设也能成立，既未被证明也未被否证。

- 组件没有同构。[Component_reindex_equiv] 仅通过等价关系关联两个连接代表的组件，并且阻碍在其构建处被描述；在 [StrictCat] 中未尝试任何声明。

- 投影没有自然性。[pi0_proj]是在C中按点构造的；[ObjSetoid]没有作为函子[Cat ⟶ Sets]展示，因此投影不是到[Pi0]的自然变换。

- π₀ 在等价下不保持不变。[equivalence_connected]
       沿等价传递连通性，但这里没有说明 [C ≃ D → pi0 C ≅ pi0 D]，这是读者
       在拿到 [Pi0 : Cat ⟶ Sets] 时首先会寻找的内容。[pi0 C] 也没有与 [pi0 (C^op)] 进行比较，而且 [DiscreteCat bool] 的见证只得到了
       [pi0_bool_separates]（两个点是不同的），而不是“恰好两个分支”。

- 没有 [Fence] 类似物。下面的所有内容都以 [ZigZag] 表述；交替使用的形式从未使用过，尽管供体的转换使得每条陈述都可以移植到它上面。
*)

(** ** Functors carry zig-zags to zig-zags / ** 函子将之字形映射到之字形 *)

(*
A functor sends each step of a chain to a step of the same direction.
   This is the piece that was missing: the donor file has the chain, its
   composition and its reversal, but no action of a functor on it.

   The recursion is on the chain and nothing else — no functor law is
   consumed, only [fmap] itself.  In particular this holds for an arbitrary
   functor, with no fullness, faithfulness or surjectivity hypothesis.

   The universe binders are spelled out because minimization identifies the
   two categories' hom universes here, and that identification propagates
   to [pi0_fmap] downstream; see the universe block in the header, where
   the two forms are compared.

--------
函子将链的每一步映射到同一方向的一步。
这是缺失的部分：捐赠文件有链、它的复合以及它的逆，但没有函子在其上的作用。

递归仅在链上进行，别的没有——没有消耗任何函子律，仅消耗 [fmap] 本身。特别地，这对于任意函子都成立，无需假设充满性、忠实性或满射性。

宇宙绑定器被写出来是因为最小化在此处识别了两个范畴的同态宇宙，并且该识别会传播到下游的 [pi0_fmap]；参见头文件中的宇宙块，其中比较了这两种形式。
*)
Fixpoint zigzag_fmap@{oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D) {x y : C}
  (s : ZigZag@{oc hc} x y) : ZigZag@{od hd} (F x) (F y) :=
  match s in ZigZag a b return ZigZag@{od hd} (F a) (F b) with
  | zz_nil w    => zz_nil (F w)
  | zz_fwd f s' => zz_fwd (fmap[F] f) (zigzag_fmap F s')
  | zz_bwd f s' => zz_bwd (fmap[F] f) (zigzag_fmap F s')
  end.

(*
The image of a one-step chain is the one-step chain on the image arrow,
   ON THE NOSE.  Both sides mention [zigzag_fmap] and [hom_zigzag], so the
   statement is not [t = t] with the notation expanded on one side.

--------
一步链的图像是在图像箭头上的一步链，就在鼻子上。双方都提到了 [zigzag_fmap] 和 [hom_zigzag]，所以该声明不是带有一边展开符号的 [t = t]。
*)
Example zigzag_fmap_hom {C D : Category} (F : C ⟶ D) {x y : C} (f : x ~> y) :
  zigzag_fmap F (hom_zigzag f) = hom_zigzag (fmap[F] f) := eq_refl.

(*
Functoriality of the action.  These are NOT [eq_refl]: [zigzag_fmap]
   recurses on its chain argument, so at a variable chain it is stuck.
   Both statements were measured at [eq_refl] and REJECTED (measured and
   rejected, not guarded here — no [Fail] appears in this file), and both
   DO close by [eq_refl] at the empty chain [zz_nil x], which is what
   locates the failure at the recursion: the conversions
   [fobj[Id[C]] x = x] and [fobj[G ◯ F] x = fobj[G] (fobj[F] x)] both
   hold, and it is only the rebuilding of a variable chain that does not
   reduce.

--------
作用的函子性。这些不是 [eq_refl]: [zigzag_fmap]  
递归其链参数，因此在变量链上会卡住。  
两个语句都在 [eq_refl] 测量过并被拒绝（测量并拒绝，并非在此处受保护 — 本文件中未出现 [Fail]），并且两者都确实在空链 [zz_nil x] 处由 [eq_refl] 关闭，这就定位了递归中的失败：转换  
[fobj[Id[C]] x = x] 和 [fobj[G ◯ F] x = fobj[G] (fobj[F] x)] 都成立，并且只有重建变量链不会简化。
*)
Lemma zigzag_fmap_id {C : Category} {x y : C} (s : ZigZag x y) :
  zigzag_fmap Id[C] s = s.
Proof.
  induction s; simpl; [ reflexivity | f_equal; exact IHs | f_equal; exact IHs ].
Qed.

Lemma zigzag_fmap_compose {C D E : Category} (G : D ⟶ E) (F : C ⟶ D)
  {x y : C} (s : ZigZag x y) :
  zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s).
Proof.
  induction s; simpl; [ reflexivity | f_equal; exact IHs | f_equal; exact IHs ].
Qed.

(* The action is compatible with the donor's two chain operations. / 该操作与供体的两链操作兼容。 *)
Lemma zigzag_fmap_trans {C D : Category} (F : C ⟶ D) {x y z : C}
  (s : ZigZag x y) (t : ZigZag y z) :
  zigzag_fmap F (zigzag_trans s t)
    = zigzag_trans (zigzag_fmap F s) (zigzag_fmap F t).
Proof.
  induction s; simpl; [ reflexivity | f_equal; apply IHs | f_equal; apply IHs ].
Qed.

Lemma zigzag_fmap_sym {C D : Category} (F : C ⟶ D) {x y : C}
  (s : ZigZag x y) :
  zigzag_fmap F (zigzag_sym s) = zigzag_sym (zigzag_fmap F s).
Proof.
  induction s; simpl.
  - reflexivity.
  - rewrite zigzag_fmap_trans, IHs; reflexivity.
  - rewrite zigzag_fmap_trans, IHs; reflexivity.
Qed.

(*
What a functor out of a connected category gives, stated at exactly the
   strength it has: any two objects IN THE IMAGE are joined.  Read the
   quantifier carefully — [x] and [y] range over C, not over D, so this
   says nothing about objects of D outside the image, and it is NOT
   [Connected D].  The gap is real and is witnessed below by
   [image_connected_not_connected]: the point category is connected, the
   two-element discrete category is not, and there is a functor from the
   first to the second.

--------
从一个连通范畴出来的函子所给出的内容，用它自身的精确强度表述：像中的任何两个对象都是相连的。仔细阅读量词——[x] 和 [y] 遍历 C，而不是 D，所以这对于像外的 D 中的对象没有任何说明，并且它不是 [Connected D]。这个差距是存在的，并在下面由 [image_connected_not_connected] 证明：点范畴是连通的，两个元素的离散范畴不是，并且从第一个到第二个存在一个函子。
*)
Definition connected_image@{k oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D) (K : Connected@{k oc hc} C)
  (x y : C) : ZigZag@{od hd} (F x) (F y) := zigzag_fmap F (K x y).

(*
Surjectivity is what closes the gap, and essential surjectivity is
   enough: an object of D is joined to the image of its chosen preimage by
   the one-step chain on the isomorphism, and the two images are joined by
   [connected_image].

--------
满射性是弥合差距的关键，而本质满射性是足够的：D 的一个对象通过同构上的一步链与其所选前像的像相连接，而这两个像通过 [connected_image] 相连。
*)
Definition eso_connected@{k l oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D)
  (E : EssentiallySurjective F) (K : Connected@{k oc hc} C) :
  Connected@{l od hd} D :=
  fun d e =>
    zz_bwd (to (eso_iso d))
      (zigzag_trans (connected_image F K (eso_obj d) (eso_obj e))
                    (zz_fwd (to (eso_iso e)) (zz_nil e))).

(*
Hence connectedness is invariant under equivalence of categories.  The
   only field of [EquivalenceOfCategories] consumed is its essential
   surjectivity.

--------
因此，连通性在范畴等价下是不变的。[EquivalenceOfCategories] 唯一使用的领域是它的本质满射性。
*)
Definition equivalence_connected {C D : Category} (F : C ⟶ D)
  (E : EquivalenceOfCategories F) (K : Connected C) : Connected D :=
  eso_connected F (Equivalence_EssSurj E) K.

(** ** π₀ as a setoid / ** π₀ 作为集合等价类 *)

(*
The three chain operations of the donor file are exactly the three
   fields of an equivalence relation.  [zz_nil] is reflexivity, [zigzag_sym]
   is symmetry and [zigzag_trans] is transitivity, each passed through
   unchanged: this constant introduces no proof content of its own.

--------
捐赠文件的三个链操作正好是等价关系的三个字段。[zz_nil] 是自反性，[zigzag_sym] 是对称性，[zigzag_trans] 是传递性，每个都保持不变：这个常量本身不引入任何证明内容。
*)
Definition zigzag_Equivalence (C : Category) : Equivalence (@ZigZag C) :=
  {| Equivalence_Reflexive  := @zz_nil C
   ; Equivalence_Symmetric  := @zigzag_sym C
   ; Equivalence_Transitive := @zigzag_trans C |}.

(*
The object type of C as a setoid under Leibniz equality — the finest
   equality on it, so that the quotient below genuinely coarsens.

   THE FOURTH UNIVERSE BINDER IS LOAD-BEARING AND WAS MEASURED, NOT
   GUESSED, in two separate comparisons.  (i) Building the same object from
   Lib/Setoid.v's [eq_Setoid] returns [SetoidObject@{o o}], IDENTIFYING
   the carrier universe with the universe of the equality proofs, because
   [eq_Setoid@{u}] carries a single binder and returns [Setoid@{u u}];
   Lib/Setoid.v's [eq_equivalence@{o q}] carries two.  The two bodies
   differ only in whether the setoid is taken packaged or spelled out over
   that donor, so the difference is attributable to it.  (ii) Reusing C's
   OWN proof universe [p] in place of a fresh [q] — a three-binder variant
   with an otherwise identical body — makes [pi0_coarser] below elaborate
   with [o = h], where the four-binder form leaves [h <= o].  So the extra
   binder, and not merely the annotation on [pi0_proj], is what lets these
   constructions reach a category whose homs sit strictly below its
   objects.

--------
作为在莱布尼茨等式下的集合等价类的对象类型 C —— 它上的最精细等式，因此下面的商真正地变得更粗。

第四个宇宙绑定器是承重的，并且通过两次独立的比较进行了测量，而不是猜测。(i) 从 Lib/Setoid.v 的 [eq_Setoid] 构建相同的对象返回 [SetoidObject@{o o}]，确定了承载宇宙与等式证明的宇宙相同，因为 [eq_Setoid@{u}] 只携带一个绑定器并返回 [Setoid@{u u}]；Lib/Setoid.v 的 [eq_equivalence@{o q}] 携带两个绑定器。两个主体的区别仅在于集合体是作为整体打包还是在该提供者上逐项展开，所以差异归因于此。(ii) 在 C 的 OWN 证明宇宙 [p] 上重用，而不是使用新的 [q]——一个三绑定变体，但主体其他方面相同——使下面的 [pi0_coarser] 能够与 [o = h] 展开，而四绑定形式则保留 [h <= o]。因此，使这些构造达到其态射严格低于对象的范畴的，是额外的绑定器，而不仅仅是 [pi0_proj] 上的注解。
*)
Definition ObjSetoid@{o h p q} (C : Category@{o h p}) : SetoidObject@{o q} :=
  {| carrier   := obj[C]
   ; is_setoid := {| equiv        := @eq obj[C]
                   ; setoid_equiv := @eq_equivalence@{o q} obj[C] |} |}.

(*
π₀ of C: the objects of C with “joined by a zig-zag” as the equality.

   This is Instance/Sets/Quotient.v's [SetsQuotient] applied directly —
   [ZigZag] is already a [crelation] on [obj[C]], so no encoding step
   intervenes.  Per the house discipline of that file the CARRIER IS
   UNTOUCHED and only `≈` is coarsened; the two readbacks below record
   that.

--------
C 的 π₀：C 的对象，以“通过之字形连接”为等式。

这是 Instance/Sets/Quotient.v 的 [SetsQuotient] 直接应用——[ZigZag] 已经是 [obj[C] 上的 [crelation]，因此没有编码步骤介入。根据该文件的规范，CARRIER 保持不变，只有 `≈` 被粗化；下面的两个回读记录了这一点。
*)
Definition pi0 (C : Category) : SetoidObject :=
  SetsQuotient (ObjSetoid C) (@ZigZag C) (zigzag_Equivalence C).

(*
The carrier of π₀ IS the object type, and its equality IS the zig-zag
   relation, both by conversion.  Neither statement is a tautology: each
   names [pi0] on one side and a donor constant on the other.

--------
π₀的载体是对象类型，其相等性是之字形关系，两者都通过转换。两种说法都不是重言式：每种说法在一侧命名[pi0]，在另一侧命名一个供体常量。
*)
Example pi0_carrier (C : Category) : carrier (pi0 C) = obj[C] := eq_refl.

Example pi0_equiv (C : Category) (x y : C) :
  @equiv _ (pi0 C) x y = ZigZag x y := eq_refl.

(*
Leibniz-equal objects are joined, by the empty chain.  This is the
   [SetoidCoarser] hypothesis of Instance/Sets/Quotient.v, and it is
   the only thing the projection needs beyond the equivalence.

--------
莱布尼茨相等的对象通过空链连接。这是 Instance/Sets/Quotient.v 中的 [SetoidCoarser] 假设，并且这是投影除了等价之外所需要的唯一内容。
*)
Definition pi0_coarser@{o h} (C : Category@{o h h}) :
  SetoidCoarser@{o o o o} (A:=ObjSetoid@{o h h o} C) (@ZigZag@{o h} C) :=
  fun x y (e : x = y) =>
    match e in _ = z return ZigZag x z with eq_refl => zz_nil x end.

(*
The projection sending an object to its component, as a morphism of
   [Sets].

   THE EXPLICIT BINDERS HERE ARE LOAD-BEARING, MEASURED AS FOLLOWS.
   Written without them the same body elaborates at
   [∀ C : Category@{u u u}, ...] — all three of C's universes identified —
   and is then REJECTED at a category declared with its homs strictly below
   its objects, with “Cannot enforce vh = vo”.  With the binders written
   out only [h <= o] survives, and [pi0_proj Sets] is formable, [Sets@{o so}]
   being [Category@{so o o}].  The identification was therefore
   MINIMIZATION and not content.  What does NOT go away is [h <= o]: the
   source and target of a [Sets]-morphism are both [SetoidObject@{o o}], so
   the relation universe is forced down to the carrier's, and [ZigZag]
   lands at [max(o, h)].  That constraint is [Sets]' own object type, not
   this file's, and no attempt is made here to route around it.

--------
将一个对象投射到其组成部分，作为 [Sets] 的态射。

这里的显式绑定器是承重的，其衡量如下。没有它们写出来，同样的主体会在 [∀ C : Category@{u u u}, ...] 展开——C 的三个宇宙都被识别——然后在一个声明其态射严格低于其对象的范畴中被拒绝，出现“无法强制 vh = vo”。只有将绑定器写出，[h <= o] 才能存活，并且 [pi0_proj Sets] 可形成，[Sets@{o so}] 是 [Category@{so o o}]。因此，这个识别是最小化，而不是内容。不消失的是 [h <= o]：[Sets]-态射的源和目标都是 [SetoidObject@{o o}]，因此关系宇宙被强制到承载类型，并且 [ZigZag] 落在 [max(o, h)]。这个约束是 [Sets] 自身的对象类型，而不是这个文件的，这里没有尝试绕过它。
*)
Definition pi0_proj@{o so h} (C : Category@{o h h}) :
  ObjSetoid@{o h h o} C ~{Sets@{o so}}~> pi0@{o o o h} C :=
  sets_quot_proj@{so o} (ObjSetoid@{o h h o} C) (@ZigZag@{o h} C)
    (zigzag_Equivalence@{o o h} C) (pi0_coarser@{o h} C).

(* ... and it is the identity on underlying objects, by conversion. / ... 并且它是通过转换在底层对象上的恒等映射。 *)
Example pi0_proj_at (C : Category) (x : C) : pi0_proj C x = x := eq_refl.

(*
π₀ is functorial, and [zigzag_fmap] is exactly the respectfulness
   clause: a map on components is a map on objects that carries joined
   objects to joined objects.

   The certificate is supplied by a one-step script rather than as a field
   of the record literal, for the reason Instance/Sets/Quotient.v
   records at [sets_quot_proj]: [Proper (equiv ==> equiv) fobj[F]] is
   CONVERTIBLE with the type of [zigzag_fmap F] but the elaborator does not
   unfold [Proper] and [respectful] during unification, so the field
   assignment is rejected.  (Measured here too, at exactly that spot.)

--------
π₀是函子性的，而[zigzag_fmap]恰好是尊重性条款：一个组件上的映射是一个对象上的映射，它将合并的对象映射到合并的对象。

该证书是通过一步脚本提供的，而不是作为记录字面量的一个字段，原因见Instance/Sets/Quotient.v中[sets_quot_proj]: [Proper (equiv ==> equiv) fobj[F]]的记录，它与[zigzag_fmap F]的类型是可转换的，但展开器在统一期间不会展开[Proper]和[respectful]，所以字段赋值被拒绝。（这里也在完全相同的位置进行了测量。）
*)
Definition pi0_fmap@{o so hc hd} {C : Category@{o hc hc}}
  {D : Category@{o hd hd}} (F : C ⟶ D) :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof.
  unshelve refine {| morphism := fobj[F] |}.
  intros x y s; exact (zigzag_fmap F s).
Defined.

(* Its underlying map is the object action of F, by conversion. / 它的基础映射是通过转换得到的 F 的对象作用。 *)
Example pi0_fmap_at {C D : Category} (F : C ⟶ D) (x : C) :
  pi0_fmap F x = F x := eq_refl.

(*
Naturally isomorphic functors induce the same map on components: the
   component of the isomorphism at x is a one-step chain from F x to G x.
   Only the [to] direction and none of the coherence is consumed, which is
   why the same proof would work for a bare pointwise family of arrows.

--------
自然同构函子会在分量上产生相同的映射：在 x 处同构的分量是从 F x 到 G x 的一步链。只消耗了 [to] 方向而没有消耗任何相干性，这就是为什么相同的证明对于单独的逐点箭头族也同样适用。
*)
Lemma pi0_fmap_respects {C D : Category} (F G : C ⟶ D) (H : F ≈ G) :
  pi0_fmap F ≈ pi0_fmap G.
Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.

(*
Connectedness read off π₀.  Both directions are NEAR-DEFINITIONAL —
   [equiv] on [pi0 C] IS [ZigZag] by [pi0_equiv] above — and they are
   recorded because the π₀ phrasing is the one a consumer will reach for,
   not because either carries an argument.  Read [pi0_subsingleton] as “π₀
   has at most one point”; the “exactly one” reading needs the
   inhabitedness clause, and is [connected_nonempty_iff_pi0_singleton] in
   the section on the two readings below.

--------
连通性通过 π₀ 读取。两个方向都是近乎定义的 —— [equiv] 在 [pi0 C] 上是 [ZigZag]，依据上文的 [pi0_equiv] —— 它们之所以被记录，是因为 π₀ 的表述是用户会使用的，而不是因为任何一方有论证。将 [pi0_subsingleton] 读作“π₀ 至多有一个点”；“恰好一个”的理解需要存在性条款，并且在下面关于这两种理解的章节中对应 [connected_nonempty_iff_pi0_singleton]。
*)
Definition pi0_subsingleton (C : Category) : Type :=
  ∀ x y : carrier (pi0 C), x ≈ y.

Definition connected_pi0_subsingleton {C : Category} (K : Connected C) :
  pi0_subsingleton C := K.

Definition pi0_subsingleton_connected {C : Category}
  (H : pi0_subsingleton C) : Connected C := H.

Theorem connected_iff_pi0_subsingleton (C : Category) :
  Connected C ↔ pi0_subsingleton C.
Proof.
  split; [ exact (@connected_pi0_subsingleton C)
         | exact (@pi0_subsingleton_connected C) ].
Defined.

(** ** π₀ as a functor Cat ⟶ Sets / ** 作为函子 Cat ⟶ Sets 的 π₀ *)

(*
The three functor laws are free.  [fmap_respects] is [pi0_fmap_respects];
   [fmap_id] and [fmap_comp] ask for a chain between two objects that are
   Leibniz-equal, and [zz_nil] supplies it — so no property of [Id] or of
   [Compose] is consumed at all, and in particular [zigzag_fmap_id] and
   [zigzag_fmap_compose] are NOT used here.  They are the stronger,
   Leibniz-level statements; these obligations only need `≈` in [Sets],
   which on components is inhabitation of [ZigZag].

   [Cat]'s hom-setoid is natural isomorphism (Instance/Cat.v), which is
   exactly why [pi0_fmap_respects] is what [fmap_respects] wants; a functor
   into [Sets] out of a strict category of categories would be a different
   statement and is not built.

--------
三个函子律是免费的。[fmap_respects] 等于 [pi0_fmap_respects]；[fmap_id] 和 [fmap_comp] 要求在两个莱布尼茨相等的对象之间建立一个链，而 [zz_nil] 提供了它——因此 [Id] 或 [Compose] 的任何属性都没有被消耗，特别是 [zigzag_fmap_id] 和 [zigzag_fmap_compose] 在这里没有使用。它们是更强的莱布尼茨级别声明；这些义务仅在 [Sets] 中需要 `≈`，在组件上则是 [ZigZag] 的存在性。

[Cat] 的同态集是自然同构（Instance/Cat.v），这正是 [pi0_fmap_respects] 所需的 [fmap_respects]；从严格的范畴的范畴中到 [Sets] 的函子将是一个不同的声明，并且尚未被构建。
*)
Program Definition Pi0 : Cat ⟶ Sets := {|
  fobj := pi0;
  fmap := fun _ _ F => pi0_fmap F
|}.
Next Obligation. intros F G H. exact (pi0_fmap_respects F G H). Defined.
Next Obligation. exact (zz_nil _). Defined.
Next Obligation. exact (zz_nil _). Defined.

Example Pi0_obj (C : Cat) : fobj[Pi0] C = pi0 C := eq_refl.

(** ** The connected component of an object, as a full subcategory / ** 作为一个完全子范畴的对象的连通分支 *)

(*
The objects joined to x, with EVERY morphism of C between them.  The
   selected-morphism family is the universe-polymorphic unit, so the two
   closure fields are discharged by the ambient obligation tactic and the
   subcategory is full by construction.

--------
与 x 相连的对象，以及 C 中它们之间的每一个态射。所选的态射族是宇宙多态单元，因此两个闭包域由环境义务策略解除，并且子范畴按构造是满的。
*)
Program Definition ComponentSub (C : Category) (x : C) : Subcategory C := {|
  sobj := fun y => ZigZag x y;
  shom := fun _ _ _ _ _ => poly_unit
|}.

Example component_sobj (C : Category) (x y : C) :
  sobj C (ComponentSub C x) y = ZigZag x y := eq_refl.

Definition ConnectedComponent (C : Category) (x : C) : Category :=
  Sub C (ComponentSub C x).

Example component_obj_type (C : Category) (x : C) :
  obj[ConnectedComponent C x] = (∃ y : C, ZigZag x y) := eq_refl.

Definition Component_Incl (C : Category) (x : C) :
  ConnectedComponent C x ⟶ C := Incl C (ComponentSub C x).

Example Component_Incl_obj (C : Category) (x : C)
  (y : ConnectedComponent C x) : Component_Incl C x y = `1 y := eq_refl.

Definition ComponentSub_Full (C : Category) (x : C) :
  Category.Construction.Subcategory.Full C (ComponentSub C x) :=
  fun _ _ _ _ _ => ttt.

Definition Component_Incl_Faithful (C : Category) (x : C) :
  Faithful (Component_Incl C x) := Incl_Faithful C (ComponentSub C x).

Definition Component_Incl_Full (C : Category) (x : C) :
  Functor.Full (Component_Incl C x) :=
  Full_Implies_Full_Functor C (ComponentSub C x) (ComponentSub_Full C x).

(*
Every arrow of C between two selected objects is an arrow of the
   component, the selection witness being [ttt].

--------
在两个选定对象之间的每一条 C 箭头都是组件的箭头，选择见证为 [ttt]。
*)
Definition component_arr {C : Category} {x : C} {a b : C}
  (sa : ZigZag x a) (sb : ZigZag x b) (f : a ~> b) :
  (a; sa) ~{ConnectedComponent C x}~> (b; sb) := (f; ttt).

(*
Membership is DATA, so one object of C sitting in the component by two
   different chains gives two DIFFERENT objects of the subcategory.  They
   are canonically isomorphic, by the identity of C in both directions.
   (Construction/Subcategory.v's [Full_membership_iso] proves the same
   thing generically; it is not used, the direct construction being two
   lines because [shom] here is [poly_unit] and the hom-setoid of [Sub]
   compares first projections.)

--------
成员是数据，因此一个 C 的对象通过两个不同的链条位于组件中，会产生子类的两个不同对象。它们是典型同构的，因为 C 在两个方向上是相同的。（Construction/Subcategory.v 的 [Full_membership_iso] 泛型地证明了同样的事情；它没有被使用，直接构造只是两行，因为这里的 [shom] 是 [poly_unit]，而 [Sub] 的 Hom-setoid 比较的是第一个投影。）
*)
Program Definition component_iso (C : Category) (x y : C)
  (s t : ZigZag x y) :
  @Isomorphism (ConnectedComponent C x) (y; s) (y; t) := {|
  to := (id[y]; ttt) ; from := (id[y]; ttt)
|}.

(*
A chain in C starting inside the component lifts to a chain in the
   component.  This is what makes each component connected, and it is the
   one genuinely recursive construction of this section: each intermediate
   object of the chain has to be SHOWN to lie in the component, by
   extending the chain that got us to the previous one, and the target
   membership proof is carried along as an explicit argument so that the
   chain may end at whichever proof the caller holds.

   The [zz_nil] branch is where the proof-relevance is paid for: the two
   membership proofs there need not agree, so the empty chain of C becomes
   a ONE-step chain of the component, on the identity arrow.

--------
从组件内开始的 C 链可以提升为组件中的链。这就是使每个组件保持连通的原因，也是本节中唯一真正的递归构造：链的每个中间对象必须通过扩展到前一个对象的链来证明它位于组件中，目标成员资格证明作为显式参数携带，以便链可以在调用者持有的任意证明处结束。

[zz_nil] 分支是支付证明相关性代价的地方：那里两个成员资格证明不必一致，因此 C 的空链在恒等箭头上就变成了组件的一步链。
*)
Fixpoint component_lift {C : Category} {x : C} {y z : C}
  (sy : ZigZag x y) (s : ZigZag y z) :
  ∀ sz : ZigZag x z, @ZigZag (ConnectedComponent C x) (y; sy) (z; sz) :=
  match s in ZigZag a b
        return ∀ (sa : ZigZag x a) (sb : ZigZag x b),
               @ZigZag (ConnectedComponent C x) (a; sa) (b; sb) with
  | zz_nil w    => fun sa sb => hom_zigzag (component_arr sa sb (id[w]))
  | zz_fwd f s' => fun sa sb =>
      zz_fwd (component_arr sa (zigzag_trans sa (hom_zigzag f)) f)
             (component_lift (zigzag_trans sa (hom_zigzag f)) s' sb)
  | zz_bwd f s' => fun sa sb =>
      zz_bwd (component_arr (zigzag_trans sa (zz_bwd f (zz_nil _))) sa f)
             (component_lift (zigzag_trans sa (zz_bwd f (zz_nil _))) s' sb)
  end sy.

(*
Each component is connected — the half of “C is the disjoint union of
   its connected components” that is a theorem here.  The chain from a to b
   is built in C by going back to x and out again, then lifted.

--------
每个组成部分都是连通的——“C 的一半是其连通分支的互不相交并集”在这里是一个定理。从 a 到 b 的链条是在 C 中通过返回 x 再出去，然后抬升而构建的。
*)
Definition Component_Connected (C : Category) (x : C) :
  Connected (ConnectedComponent C x).
Proof.
  intros [a sa] [b sb].
  exact (component_lift sa (zigzag_trans (zigzag_sym sa) sb) sb).
Defined.

(* ... and each is inhabited, by its own representative. / ... 每个都有自己的代表居住。 *)
Definition Component_obj (C : Category) (x : C) : ConnectedComponent C x :=
  (x; zz_nil x).

(*
A connected category is its own single component, up to equivalence: the
   inclusion is fully faithful always, and connectedness makes it
   surjective on objects on the nose, so the witnessing isomorphism is
   [iso_id].

--------
一个连通范畴在等价意义下是它自己的单一分量：包含函子总是完全忠实的，而连通性使它在对象上严格满射，所以见证的同构是 [iso_id]。
*)
Definition Component_Incl_ESO (C : Category) (x : C) (K : Connected C) :
  EssentiallySurjective (Component_Incl C x) :=
  @Build_EssentiallySurjective _ _ (Component_Incl C x)
    (fun d => ((d; K x d) : ConnectedComponent C x)) (fun d => iso_id).

Definition connected_Component_equiv (C : Category) (x : C)
  (K : Connected C) : EquivalenceOfCategories (Component_Incl C x) :=
  @FF_ESO_Equivalence _ _ (Component_Incl C x)
    (Component_Incl_Full C x) (Component_Incl_Faithful C x)
    (Component_Incl_ESO C x K).

(*
The component does not depend on which representative names it.  The
   object and arrow actions are elaborated as plain definitions first,
   because writing them inline in a [Program Definition] makes Program
   destructure the sigma and insert [eq_rect] transports that no ordinary
   case analysis discharges — the hazard Functor/Construction/Postcompose.v
   records for indexed arrow actions, met here through [sigT].

--------
该组件不依赖于由哪个代表命名。对象和箭头操作首先作为普通定义进行阐述，因为如果将它们内联写入 [Program Definition]，程序会析构 sigma 并插入 [eq_rect] 传输，而普通的案例分析无法处理这些传输——Functor/Construction/Postcompose.v 针对索引箭头操作记录的风险，在此通过 [sigT] 遇到。
*)
Definition component_reindex_obj {C : Category} {x x' : C} (z : ZigZag x x')
  (y : ConnectedComponent C x) : ConnectedComponent C x' :=
  (`1 y; zigzag_trans (zigzag_sym z) `2 y).

Definition component_reindex_map {C : Category} {x x' : C} (z : ZigZag x x')
  {a b : ConnectedComponent C x} (f : a ~> b) :
  component_reindex_obj z a
    ~{ConnectedComponent C x'}~> component_reindex_obj z b := (`1 f; ttt).

Program Definition Component_reindex {C : Category} {x x' : C}
  (z : ZigZag x x') :
  ConnectedComponent C x ⟶ ConnectedComponent C x' := {|
  fobj := component_reindex_obj z ; fmap := @component_reindex_map C x x' z
|}.

Definition Component_reindex_Faithful (C : Category) (x x' : C)
  (z : ZigZag x x') : Faithful (Component_reindex z).
Proof. construct; simpl in *; auto. Defined.

Definition Component_reindex_Full (C : Category) (x x' : C)
  (z : ZigZag x x') : Functor.Full (Component_reindex z).
Proof.
  construct.
  - exact (`1 g; ttt).
  - simpl; reflexivity.
Defined.

Definition Component_reindex_ESO (C : Category) (x x' : C)
  (z : ZigZag x x') : EssentiallySurjective (Component_reindex z).
Proof.
  unshelve refine (@Build_EssentiallySurjective _ _ _ _ _).
  - intro d; exact ((`1 d; zigzag_trans z `2 d) : ConnectedComponent C x).
  - intros [w s]; simpl.
    exact (component_iso C x' w _ s).
Defined.

(*
Only an EQUIVALENCE is claimed, and that is not a shortfall of the proof
   but of the objects: reindexing changes the membership proof each object
   carries, so the object [(w; s)] of the target is reached from
   [(w; zigzag_trans z s)] and comes back as
   [(w; zigzag_trans (zigzag_sym z) (zigzag_trans z s))], a DIFFERENT chain
   from [s].  The two index isomorphic objects, which is what
   [component_iso] supplies and what the essential-surjectivity witness
   above uses.

--------
仅声明了一个等价性，这不是证明的缺失，而是对象的原因：重新索引会改变每个对象携带的成员证明，因此目标的对象 [(w; s)] 是从 [(w; zigzag_trans z s)] 到达的，然后作为 [(w; zigzag_trans (zigzag_sym z) (zigzag_trans z s))] 返回，这是一个不同于 [s] 的链。这两个索引同构的对象，就是 [component_iso] 提供的，也是上述本质满射见证所使用的。
*)
Definition Component_reindex_equiv (C : Category) (x x' : C)
  (z : ZigZag x x') :
  EquivalenceOfCategories (Component_reindex z) :=
  @FF_ESO_Equivalence _ _ (Component_reindex z)
    (Component_reindex_Full C x x' z) (Component_reindex_Faithful C x x' z)
    (Component_reindex_ESO C x x' z).

(** ** Two readings of “connected”, separated / ** “connected”的两个含义，被分开 *)

(*
THE SOURCE ISSUE AND THE DONOR FILE DO NOT DEFINE THE SAME PREDICATE,
   AND THE DIFFERENCE IS EXACTLY THE EMPTY CATEGORY.  The issue asks for
   “INHABITED, and any two objects are joined by a zig-zag”; the in-tree
   [Connected] (Structure/Groupoid/Connected.v) is the second clause
   alone.  The usual convention — the nLab entry cited at the head of this
   file states it — includes inhabitedness, precisely so that “a category
   is the disjoint union of its connected components” has no empty
   summand — so this is a genuine discrepancy and not a matter of taste.

   [ConnectedNonempty] below is the stronger reading, with the extra datum
   as its own field so that neither direction is hidden: [cn_zigzag]
   forgets it and [Build_ConnectedNonempty] supplies it.

--------
源问题和捐赠文件没有定义相同的谓词，而差异恰好是空范畴。该问题要求“有元素的，并且任何两个对象都由锯齿状路径连接”；在树内的 [Connected] (Structure/Groupoid/Connected.v) 只是第二条子句。通常的惯例——本文件开头引用的 nLab 条目指出——包括有元素性，正是为了使“一个范畴是其连通分量的互不相交并”不会有空的加数——所以这是真正的差异，而不是偏好问题。  

下面的 [ConnectedNonempty] 是更强的解读，额外数据作为其自身字段，因此没有方向被隐藏：[cn_zigzag] 忘记了它，而 [Build_ConnectedNonempty] 则提供了它。
*)
Record ConnectedNonempty (C : Category) : Type := {
  cn_obj    : C;
  cn_zigzag : Connected C
}.

Arguments cn_obj {C} _.
Arguments cn_zigzag {C} _.
Arguments Build_ConnectedNonempty {C} _ _.

Definition connected_of_nonempty {C : Category} (K : ConnectedNonempty C) :
  Connected C := cn_zigzag K.

Definition nonempty_connected {C : Category} (c : C) (K : Connected C) :
  ConnectedNonempty C := Build_ConnectedNonempty c K.

(*
The empty category satisfies the in-tree reading VACUOUSLY: there is no
   pair of objects to join, so the function is defined by zero clauses.

--------
空范畴以空洞的方式满足树内读数：没有要连接的对象对，因此函数由零条子句定义。
*)
Definition Zero_Connected : Connected _0.
Proof. intros x; destruct x. Defined.

(* ... and fails the issue's reading, since it has no object at all. / ...并且未能理解该问题，因为它根本没有任何对象。 *)
Theorem Zero_not_ConnectedNonempty : ConnectedNonempty _0 → False.
Proof. intro K; destruct (cn_obj K). Qed.

(*
The separation, packaged: the two readings are not the same predicate,
   and [_0] is a witness.  This is what makes the discrepancy above a
   proved fact rather than an observation.

--------
分离，已打包：这两种读数不是相同的谓词，[_0] 是一个证人。这就是使上述差异成为一个已证实事实而不是观察结果的原因。
*)
Definition connected_readings_differ :
  Connected _0 * (ConnectedNonempty _0 → False) :=
  (Zero_Connected, Zero_not_ConnectedNonempty).

(*
Every component satisfies the stronger reading, its representative
   supplying the object.  So the decomposition of C into components has no
   empty summand — which is the reason the stronger reading is the
   conventional one.

--------
每个组成部分都满足更强的解读，其代表提供对象。因此，C 分解为组成部分时没有空的加项——这就是更强解读是常规解读的原因。
*)
Definition Component_ConnectedNonempty (C : Category) (x : C) :
  ConnectedNonempty (ConnectedComponent C x) :=
  Build_ConnectedNonempty (Component_obj C x) (Component_Connected C x).

(*
The π₀ phrasing of the stronger reading: π₀ has exactly one point.  Like
   the subsingleton statement above this is near-definitional, the carrier
   of [pi0 C] being [obj[C]] and its `≈` being [ZigZag].

--------
更强读法的 π₀ 表述：π₀ 恰好有一个点。像上面提到的子单元陈述一样，这几乎是定义性的，X 的载体为 [obj[C]，而它的 `≈` 为 [ZigZag]。
*)
Theorem connected_nonempty_iff_pi0_singleton (C : Category) :
  ConnectedNonempty C ↔ (carrier (pi0 C) * pi0_subsingleton C).
Proof.
  split.
  - intro K; exact (cn_obj K, cn_zigzag K).
  - intros [c H]; exact (Build_ConnectedNonempty c H).
Defined.

(** ** Categories that are connected, and one that is not / ** 相互关联的范畴，以及一个不相关的范畴 *)

(*
A terminal object joins every pair: out to 1 and back.  Both the bundled
   class and the object-level predicate of Structure/Terminal.v are
   covered, the latter because terminality is often available only as a
   property.

--------
一个终端对象连接每一对：输出到 1 再返回。Structure/Terminal.v 中的捆绑类和对象级谓词都被涵盖，后者是因为终端性通常仅作为一种性质可用。
*)
Definition terminal_connected {C : Category} (T : @Terminal C) :
  Connected C :=
  fun x y => zz_fwd (@one C T x) (zz_bwd (@one C T y) (zz_nil y)).

Definition is_terminal_connected {C : Category} {c : C}
  (H : IsTerminalObj c) : Connected C :=
  fun x y => zz_fwd (is_terminal_one H (x:=x))
                    (zz_bwd (is_terminal_one H (x:=y)) (zz_nil y)).

Definition terminal_ConnectedNonempty {C : Category} (T : @Terminal C) :
  ConnectedNonempty C :=
  Build_ConnectedNonempty (@terminal_obj C T) (terminal_connected T).

(*
Dually for an initial object: in to 0 and back out.  Note that these are
   written out rather than obtained from the terminal case at [C^op],
   because a chain in [C^op] is not a chain in C on the nose — the two
   constructors exchange — and no transport between them is built here.

--------
初始对象的双重性：进入0并再返回。请注意，这些是写出来的，而不是从[C^op]的终端情况得到的，因为在[C^op]中的链条并不完全等同于C中的链条——两个构造函数是互换的——并且这里没有建立它们之间的任何传输。
*)
Definition initial_connected {C : Category} (I : @Initial C) :
  Connected C :=
  fun x y => zz_bwd (@zero C I x) (zz_fwd (@zero C I y) (zz_nil y)).

Definition is_initial_connected {C : Category} {c : C}
  (H : IsInitialObj c) : Connected C :=
  fun x y => zz_bwd (is_initial_zero H (x:=x))
                    (zz_fwd (is_initial_zero H (x:=y)) (zz_nil y)).

Definition initial_ConnectedNonempty {C : Category} (I : @Initial C) :
  ConnectedNonempty C :=
  Build_ConnectedNonempty (@initial_obj C I) (initial_connected I).

(* The point category, directly: its single hom is the one-step chain. / 点范畴，直接：它的单同态就是一步链。 *)
Definition One_Connected : Connected _1 :=
  fun x y => @hom_zigzag _1 x y ttt.

Definition One_ConnectedNonempty : ConnectedNonempty _1 :=
  @Build_ConnectedNonempty _1 ttt One_Connected.

(*
In a discrete category a chain cannot leave the object it starts at:
   every arrow forces its endpoints Leibniz-equal, and an induction over
   the chain accumulates those equalities.  Stated over
   Structure/Discrete.v's [Discrete] PREDICATE rather than over
   Instance/Discrete.v's construction, so it applies to any category shown
   discrete.  (Structure/Groupoid/Connected.v proves the same statement
   for the one two-object discrete category it needed; this is the general
   form, and that one is not used below.)

--------
在离散范畴中，链条不能离开它开始的对象：每一条箭头都迫使其端点在莱布尼茨意义下相等，并且对链条进行归纳会积累这些相等性。这里是基于 Structure/Discrete.v 的 [Discrete] 谓词来表述，而不是基于 Instance/Discrete.v 的构造，因此它适用于任何被证明为离散的范畴。（Structure/Groupoid/Connected.v 证明了它所需的那个两个对象的离散范畴的同一个命题；这是一般形式，而下面没有使用那个。）
*)
Lemma discrete_zigzag_eq {C : Category} (D : Discrete C) {x y : C}
  (s : ZigZag x y) : x = y.
Proof.
  induction s as [ w | a b c f s' IH | a b c f s' IH ].
  - reflexivity.
  - transitivity b; [ exact `1 (D _ _ f) | exact IH ].
  - transitivity b; [ symmetry; exact `1 (D _ _ f) | exact IH ].
Qed.

Definition discrete_connected_eq {C : Category} (D : Discrete C)
  (K : Connected C) (x y : C) : x = y := discrete_zigzag_eq D (K x y).

(*
Hence a discrete category is connected exactly when it has at most one
   object, and satisfies the stronger reading exactly when it has exactly
   one.  The backward directions are immediate: in [DiscreteCat A] a
   morphism IS an equality proof, so [x = y] already names an arrow.

--------
因此，一个离散范畴正好在它最多有一个对象时是连通的，并且当它恰好有一个对象时满足更强的含义。反方向是显而易见的：在 [DiscreteCat A] 中，一个态射就是一个等式证明，所以 [x = y] 已经命名了一个箭头。
*)
Theorem DiscreteCat_connected_iff (A : Type) :
  Connected (DiscreteCat A) ↔ (∀ x y : A, x = y).
Proof.
  split.
  - intros K x y.
    exact (discrete_connected_eq (DiscreteCat_Discrete A) K x y).
  - intros H x y.
    exact (hom_zigzag (H x y : x ~{DiscreteCat A}~> y)).
Defined.

Theorem DiscreteCat_ConnectedNonempty_iff (A : Type) :
  ConnectedNonempty (DiscreteCat A) ↔ (A * (∀ x y : A, x = y)).
Proof.
  split.
  - intro K.
    exact (cn_obj K,
           fun x y => discrete_connected_eq (DiscreteCat_Discrete A)
                        (cn_zigzag K) x y).
  - intros [a H].
    exact (@Build_ConnectedNonempty (DiscreteCat A) a
             (snd (DiscreteCat_connected_iff A) H)).
Defined.

(*
For a GROUPOID the zig-zag form and the one-arrow form agree.  This is
   PURE ASSEMBLY of two constants of the donor file —
   Structure/Groupoid/Connected.v's [connected_arrow] forward and its
   [arrow_connected] back — and introduces no argument of its own; it is
   recorded because the biconditional is the shape a consumer wants and the
   donor states only the two halves.  The forward half is where the
   groupoid hypothesis is spent, through [zigzag_hom].

--------
对于一个 GROUPOID，之字形形式和单箭头形式是一致的。这是对捐赠文件中两个常量的纯粹组装——Structure/Groupoid/Connected.v 的 [connected_arrow] 正向和 [arrow_connected] 反向——并没有引入它自己的参数；之所以记录它，是因为双条件是使用者需要的形式，而捐赠者只陈述了两半。正向部分是消耗 groupoid 假设的地方，通过 [zigzag_hom]。
*)
Theorem groupoid_connected_iff_arrow {C : Category} (G : IsGroupoid C) :
  Connected C ↔ (∀ x y : C, x ~> y).
Proof.
  split; [ exact (connected_arrow G) | exact (@arrow_connected C) ].
Defined.

(** ** Witnesses / ** 证人 *)

(*
The walking parallel pair is connected: its two objects are joined by
   either of its two non-identity arrows, and the chain uses one of them
   forwards or backwards according to direction.

--------
步行平行对是连通的：它的两个对象由其两个非恒等箭头中的任意一个连接，并且链根据方向向前或向后使用其中一个。
*)
Definition Parallel_Connected : Connected Parallel.
Proof.
  intros x y.
  destruct x, y.
  - exact (@zz_nil Parallel ParX).
  - exact (hom_zigzag ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - exact (@zz_bwd Parallel ParY ParX ParX
             ((true; ParOne) : ParX ~{Parallel}~> ParY)
             (@zz_nil Parallel ParX)).
  - exact (@zz_nil Parallel ParY).
Defined.

Definition Parallel_ConnectedNonempty : ConnectedNonempty Parallel :=
  @Build_ConnectedNonempty Parallel ParX Parallel_Connected.

Definition pi0_Parallel_subsingleton : pi0_subsingleton Parallel :=
  Parallel_Connected.

(*
[Roof] is the sharper witness and it is CITED, not reproved:
   Structure/Groupoid/Connected.v's [Roof_Connected] already exhibits
   the walking span as connected, and its [Roof_no_arrow_neg_pos] shows
   it is not arrow-connected.  So π₀ of it is a SUBSINGLETON — which is
   what the constant below says; [Roof] is inhabited, so “exactly one
   point” is also true there, but it needs the inhabitedness clause and is
   not what is delivered — even though two
   of its three objects have an empty hom-set between them in BOTH
   directions — Instance/Roof.v supplies the two emptiness
   lemmas.  That is the case in which π₀ says strictly more than the
   one-arrow reading would.

--------
[Roof] 是更有分量的证据，并且它是被引用的，而不是被指责的：
Structure/Groupoid/Connected.v 的 [Roof_Connected] 已经展示了行跨度是连通的，而它的 [Roof_no_arrow_neg_pos] 显示它不是箭头连通的。所以它的 π₀ 是一个 SUBSINGLETON——这也正是下面常量所说明的；[Roof] 是有元素的，所以“恰好一个点”在那儿也是成立的，但它需要有元素的条件，并不是直接提供的——即使它的三个对象中有两个在两个方向上的同态集都是空的——Instance/Roof.v 提供了这两个空集引理。这就是 π₀ 所表述的严格内容比单箭头解释更多的情况。
*)
Definition pi0_Roof_subsingleton : pi0_subsingleton Roof := Roof_Connected.

(* The two-element discrete category is NOT connected. / 二元离散范畴未连接。 *)
Theorem DiscreteCat_bool_not_connected :
  Connected (DiscreteCat bool) → False.
Proof.
  intro K.
  pose proof (fst (DiscreteCat_connected_iff bool) K true false) as H.
  discriminate H.
Qed.

(*
... and π₀ of it genuinely separates its two objects, which is what
   makes the construction non-vacuous: the quotient does not collapse
   everything.  The argument does not read the chain and conclude False
   from its shape — no analysis of chains could, a chain being data with
   three constructors and no contradictory one; it runs the endpoint
   invariant [discrete_zigzag_eq] (itself an induction over the chain, but
   one whose conclusion is an EQUALITY) and then discriminates that
   equality in [bool].

--------
... 并且它的 π₀ 真正地将它的两个对象分开，这就是使得该构造非空的原因：商不会将所有东西压缩掉。该论证不会读取链并从其形状得出 False —— 没有对链的分析能够做到这一点，因为链是具有三个构造函数且没有矛盾构造的数据；它运行端点不变量 [discrete_zigzag_eq]（它本身是对链的归纳，但其结论是一个等式），然后在 [bool] 中对该等式进行区分。
*)
Theorem pi0_bool_separates :
  @equiv _ (pi0 (DiscreteCat bool)) true false → False.
Proof.
  intro s.
  pose proof (discrete_zigzag_eq (DiscreteCat_Discrete bool) s) as H.
  discriminate H.
Qed.

(* The component of [true] excludes [false], by the same invariant. / [true] 的组件排除了 [false]，根据相同的不变量。 *)
Theorem component_bool_excludes_false :
  sobj (DiscreteCat bool) (ComponentSub (DiscreteCat bool) true) false
    → False.
Proof.
  intro s.
  pose proof (discrete_zigzag_eq (DiscreteCat_Discrete bool) s) as H.
  discriminate H.
Qed.

(*
A functor from a connected category to a disconnected one.  This is what
   makes [connected_image] the honest statement of the first section: its
   conclusion holds here, while [Connected (DiscreteCat bool)] is
   refutable.  So the implication “C is connected and there is a functor
   C ⟶ D, therefore D is connected” is FALSE, and the surjectivity
   hypothesis of [eso_connected] cannot simply be dropped.  The witness is
   sharp in the sense that matters: that hypothesis genuinely FAILS here
   ([One_to_bool_not_ESO] below).  It is not sharp in any finer sense —
   whether some hypothesis weaker than essential surjectivity would do is
   left open, and nothing is claimed about this functor's fullness or
   faithfulness.

--------
从一个连通范畴到一个非连通范畴的函子。这就是使得 [connected_image] 成为第一部分诚实陈述的原因：它的结论在这里成立，而 [Connected (DiscreteCat bool)] 是可以反驳的。因此蕴含“C 是连通的并且存在一个函子 C ⟶ D，因此 D 是连通的”是错误的，并且 [eso_connected] 的满射假设不能简单地被取消。这个例子在重要意义上是尖锐的：在这里该假设确实失败（见下文 [One_to_bool_not_ESO]）。它在更细的意义上并不尖锐——是否存在比本质满射更弱的假设可行仍未确定，也没有对这个函子的充足性或忠实性作任何声明。
*)
Program Definition One_to_bool : _1 ⟶ DiscreteCat bool := {|
  fobj := fun _ => true;
  fmap := fun _ _ _ => eq_refl
|}.

Definition image_connected_not_connected :
  (∀ x y : _1, ZigZag (One_to_bool x) (One_to_bool y))
    * (Connected (DiscreteCat bool) → False) :=
  (connected_image One_to_bool One_Connected, DiscreteCat_bool_not_connected).

(*
... and the hypothesis of [eso_connected] genuinely fails at it: an
   essential-surjectivity witness would supply an isomorphism
   [true ≅ false] in [DiscreteCat bool], whose forward leg is an equality
   of booleans.

--------
... 而 [eso_connected] 的假设在这方面确实失败：一个本质满射的证据会提供一个同构 [true ≅ false] 在 [DiscreteCat bool] 中，其正向部分是布尔值的相等。
*)
Theorem One_to_bool_not_ESO :
  EssentiallySurjective One_to_bool → False.
Proof.
  intro E.
  pose proof (to (@eso_iso _ _ One_to_bool E false)) as H.
  discriminate H.
Qed.

(**
** Connected diagrams (Riehl §3.4)

   Riehl's running definition derives a notion for DIAGRAMS from the one
   for categories: a diagram is connected when its INDEXING category is.
   That is the form her Propositions 3.4.8 and 3.6.5 quantify over, and it
   is what makes “a connected limit is computed from any one component” a
   statement one can even write down.

   It is a property of the SHAPE alone.  Nothing here looks at the target,
   which is why [ConnectedDiagram] is a plain definition unfolding to the
   indexing category's own predicate rather than a new inductive, and why
   [connected_diagram_reindex] below is the identity function: two
   diagrams on one shape are connected together or not at all.

   The two readings of connectedness separate here exactly as they do for
   categories — see [connected_readings_differ] above — so both are named,
   and the passage between them is the categorical one applied at the
   index.  READ THE NAMES CAREFULLY, BECAUSE THE UNQUALIFIED ONE IS NOT
   HERS: Riehl's own definition is the INHABITED one (“a category is
   connected if it is NON-EMPTY and any two objects are joined by a finite
   zigzag”), so the notion this section is named after is
   [ConnectedNonemptyDiagram].  [ConnectedDiagram] is the BARE in-tree
   reading, which holds vacuously at the empty shape.  The nomenclature is
   inherited from Structure/Groupoid/Connected.v rather than chosen here,
   and it is disclosed rather than repaired: renaming the donor's
   [Connected] is out of scope for this file.

--------
** 连通图（Riehl §3.4）

Riehl 的运行定义从范畴的概念中得出图的概念：当其索引范畴是连通时，一个图就是连通的。这就是她命题 3.4.8 和 3.6.5 所量化的形式，也是使“一个连通的极限可以从任意一个分量计算出来”成为可以书写的陈述的原因。

这是形状自身的一个属性。这里没有关注目标，这就是为什么 [ConnectedDiagram] 是一个普通定义，展开到索引范畴自身的谓词而不是一个新的归纳，以及为什么下面的 [connected_diagram_reindex] 是恒等函数：在一个形状上的两个图表要么彼此连接，要么根本不连接。

这里连接性的两种读法完全像范畴的情况一样分开——见上文的 [connected_readings_differ]——所以两者都有名字，并且它们之间的通道是应用在指标上的范畴化的。仔细阅读这些名称，因为未加限定的那个并不是她的：Riehl 自己的定义是“有对象的”（INHABITED）定义（“一个范畴是连接的，如果它非空并且任意两个对象之间存在有限之字形的连接”），所以本节名称所依的概念是 [ConnectedNonemptyDiagram]。[ConnectedDiagram] 是裸树内的读法，在空形状下是空虚成立的。命名法是继承自 Structure/Groupoid/Connected.v，而不是在此处选择的，并且是公开的而非修正的：重命名捐赠者的 [Connected] 不在此文件的处理范围内。
*)

Definition ConnectedDiagram {J C : Category} (D : J ⟶ C) : Type :=
  Connected J.

Definition ConnectedNonemptyDiagram {J C : Category} (D : J ⟶ C) : Type :=
  ConnectedNonempty J.

(*
Each IS the indexing category's predicate, by conversion.  Neither is a
   tautology: each names the new constant on one side and the donor
   predicate applied to the index on the other.

--------
通过转换，每一个都是索引范畴的谓词。两者都不是重言式：每一个在一侧命名新的常量，在另一侧应用于索引的供体谓词。
*)
Example connected_diagram_is_index {J C : Category} (D : J ⟶ C) :
  ConnectedDiagram D = Connected J := eq_refl.

Example connected_nonempty_diagram_is_index {J C : Category} (D : J ⟶ C) :
  ConnectedNonemptyDiagram D = ConnectedNonempty J := eq_refl.

(* The inhabited reading implies the bare one, at the index. / 有住的阅读意味着裸的阅读，在索引处。 *)
Definition connected_diagram_of_nonempty {J C : Category} (D : J ⟶ C)
  (K : ConnectedNonemptyDiagram D) : ConnectedDiagram D :=
  connected_of_nonempty K.

(*
Connectedness never looks at the target: any two diagrams on the same
   shape are connected together or not at all.  The proof is the identity,
   which is the honest content of the remark.

--------
连通性从不看目标：同一形状上的任意两个图表要么相互连通，要么根本不连通。证明就是恒等式，这正是该备注的真实内容。
*)
Definition connected_diagram_reindex {J C E : Category}
  (D : J ⟶ C) (D' : J ⟶ E) (K : ConnectedDiagram D) : ConnectedDiagram D'
  := K.

(*
π₀ of the shape is a subsingleton exactly when the diagram is
   connected — the [connected_iff_pi0_subsingleton] biconditional read at
   the index.

--------
当图是连通的时，形状的 π₀ 恰好是一个子单子——在索引处读取的 [connected_iff_pi0_subsingleton] 双条件。
*)
Definition connected_diagram_pi0 {J C : Category} (D : J ⟶ C)
  (K : ConnectedDiagram D) : pi0_subsingleton J :=
  connected_pi0_subsingleton K.

Definition pi0_connected_diagram {J C : Category} (D : J ⟶ C)
  (H : pi0_subsingleton J) : ConnectedDiagram D :=
  pi0_subsingleton_connected H.

(*
Witnesses, positive and negative, on the two shapes this file already
   exercises.  Both are pure instantiation: no new connectedness argument
   is made for a diagram that was not already made for its shape.

--------
证人，对这个文件已经处理的两种形状的正面和负面。两者都是纯粹的实例化：对于一个图形，没有提出新的连通性论证，这些论证已经针对其形状提出过。
*)
Definition Parallel_ConnectedDiagram {C : Category} (D : Parallel ⟶ C) :
  ConnectedDiagram D := Parallel_Connected.

Definition bool_diagram_not_connected {C : Category}
  (D : DiscreteCat bool ⟶ C) : ConnectedDiagram D → False :=
  DiscreteCat_bool_not_connected.

(*
NOT delivered here: no connected LIMIT.  The reason connected diagrams
   matter — Riehl's Propositions 3.4.8 and 3.6.5, where the coslice
   projection creates colimits and a connected limit is computed from one
   component — needs limit machinery this file does not touch, and neither
   proposition is stated.  What is supplied is the hypothesis they
   quantify over.

--------
未在此处给出：没有连通极限。连通图的重要性原因 —— Riehl 的命题 3.4.8 和 3.6.5，其中余切投影生成余极限，并且连通极限从一个分量计算 —— 需要本文件未涉及的极限工具，而且两个命题都未被陈述。所提供的是它们所量化的假设。
*)
