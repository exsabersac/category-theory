Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(*
 The single-object separator, reconciled with Theory/Concrete.v

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/well-pointed+category

 Issue #447 recorded as its verified current state that the tree
 carried no separating vocabulary at all, only the dual [Cogenerator]
 of Adjunction/SAFT.v.  That was STALE.  Measured in this worktree
 with grep -rn 'Separator' --include='*.v', Theory/Concrete.v has
 carried Awodey's single-object notion since the concreteness
 development landed:

 Class Separator (t : C), the same clause as [IsSeparator]
 with the two objects implicit, presented as a one-field class
 so that instance resolution can find it;
 Concrete_of_Separator, which turns a separator into a
 concrete structure whose underlying functor is Hom(t, -) --
 and whose [underlying_faithful] obligation IS the forward
 half of Awodey's characterization, proved but not named;
 Separator_of_Faithful, the backward half, named and proved;
 WellPointedCategory C, the separator condition at the
 terminal object (Awodey's own case, global elements);
 Sets_Separator, the witness the issue asks for -- the
 terminal object of [Sets] separates -- with [Sets_WellPointed]
 and [Sets_empty_not_Separator], the refutation keeping the
 class from reading as content-free.

 So this issue's genuinely new material is the FAMILY notion
 ([Generator]), the joint-faithfulness characterization in both
 directions, the transport lemmas, and the duality bridge -- all in
 Structure/Generator.v and Structure/Generator/Dual.v.  What is left
 is to keep the tree from ending with two unrelated spellings of one
 condition, and that is this file: the two bridges below are both
 [:=] terms, since [Separator]'s field and [IsSeparator]'s body differ
 only in which arguments are implicit.

 WHY A THIRD FILE, MEASURED.  Structure/Generator.v does NOT require
 Theory/Concrete.v, and the reason is a name clash that would
 otherwise be imposed on every later file: [bool_setoid_object] is
 defined twice in the tree, at Instance/Sets.v and at
 Theory/Concrete.v (two different [SetoidObject] terms for the
 two-element setoid), so importing Concrete after Sets shadows the
 Sets one.  Structure/Generator.v imports Instance/Sets.v and is the
 interface the witnesses for this issue are built against, so the
 shadowing is contained here instead, where nothing uses either
 spelling.  The same isolation argument as Structure/Generator/Dual.v,
 for a different hazard.

 UNIVERSES, measured with [Set Printing Universes. About ...].  The
 two bridges carry only [u <= u1] and [u0 <= u1], the bound by which
 [IsSeparator]'s result level dominates the category's two levels;
 [Separator] itself (Theory/Concrete.v) prints an EMPTY block.
 No constant here is pinned to [Set].

 NOT DELIVERED.  No witness: this file builds no separator of any
 category.  The [Sets] witness is Instance/Sets/Generator.v, which
 proves the terminal-object statement directly and ALSO reads
 Theory/Concrete.v's [Sets_Separator] through
 [IsSeparator_of_Separator] as [Sets_terminal_separates_from_Concrete]
 (a first draft of this file carried that read-through itself, under
 the names [Sets_terminal_IsSeparator] / [Sets_terminal_Generator],
 which collided with the witness file's own [Sets_terminal_Generator];
 integration kept the witness file's).  No statement about
 [Concrete] itself: nothing here says a category with a separating
 FAMILY is concrete (it is not, in general -- a family of
 representables is jointly faithful, which is weaker than any single
 functor to [Sets] being faithful, and the coproduct that would
 assemble them is unsound for this purpose, as Structure/Generator.v's
 header records).  No instance declarations: the bridges are plain
 definitions, so declaring an [IsSeparator] does not make
 [Separator]'s instance resolution fire, and vice versa. 

 --------
 单对象分隔符，与 Theory/Concrete.v 调和

 nLab:   https://ncatlab.org/nlab/show/separator 
 nLab:   https://ncatlab.org/nlab/show/well-pointed+category 

 问题 #447 被记录为其已验证的当前状态，即该树根本没有携带任何分隔词汇，仅有 Adjunction/SAFT.v 的复数 [Cogenerator]。这已经过时。在本工作树中，通过 grep -rn 'Separator' --include='*.v' 测量，Theory/Concrete.v 自从具体性开发开始以来就采用了 Awodey 的单对象概念:类分隔符（t : C），与 [IsSeparator] 相同的条款，两个对象是隐式的，以单字段类的形式呈现，以便实例解析可以找到它；
 Concrete_of_Separator，将分隔符转换为一个具体结构，其底层函子是 Hom(t, -) —— 其 [underlying_faithful] 义务是 Awodey 特征的前半部分，已证明但未命名；
 Separator_of_Faithful，后半部分，已命名并证明；
 WellPointedCategory C，在终对象处的分隔符条件（Awodey 自身的情况，全局元素）；
 Sets_Separator，问题要求的证据 —— [Sets] 的终对象分隔 —— 以及 [Sets_WellPointed] 和 [Sets_empty_not_Separator]，反证保持类不能被解读为无内容。所以这个问题真正的新内容是 FAMILY 概念（[Generator]）、双向的联合忠诚特性描述、传输引理以及对偶桥——全部在 Structure/Generator.v 和 Structure/Generator/Dual.v 中。剩下要做的是防止树以一个条件的两个不相关拼写结束，而这就是这个文件：下面的两个桥都是 [:=] 项，因为 [Separator] 的字段和 [IsSeparator] 的主体仅在哪些参数是隐式的方面不同。为什么需要第三个文件，Measure。Structure/Generator.v 并不需要 Theory/Concrete.v，其原因是名字冲突，否则会影响到每一个后续文件：[bool_setoid_object] 在树中被定义了两次，分别在 Instance/Sets.v 和 Theory/Concrete.v（针对两个元素的集合体有两个不同的 [SetoidObject] 项），所以在导入 Concrete 后会覆盖 Sets 中的定义。Structure/Generator.v 导入 Instance/Sets.v，并且是针对该问题的证人构建接口，所以这里的覆盖被限制在此处，因为没有任何地方使用这两种拼写。与 Structure/Generator/Dual.v 相同的隔离论证，用于不同的潜在风险。用 [Set Printing Universes. About ...] 测量的宇宙。这两座桥只承载 [u <= u1] 和 [u0 <= u1]，[IsSeparator] 的结果等级主导了该类别的两个等级；[Separator] 本身（Theory/Concrete.v）打印一个空块。这里没有常量固定到 [Set]。未交付。没有证人：此文件没有构建任何类别的分隔符。[Sets] 证人是 Instance/Sets/Generator.v，它直接证明了终端对象的陈述，并且还通过 [IsSeparator_of_Separator] 将 Theory/Concrete.v 的 [Sets_Separator] 读取为 [Sets_terminal_separates_from_Concrete]（此文件的初稿自己进行了这种读取，名称为 [Sets_terminal_IsSeparator] / [Sets_terminal_Generator]，与证人文件自己的 [Sets_terminal_Generator] 冲突；整合时保留了证人文件的）。关于 [Concrete] 本身没有说明：这里没有任何内容表明具有分离 FAMILY 的范畴是具体的（一般来说不是——一族可表示的对象是联合忠实的，这比单个函子到 [Sets] 的忠实性要弱，而用于组合它们的余积在此目的上是不可行的，如 Structure/Generator.v 的头文件所记录的）。没有实例声明：这些桥只是普通定义，因此声明一个 [IsSeparator] 并不会触发 [Separator] 的实例解析，反之亦然。
*)

Section Bridge.

Context {C : Category}.

(* * ** The two spellings of Awodey's condition / * ** 奥沃迪状况的两种拼写方式 *)

(*
 [Separator] (Theory/Concrete.v) is the class form, whose field
 [separates] takes its two objects implicitly; [IsSeparator]
 (Structure/Generator.v) is the Type-valued form that the
 characterizations consume as a function.  Nothing moves but the
 packaging. 

 --------
 [Separator]（Theory/Concrete.v）是类形式，其字段 [separates] 隐式地接受它的两个对象；[IsSeparator]（Structure/Generator.v）是类型值形式，特征作为函数使用它。没有什么移动，只有打包。
*)
Definition Separator_of_IsSeparator (c : C) (H : IsSeparator c) :
  Separator c := @Build_Separator C c (fun x y f g E => H x y f g E).

Definition IsSeparator_of_Separator (c : C) (S : Separator c) :
  IsSeparator c := fun x y f g E => @separates C c S x y f g E.

(*
 The forward half of Awodey's characterization is already in the tree,
 though only as the [underlying_faithful] obligation of
 Theory/Concrete.v's concretization.  Recovering it that way gives
 the same statement as Structure/Generator.v's [separator_faithful],
 and this is the check that the two developments agree. 

 --------
 Awodey 描述的前半部分已经在树中，尽管它仅作为 Theory/Concrete.v 的具体化的 [underlying_faithful] 义务。以这种方式恢复它会得到与 Structure/Generator.v 的 [separator_faithful] 相同的陈述，这是检查这两个发展是否一致的方法。
*)
Example separator_faithful_via_concrete (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @underlying_faithful C
    (@Concrete_of_Separator C c (Separator_of_IsSeparator c H)).

End Bridge.
