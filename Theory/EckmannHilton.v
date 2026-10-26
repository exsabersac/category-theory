Require Import Category.Lib.

Generalizable All Variables.

(** * The Eckmann–Hilton argument / * 埃克曼–希尔顿论证 *)

(*
nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Wikipedia: https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument
   Paper:     Eckmann, Hilton, “Group-like structures in general categories
              I. Multiplications and comultiplications”, Mathematische
              Annalen 145, 1962
   Paper:     Eckmann, Hilton, “Structure maps in group theory”, Fundamenta
              Mathematicae 50, 1961 (Theorem 1.12)
   Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              §II.5 Exercise 5 (printed p. 45)

   Suppose one carrier bears two binary operations, each with a two-sided
   unit, and suppose the two operations INTERCHANGE: evaluating a 2x2 array
   rows-first agrees with evaluating it columns-first,

       f (g a b) (g c d)  ≈  g (f a c) (f b d).

   Then the two units coincide, the two operations coincide, and the single
   operation that remains is commutative and associative.  Nothing else is
   assumed — no associativity, no commutativity, not even that either
   operation is a monoid on its own.  Both laws are OUTPUTS.

   This file states and proves exactly that, over a bare setoid.  It is
   deliberately PRE-CATEGORICAL: its only import is [Category.Lib], and in
   particular it does not import [Category.Theory.Category].  The argument
   never mentions objects, morphisms, or composition; it is a fact about a
   set with two interchanging unital operations, and the categorical
   instances below are instances, not the content.

--------
nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Wikipedia: https://en.wikipedia.org/wiki/Eckmann%E2%80%93Hilton_argument
   Paper:     Eckmann, Hilton, “Group-like structures in general categories
              I. Multiplications and comultiplications”, Mathematische
              Annalen 145, 1962
   Paper:     Eckmann, Hilton, “Structure maps in group theory”, Fundamenta
              Mathematicae 50, 1961 (Theorem 1.12)
   Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              §II.5 Exercise 5 (printed p. 45)

   设一载体带有两个二元运算，各有双侧单位，且两运算*交换* (interchange)：对 2×2 数组
   先按行求值与先按列求值一致，

       f (g a b) (g c d)  ≈  g (f a c) (f b d).

   则两单位重合、两运算重合，剩下的单一运算交换且结合。此外一无所设——无结合律、
   无交换律，甚至不要求任一运算自身是幺半群。两定律都是*输出*。

   本文件在裸 setoid 上恰陈述并证明这一点。它刻意是*前范畴的*：仅导入 [Category.Lib]，
   尤其不导入 [Category.Theory.Category]。论证从不提及对象、态射或复合；它是关于带两个
   交换单位运算的集合的事实，下文范畴实例是实例而非内容。
*)

(*
Where the argument comes from, and what it is used for

   Eckmann and Hilton isolated the principle while studying H-spaces and
   the dual “H-cospaces”: a space with a multiplication and a
   comultiplication that are compatible in the above sense has an abelian
   fundamental structure.  The 1961 paper in Fundamenta Mathematicae proves
   it for group-like structure maps (Theorem 1.12); the 1962 Mathematische
   Annalen paper generalises multiplications and comultiplications to an
   arbitrary category.  The argument is now folklore, and it explains a
   long list of otherwise unrelated facts:

   - The higher homotopy groups π_n(X, x) for n ≥ 2 are abelian.  Two
     concatenations of n-cubes are available in that range (along any two
     of the n coordinate directions), they share the constant map as unit,
     and they interchange because the two directions are independent.

   - A monoid object in the category of monoids is a commutative monoid;
     a group object in Grp is an abelian group.  The ambient
     multiplication and the internal one interchange because the internal
     one is a homomorphism for the ambient one.  This is the reason the
     tower of “monoids in monoids in ...” collapses at the second rung, so
     that further categorification must add BRAIDING rather than a further
     multiplication.

   - The endomorphisms of an identity — 2-cells on an identity 1-cell in a
     2-category, the endomorphism monoid of the unit object of a monoidal
     category — form a COMMUTATIVE monoid.  (In this tree “the centre of a
     monoidal category” names the Drinfeld or premonoidal centres,
     Structure/Monoidal/Drinfeld.v — categories, not monoids — so that
     phrase is deliberately avoided here.)  Vertical and
     horizontal composition of such cells interchange (that is the middle
     four interchange law) and there they genuinely share a unit, which is
     precisely the special position that makes the collapse bite.

   In this library the principle is cited in several background essays and
   is now proved once here:

   - Structure/Semiadditive.v derives commutativity and associativity of
     the convolution addition on hom-setoids from the interchange law
     between its two convolutions [conv] and [conv_pr]; those three
     lemmas ([conv_conv_pr], [conv_comm], [conv_assoc]) are instances of
     this file's [eh_ops], [eh_comm] and [eh_assoc].
   - Instance/Cat/TwoCategory.v's [NatBase_centre] exhibits the collapse
     concretely: the 2-cells on the identity functor of the delooping of
     (ℕ, +) compose to the same thing vertically and horizontally, and
     both composites compute to addition (by [eq_refl]).
   - Theory/TwoCategory.v explains why a 2-category does not
     degenerate: its two compositions have DIFFERENT units in general, so
     the argument only bites where the units collapse.
   - Structure/Monoid.v (the microcosm remark), Structure/Group.v
     (group objects in Grp are abelian), Structure/Abelian.v,
     Structure/Monoidal/Braided.v and Structure/Monoidal/Proofs.v
     all appeal to the principle in prose.

   SCOPE, stated precisely.  The theorem below takes SEPARATE units, one
   for each operation, and DERIVES their coincidence ([eh_units]).  That is
   strictly more general than the in-tree instance it now serves:
   Structure/Semiadditive.v's two convolutions both have [zero_mor] as
   unit, so the coincidence there is [reflexivity] and that file never
   needed the lemma.  A reader who only wants the common-unit form may
   instantiate with [ug := uf] and ignore [eh_units].

   The hypotheses are Section variables rather than fields of a class, so
   after [End] every lemma below takes them as explicit arguments.  That is
   the intended interface: a consumer supplies its two operations, its two
   units, the four unit laws and the interchange law, and reads off the
   conclusions.

--------
论证的来源和用途

Eckmann 和 Hilton 在研究 H 空间时分离出了该原理
 对偶“H-余空间”：一个带有乘法和一个的空间
 在上述意义上兼容的余乘具有阿贝尔
 基本结构。 1961 年发表在《数学基础》上的论文证明
 它用于类群结构图（定理 1.12）； 1962年数学
 Annalen 论文将乘法和余乘推广为
 任意范畴。 这个说法现在已经成为民间传说，它解释了一个问题
 一长串其他不相关的事实：

- n ≥ 2 时的较高同伦群 π_n(X, x) 是阿贝尔群。 两个
 n 立方体的串联在该范围内可用（沿着任意两个
 n 个坐标方向），它们共享常量映射作为单位，
 并且它们互换，因为两个方向是独立的。

- 幺半群范畴中的幺半群对象是可交换幺半群；
 Grp 中的群对象是阿贝尔群。 环境
 乘法和内部一互换，因为内部
 一种是环境同态。 这就是原因
 “monoids in monoids in ...”的塔在第二级倒塌，所以
 进一步的分类必须添加 BRAIDING 而不是进一步的
 乘法。

- 同一性的自同态 — 同一性中的 2 细胞对 1 细胞
 2-范畴，幺半群的单位对象的自同态幺半群
 范畴——形成一个可交换幺半群。 （在这棵树中“a的中心
 幺半群范畴”命名为 Drinfeld 或前幺半群中心，
 Structure/Monoidal/Drinfeld.v — 范畴，而不是幺半群 — 因此
 这里故意避免使用这个短语。）垂直和
 这种细胞交换的水平组成（即中间
 四个交换律），并且它们真正共享一个单位，即
 正是这个特殊的位置让崩塌咬住了。

在这个库中，多篇背景文章引用了该原理，并且
 现在在这里证明一次：

- Structure/Semiadditive.v 导出以下的交换律和结合律
 根据交换律对 hom-setoids 进行卷积加法
 在其两个卷积 [conv] 和 [conv_pr] 之间； 那三个
 引理（[conv_conv_pr]、[conv_comm]、[conv_assoc]）是以下实例
 该文件是 [eh_ops]、[eh_comm] 和 [eh_assoc]。 
- Instance/Cat/TwoCategory.v 的 [NatBase_centre] 出现崩溃
 具体来说：去循环的恒等函子上的 2 个单元格
 (ℕ, +) 垂直和水平组合相同的东西，并且
 两种复合材料都计算加法（通过 [eq_refl]）。 
- Theory/TwoCategory.v 解释了为什么 2 范畴不
 简并：它的两种成分通常具有不同的单位，所以
 争论只在单位崩溃的地方起作用。 
- Structure/Monoid.v（微观评论）、Structure/Group.v
 （Grp 中的组对象是阿贝尔的），Structure/Abelian.v，
 Structure/Monoidal/Braded.v 和 Structure/Monoidal/Proofs.v
 所有这些都诉诸散文中的原则。

范围，准确说明。 下面的定理采用单独的单位，一
 对于每个操作，并导出它们的重合度 ([eh_units])。 那就是
 严格来说比它现在服务的树内实例更通用：
 Structure/Semiadditive.v 的两个卷积都有 [zero_mor] 作为
 单位，所以巧合的是 [reflexivity] 并且该文件永远不会
 需要引理。 只想要公共单位形式的读者可能会
 使用 [ug := uf] 实例化并忽略 [eh_units]。

假设是节变量而不是类的字段，所以
 在 [End] 之后，下面的每个引理都将它们作为显式参数。 那就是
 预期的接口：消费者提供其两个操作，其两个
 单位、四个单位定律和互换定律，并读出
 结论。
*)

(*
Lib.v sets [Default Proof Using “Type”], which keeps only the Section
   variables occurring in a lemma's STATEMENT.  Every statement here
   mentions only [f], [g], [uf] and [ug]; the respectfulness, unit and
   interchange hypotheses are consumed in the PROOFS alone, so they must be
   requested explicitly.  Declaring “All” once is clearer than repeating a
   variable list on each lemma, and it makes the discharged interface
   uniform: every lemma below takes the same seven hypotheses.

--------
看来进入劳动力市场时,
可以是在 让我看看 lemma 语句中的变量吟可以是每个 让我看看
军民合作要在《公约》第10为一个缔约方的 你很了解《公约》第 October 条。
该死 页 
明确要求。 Tess. 一次宣布“ Tess”比一次更清晰
的变量的内容充电接口 你是
统一: 下方研究成果所面对的 你有什么她在做下方的人民?
*)
Local Set Default Proof Using "All".

Section EckmannHilton.

Context {A : Type}.
Context `{sA : Setoid A}.

(* The two operations and their units. / 这两个操作及其单位。 *)
Context (f g : A → A → A).
Context (uf ug : A).

(*
Both operations respect the carrier's equivalence.  These are stated as
   [Proper] hypotheses so that setoid rewriting can work underneath them.
   They are Section hypotheses, NOT global instances: [Context] registers a
   class-typed binder as a local instance for the duration of the Section,
   which is what makes [rewrite] see them, and at [End] they discharge as
   ordinary EXPLICIT arguments rather than as instances anything downstream
   could resolve by accident.

--------
这两个操作都遵循载体的等价性。它们被声明为 [Proper] 假设，以便在它们之下可以进行集合重写。它们是 Section 假设，而不是全局实例：[Context] 将一个类类型的绑定器注册为 Section 期间的本地实例，这就是为什么 [rewrite] 能看到它们，并且在 [End] 时，它们作为普通的显式参数解除，而不是作为任何下游可能意外解析的实例。
*)
Context (f_respects : Proper (equiv ==> equiv ==> equiv) f).
Context (g_respects : Proper (equiv ==> equiv ==> equiv) g).

(*
[uf] is a two-sided unit for [f], and [ug] one for [g].  Note that
   nothing yet relates the two.

--------
[uf] 是 [f] 的双面单元，而 [ug] 是 [g] 的单面单元。请注意，目前两者之间尚无关联。
*)
Context (f_unit_left  : ∀ a, f uf a ≈ a).
Context (f_unit_right : ∀ a, f a uf ≈ a).
Context (g_unit_left  : ∀ a, g ug a ≈ a).
Context (g_unit_right : ∀ a, g a ug ≈ a).

(*
The interchange law.  The orientation is the one Structure/Semiadditive.v
   proves for its convolutions ([conv_interchange]): [f] is the operation
   applied LAST on the left and FIRST on the right.

--------
交换律。方向是 Structure/Semiadditive.v 为其卷积证明的那个（[conv_interchange]）：[f] 是在左边最后应用、在右边首先应用的操作。
*)
Context (interchange : ∀ a b c d, f (g a b) (g c d) ≈ g (f a c) (f b d)).

(*
Eckmann–Hilton, step one: the two units coincide.

   Read the interchange law at the array whose entries are the two units
   arranged antidiagonally,

       ( uf  ug )
       ( ug  uf ).

   Evaluating with [g] first collapses both rows to [uf] (because [ug] is
   [g]'s unit), and then [f] collapses [f uf uf] to [uf].  Evaluating with
   [f] first collapses both columns to [ug] (because [uf] is [f]'s unit),
   and then [g] collapses [g ug ug] to [ug].  Interchange says the two
   readings agree.

--------
Eckmann–Hilton，第一步：两个单位重合。

   在其元素按反对角线排列的数组上读取交换律，

       ( uf  ug )
       ( ug  uf )。

   如果先用 [g] 评估，则会将两行都折叠为 [uf]（因为 [ug] 是 [g] 的单位），然后 [f] 会将 [f uf uf] 折叠为 [uf]。 
   如果先用 [f] 评估，则会将两列都折叠为 [ug]（因为 [uf] 是 [f] 的单位），然后 [g] 会将 [g ug ug] 折叠为 [ug]。 
   交换律表明这两种读法是一致的。
*)
Lemma eh_units : uf ≈ ug.
Proof.
  transitivity (f (g uf ug) (g ug uf)).
  - rewrite g_unit_right, g_unit_left.
    now rewrite f_unit_left.
  - rewrite interchange.
    rewrite f_unit_left, f_unit_right.
    now rewrite g_unit_left.
Qed.

(*
With the units identified, [uf] is a two-sided unit for [g] as well, so
   the padding arguments below can be written with a single unit.

--------
确定了单元后，[uf] 对 [g] 也是一个双面单元，因此下面的填充参数可以用一个单元来编写。
*)
Lemma eh_common_unit_left (a : A) : g uf a ≈ a.
Proof.
  rewrite eh_units.
  now rewrite g_unit_left.
Qed.

Lemma eh_common_unit_right (a : A) : g a uf ≈ a.
Proof.
  rewrite eh_units.
  now rewrite g_unit_right.
Qed.

(*
Eckmann–Hilton, step two: the two operations coincide.

   In the three chains that follow, [1] abbreviates the common unit — [uf],
   which by [eh_common_unit_left]/[eh_common_unit_right] is now a two-sided
   unit for [g] as well.

   Pad [a] and [b] with the common unit so that both become [g]-composites,
   then push the interchange law through and strip the [f]-units:

       f a b  ≈  f (g a 1) (g 1 b)  ≈  g (f a 1) (f 1 b)  ≈  g a b.

--------
Eckmann–Hilton，第二步：两个运算一致。

在接下来的三个链条中，[1] 代表共同单位 — [uf]，通过 [eh_common_unit_left]/[eh_common_unit_right]，现已成为 [g] 的双边单位。

用共同单位填充 [a] 和 [b]，使两者都成为 [g] 复合体，然后应用交换律并去除 [f] 单位：

    f a b  ≈  f (g a 1) (g 1 b)  ≈  g (f a 1) (f 1 b)  ≈  g a b。
*)
Lemma eh_ops (a b : A) : f a b ≈ g a b.
Proof.
  transitivity (f (g a uf) (g uf b)).
  - now rewrite eh_common_unit_right, eh_common_unit_left.
  - rewrite interchange.
    now rewrite f_unit_right, f_unit_left.
Qed.

(*
Eckmann–Hilton, step three: the operation is commutative.

   The same padding, with the units placed on the other side, so that
   interchange transposes the two arguments; the last step is [eh_ops]
   read backwards:

       f a b  ≈  f (g 1 a) (g b 1)  ≈  g (f 1 b) (f a 1)  ≈
       g b a  ≈  f b a.

--------
Eckmann–Hilton，第三步：这个运算是交换的。

相同的填充，单位放在另一边，因此交换会对换两个参数；最后一步是 [eh_ops] 倒着读：

    f a b  ≈  f (g 1 a) (g b 1)  ≈  g (f 1 b) (f a 1)  ≈
    g b a  ≈  f b a。
*)
Lemma eh_comm (a b : A) : f a b ≈ f b a.
Proof.
  transitivity (f (g uf a) (g b uf)).
  - now rewrite eh_common_unit_left, eh_common_unit_right.
  - rewrite interchange.
    rewrite f_unit_left, f_unit_right.
    now rewrite <- eh_ops.
Qed.

(*
Eckmann–Hilton, step four: the operation is associative.

   Pad only the first argument, and read interchange in both directions
   around the intermediate term [f (g a 1) (g b c)]:

       f (f a b) c  ≈  g (f a b) (f 1 c)  ≈  f (g a 1) (g b c)  ≈
       f a (g b c)  ≈  f a (f b c).

--------
埃克曼–希尔顿，第四步：运算是结合的。

   仅填充第一个参数，并在中间项 [f (g a 1) (g b c)] 周围两个方向上读取互换：

       f (f a b) c  ≈  g (f a b) (f 1 c)  ≈  f (g a 1) (g b c)  ≈
       f a (g b c)  ≈  f a (f b c).
*)
Lemma eh_assoc (a b c : A) : f (f a b) c ≈ f a (f b c).
Proof.
  transitivity (f (g a uf) (g b c)).
  - rewrite interchange.
    rewrite f_unit_left.
    now rewrite <- eh_ops.
  - rewrite eh_common_unit_right.
    now rewrite <- eh_ops.
Qed.

(*
The [g]-side readings.  Since the operations coincide these are one
   rewrite away, but they are what a consumer holding only [g] wants.

--------
[g] 端的读数。由于操作相符，它们只差一次重写，但它们正是仅持有 [g] 的消费者想要的。
*)
Lemma eh_g_comm (a b : A) : g a b ≈ g b a.
Proof.
  rewrite <- !eh_ops.
  now rewrite eh_comm.
Qed.

Lemma eh_g_assoc (a b c : A) : g (g a b) c ≈ g a (g b c).
Proof.
  rewrite <- !eh_ops.
  now rewrite eh_assoc.
Qed.

(*
The theorem, packaged.

   PACKAGING CHOICE: the library's `≈` is a [crelation], i.e. Type-valued,
   so the four conclusions cannot be conjoined with [and].  They are
   conjoined with the library's [∧], which is [prod] (Lib/Foundation.v),
   right-associated.  A record was the alternative; a nested product was
   chosen because it needs no new inductive type and its components are
   reachable with the ordinary [fst]/[snd] of a pair.  The four components
   are, in order, [eh_units], [eh_ops], [eh_comm] and [eh_assoc]; the
   [g]-side corollaries are deliberately left out, being immediate from the
   second component.

--------
定理，打包好了。

   打包选择：库里的 `≈` 是一个 [crelation]，即类型值，
   因此四个结论不能用 [and] 连接。它们是
   用库里的 [∧] 连接的，这个是 [prod]（Lib/Foundation.v），
   右结合。记录是一种替代方案；选择嵌套积是因为它不需要新的归纳类型，其组件可通过普通的 [fst]/[snd] 对访问。四个组件
   按顺序是 [eh_units]、[eh_ops]、[eh_comm] 和 [eh_assoc]；
   [g] 方面的推论故意省略，因为它们可以直接从第二个组件得出。
*)
Definition eckmann_hilton :
  (uf ≈ ug)
    ∧ (∀ a b : A, f a b ≈ g a b)
    ∧ (∀ a b : A, f a b ≈ f b a)
    ∧ (∀ a b c : A, f (f a b) c ≈ f a (f b c)) :=
  (eh_units, (eh_ops, (eh_comm, eh_assoc))).

End EckmannHilton.
