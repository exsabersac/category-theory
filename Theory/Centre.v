Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * The centre of a category / * 一个范畴的中心 *)

(*
nLab:      https://ncatlab.org/nlab/show/center+of+a+category
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              §II.5 Exercise 8 (printed p. 45)          [maclane:II.5:ex8]
   Book:      Riehl, “Category Theory in Context”, §1.7 Exercise 1.7.iv
              (printed p. 51)                           [riehl:1.7:exiv]

   The CENTRE of a category C is the collection of natural transformations
   from the identity functor to itself,

       Z(C)  :=  End(Id[C])  =  (Id[C] ⟹ Id[C]),

   under vertical composition.  Mac Lane's Exercise 8 and Riehl's Exercise
   1.7.iv ask for the same thing: show that these form a COMMUTATIVE monoid.
   Mac Lane sets it in the same exercise list as the Eckmann–Hilton argument
   (§II.5 Exercise 5, proved in this tree as Theory/EckmannHilton.v), and
   this file is that exercise, together with the packaging that explains why
   the two sit in the same list.

   The commutativity is a one-line consequence of naturality, and the line
   is worth writing out because it is easy to mistake for something deeper.
   Let α, β : Id ⟹ Id and fix an object x.  The component `β x` is itself a
   morphism `x ~> x`, so it is a legal argument for α's naturality square,
   and that square reads

       fmap[Id] (β x) ∘ α x  ≈  α x ∘ fmap[Id] (β x).

   Since `fmap[Id]` is the identity on morphisms — definitionally so in this
   library, `Id`'s field being `fun _ _ f => f` (Theory/Functor.v) — the
   square IS

       β x ∘ α x  ≈  α x ∘ β x,

   which is commutativity at x.  No unit is needed, no padding, no
   interchange law: the naturality of one centre element AT the component of
   another is already the statement.  That is [centre_commutes_at] below,
   and [centre_commutative] is its componentwise packaging in the hom-setoid
   of `[C, C]`.

   Note what the argument does NOT need.  It never uses β's naturality, only
   α's; it never uses `fmap_comp` or `fmap_id`; and it holds in every
   category whatsoever, with no completeness, size, or local smallness
   hypothesis.  The centre is therefore always defined and always
   commutative, though it may well be trivial ([centre_Sets_trivial] below
   shows that it is trivial for `Sets`).

--------
nLab:      https://ncatlab.org/nlab/show/center+of+a+category
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument

   范畴的中心 (center) 收集与一切态射交换的自同态（或相关的自然变换数据）。本文件在
   setoid 设定下给出中心对象/幺半群结构，并与 Eckmann–Hilton 论证的零元阴影相联系
   （见 Theory/EckmannHilton.v）。文内其它长注释后续可续译。
*)

(*
Why this is the arity-zero shadow of Eckmann–Hilton

   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/center+of+a+category
   Paper: Eckmann, Hilton, “Group-like structures in general categories I”,
          Mathematische Annalen 145, 1962

   Read one level up.  A category C is a one-object bicategory's worth of
   structure sitting inside Cat: `[C, C]` is a hom-category of Cat, its
   objects (functors) are 1-cells and its morphisms (natural
   transformations) are 2-cells, and Id[C] is the identity 1-cell.  The
   2-cells on an identity 1-cell are exactly the position at which the
   Eckmann–Hilton collapse bites: vertical and horizontal composition
   normally have DIFFERENT units — Theory/TwoCategory.v makes
   that point explicitly, and it is why a 2-category does not degenerate —
   but on an identity 1-cell the two units coincide, the argument applies,
   and the monoid of such 2-cells is forced to be commutative.

   In this tree the collapse was already visible concretely before it was
   stated in general.  Instance/Cat/TwoCategory.v's [NatBase_centre]
   exhibits the 2-cells on the identity functor of the delooping
   of (ℕ, +): every natural number gives one, and their vertical and
   horizontal composites both compute to addition BY [eq_refl]
   ([NatBase_centre_vcomp], [NatBase_centre_hcomp]).  That file's comment
   names the present exercise as what it is illustrating.  This file
   supplies the general theorem those examples instantiate.

   The same one-object reading is what makes the centre a monoid in the
   sense the library already has: Construction/Deloop.v's [hom_monoid C a]
   turns the endomorphism hom-setoid of any object of any category into a
   [MonObject], every monoid law being a category law by projection.  Taking
   C := `[C, C]` and a := Id[C] gives the centre with no new proof
   obligations at all — [centre_monoid] below is literally that application,
   and the three data fields of the resulting monoid (carrier, unit,
   operation) are the transformation setoid, [nat_id] and [nat_compose],
   each recorded by [eq_refl].  What this file must supply on its own is the
   one thing [hom_monoid] cannot know: commutativity.

   HONESTY ABOUT THE EH ROUTE.  The exercise's traditional packaging
   presents the centre as an Eckmann–Hilton situation and reads
   commutativity off the general argument.  That packaging is delivered
   below ([centre_commutative_EH]), and it is a genuine invocation of
   Theory/EckmannHilton.v's [eh_comm] with all seven hypotheses discharged.
   It is NOT, however, an independent derivation of commutativity, and this
   file says so in two machine-checked ways rather than in prose:

   (1) The second operation is not an independent operation.  At the
       identity functor the Godement (horizontal) composite has the SAME
       components as the vertical one — [centre_hcompose_is_vcomp] records
       `transform[nat_hcompose α β] x = transform[nat_compose α β] x` by
       [eq_refl], and both whiskerings against Id are the identity on
       components ([centre_whisker_left], [centre_whisker_right]).  So the
       “two operations” the argument wants are one operation and that same
       operation with its arguments swapped.

   (2) The interchange hypothesis already contains the conclusion.
       [centre_interchange_forces_commutative] derives commutativity from
       interchange by instantiating two of its four arguments at the unit
       and cancelling with the unit laws — no padding argument, no
       [eh_units] step, no appeal to Theory/EckmannHilton.v at all.  So no
       proof of interchange for these operations can be weaker than
       commutativity, and indeed [centre_interchange]'s proof below consumes
       [centre_commutes_at] literally.

   The EH route is therefore a CONSISTENCY EXHIBIT: it shows that the centre
   genuinely is an Eckmann–Hilton situation and that the abstract engine
   applies to it, which is the mathematical content of putting the two
   exercises next to each other.  It is not a second, independent proof.
   Theory/EckmannHilton.v's own header anticipates exactly this (“there they
   genuinely share a unit, which is precisely the special position that
   makes the collapse bite”); this file is that engine's third consumer,
   after Structure/Semiadditive.v (which uses [eh_ops], [eh_comm] and
   [eh_assoc] for its two convolutions) and Instance/Top/LoopSpace.v (which
   uses the packaged [eckmann_hilton]).  Instance/Cat/TwoCategory.v does NOT
   import it: its [NatBase_centre] examples exhibit the collapse by
   computation rather than by invoking the theorem.

--------
为什么这是 Eckmann-Hilton 的零元影子

nLab：https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 nLab：https://ncatlab.org/nlab/show/center+of+a+category
 论文：Eckmann, Hilton，“一般范畴 I 中的类群结构”，
 数学年鉴 145, 1962

读上一级。 范畴 C 是单对象双范畴的价值
 Cat 内部的结构：`XPROTECT0X` 是 Cat 的 hom 范畴，其
 对象（函子）是 1-cell 及其态射（自然
 转换）是 2 细胞，Id[C] 是恒等 1 细胞。 的
 同一 1 单元上的 2 单元恰好是
 Eckmann-Hilton 塌陷咬合：垂直和水平组合
 通常有不同的单位 - Theory/TwoCategory.v 使得
 明确地指出了这一点，这就是为什么 2 范畴不会退化——
 但在恒等 1 细胞上，两个单位重合，该论证适用，
 并且这样的 2-cell 的幺半群被迫是可交换的。

在这棵树上，倒塌之前就已经明显可见
 一般来说。 Instance/Cat/TwoCategory.v 的 [NatBase_centre]
 显示去循环的恒等函子上的 2 个单元
 (ℕ, +)：每个自然数都给出一，并且它们的垂直和
 水平复合材料均通过 [eq_refl] 计算加法
 （[NatBase_centre_vcomp]、[NatBase_centre_hcomp]）。 该文件的评论
 将当前的练习命名为其所说明的内容。 这个文件
 提供了这些例子所实例化的一般定理。

相同的单对象读取使得中心成为幺半群
 感觉库已经有了：Construction/Deloop.v's [hom_monoid C a]
 将任何范畴的任何对象的自同态 hom-setoid 变成
 [MonObject]，每个幺半群法则都是投影的范畴法则。 服用
 C := `XPROTECT8X` 和 a := Id[C] 给了中心没有新的证据
 完全没有义务 — 下面的 [centre_monoid] 实际上就是该应用程序，
 以及生成的幺半群的三个数据字段（载体、单位、
 操作）是变换 setoid、[nat_id] 和 [nat_compose]，
 每个都由 [eq_refl] 记录。 该文件必须单独提供的是
 [hom_monoid] 无法知道一件事：交换性。

关于 EH 路线的诚实。 演习的传统包装
 将中心呈现为 Eckmann-Hilton 情况并读取
 脱离一般论证的交换律。 该包装已交付
 下面（[centre_commutative_EH]），它是一个真正的调用
 Theory/EckmannHilton.v 的 [eh_comm] 已排除所有七个假设。 
然而，它不是交换性的独立推导，并且这
 文件以两种机器检查的方式而不是散文方式表达了这一点：

(1)第二次操作不是独立操作。 在
 恒等函子 Godement（水平）复合体具有相同的
 组件作为垂直组件 — [centre_hcompose_is_vcomp] 记录
 `transformXPROTECT18X x = transformXPROTECT19X x` 通过
 [eq_refl]，并且两个针对 Id 的胡须都是上面的恒等
 组件（[centre_whisker_left]、[centre_whisker_right]）。 所以
 论证想要的“两个操作”是一个操作并且是相同的
 其参数交换的操作。

(2) 互换假设已经包含了结论。 
[centre_interchange_forces_commutative] 的交换律来自
 通过在单元中实例化其四个参数中的两个来进行交换
 并用单位定律取消——没有填充参数，没有
 [eh_units] 步骤，对 Theory/EckmannHilton.v 根本没有吸引力。 所以不
 这些操作的交换证明可能弱于
 交换性，实际上 [centre_interchange] 的下面的证明消耗了
 [centre_commutes_at] 字面上的意思。

因此，EH 路线是一个一致性展示：它表明中心
 确实是 Eckmann-Hilton 情况，并且抽象引擎
 适用于它，这就是将两者放在一起的数学内容
 彼此相邻的练习。 这不是第二个独立的证据。 
Theory/EckmannHilton.v 自己的标题正是预见到了这一点（“他们在那里
 真正共享一个单位，这正是其特殊地位
 使塌陷咬住”）； 该文件是该引擎的第三个消费者，
 在 Structure/Semiadditive.v 之后（使用 [eh_ops]、[eh_comm] 和
 [eh_assoc] 的两个卷积）和 Instance/Top/LoopSpace.v（其中
 使用封装的 [eckmann_hilton]）。 Instance/Cat/TwoCategory.v 不
 导入它：其 [NatBase_centre] 示例显示崩溃
 计算而不是调用定理。
*)

(*
THREE DIFFERENT THINGS ARE CALLED A CENTRE.  All three are in this tree,
   and they are of three different KINDS.  Naming them together once is
   cheaper than disambiguating them repeatedly downstream.

   - THIS centre: the natural endotransformations of the identity functor,
     `Id[C] ⟹ Id[C]`, under vertical composition.  A commutative MONOID.
     Defined for an arbitrary category, no extra structure required.
     Mac Lane §II.5 Exercise 8; Riehl Exercise 1.7.iv.

   - The PREMONOIDAL centre: the central MORPHISMS of a binoidal category —
     those whose two whiskerings commute with everything — assembled into a
     wide subcategory.  A CATEGORY, namely `Centre C` of
     Structure/Binoidal/Central.v (built from [CentralSub]), given
     a monoidal structure in Structure/Premonoidal/Centre.v.  Requires a
     binoidal/premonoidal ambient structure.

   - The DRINFELD (monoidal) centre: objects of a monoidal category equipped
     with a half-braiding, with intertwiners as morphisms.  A BRAIDED
     MONOIDAL CATEGORY, `Drinfeld` of Structure/Monoidal/Drinfeld.v,
     with [Drinfeld_Braided] and the forgetful [Drinfeld_Forget].  Requires
     a monoidal ambient structure.

   The bare name [Centre] is DELIBERATELY NOT taken here: it already belongs
   to Structure/Binoidal/Central.v, and a second [Centre] in Theory/ would
   make any file importing both ambiguous.  The names below are all
   lower-case and prefixed ([centre_setoid], [centre_monoid],
   [centre_commutative]).

   REMARKS ON CONCRETE CENTRES, not computed here.  For `Sets` the centre is
   trivial, and that IS proved below ([centre_Sets_trivial]) — the argument
   is the standard one, probe naturality with the map out of a singleton
   that picks a point.  For Grp and Ab the answer is more interesting, and
   it is NOT computed in this tree.  The expected answer for FINITELY
   GENERATED abelian groups is the multiplicative monoid (ℤ, ·), each
   integer n acting on every group by the n-fold sum — a family that is
   natural because every homomorphism preserves sums — via the route of
   Riehl's Proposition 1.4.6, per the issue catalog; pinning it down
   (rather than merely exhibiting the family) needs machinery this tree
   does not have.
   These two sentences are a REMARK, not a claim about anything proved here,
   and nothing below depends on them.

--------
三个不同的东西被称为一个中心。 三个人都在这棵树上，
 它们分为三种不同的类型。 将它们一起命名一次就是
 比在下游反复消除歧义便宜。

- 这个中心：恒等函子的自然内变换，
 `IdXPROTECT0X ⟹ IdXPROTECT1X`，垂直构图。 可交换 MONOID。 
为任意范畴定义，不需要额外的结构。 
Mac Lane §II.5 练习 8； 里尔练习 1.7.iv。

- PREMONOIDAL 中心：双曲面范畴的中心形态 —
 那些两根胡须与一切事物通勤的人——组装成一个
 广泛的子范畴。 A CATEGORY，即 `Centre C`
 Structure/Binoidal/Central.v（由 [CentralSub] 构建），给定
 Structure/Premonoidal/Centre.v 中的幺半群结构。 需要一个
 双态/前矩态环境结构。

- DRINFELD（单曲面）中心：配备单曲面范畴的物体
 具有半编织，具有作为态射的交织子。 编织
 MONOIDAL 范畴，Structure/Monoidal/Drinfeld.v 的 `Drinfeld`，
 与 [Drinfeld_Braided] 和健忘的 [Drinfeld_Forget]。 需要
 幺半群环境结构。

[Centre] 的裸名故意不在这里使用：它已经属于
 Structure/Binoidal/Central.v，理论/中的第二个 [Centre] 将
 使任何导入的文件都变得不明确。 下面的名字都是
 小写并带有前缀（[centre_setoid]、[centre_monoid]、
 [centre_commutative]）。

关于混凝土中心的备注，此处不计算。 对于 `Sets`，中心是
 微不足道，并且在下面证明了（[centre_Sets_trivial]） - 论点
 是标准的，用单例的地图探索自然性
 选取一个点。 对于 Grp 和 Ab 来说，答案更有趣，并且
 它不在这棵树中计算。 FINITELY 的预期答案
 生成的阿贝尔群是乘法幺半群 (ℤ, ·)，每个
 整数 n 通过 n 重和作用于每个组 — 一个族
 很自然，因为每个同态都保留和 - 通过
 Riehl 的命题 1.4.6，根据发行目录； 固定它
 （而不仅仅是展示家庭）这棵树需要机械
 没有。 
这两句话是一个备注，而不是对这里证明的任何事情的断言，
 下面的一切都不依赖于它们。
*)

(** ** The centre as a setoid and as a monoid / ** 中心作为集合等价类和作为幺半群 *)

Section Centre.

Context {C : Category}.

(*
The carrier: the hom-setoid of the functor category `[C, C]` at the
   identity functor.  This is the categorical home of the centre — the
   objects of `[C, C]` are functors and its morphisms are natural
   transformations (Instance/Fun.v), so `Id[C] ~{[C, C]}~> Id[C]` is
   `Id[C] ⟹ Id[C]` and the setoid is [Transform_Setoid], comparing two
   transformations componentwise.

--------
载体：函子范畴 `XPROTECT0X` 的 hom-setoid
 恒等函子。 这是该中心的绝对所在地——
 `XPROTECT1X` 的对象是函子，其态射是自然的
 转换（Instance/Fun.v），所以 `IdXPROTECT2X ~{XPROTECT3X}~> IdXPROTECT4X` 是
 `IdXPROTECT5X ⟹ IdXPROTECT6X` 和 setoid 是 [Transform_Setoid]，比较两者
 按组件进行变换。
*)
Definition centre_setoid : SetoidObject := {|
  carrier   := @hom ([C, C]) Id[C] Id[C];
  is_setoid := @homset ([C, C]) Id[C] Id[C]
|}.

(*
The monoid structure needs no proof: it is Construction/Deloop.v's
   endomorphism monoid of the object Id[C] of the category `[C, C]`.  The
   associativity and unit laws are taken by PROJECTION from `[C, C]`'s own
   [comp_assoc], [id_left] and [id_right] — the fields Instance/Fun.v's
   [Fun] discharges — and not from that file's standalone restatements
   [nat_comp_assoc], [nat_id_left], [nat_id_right], which are separate
   corollaries.  (The last two are used below, for the EH route's unit
   hypotheses, where they are what is wanted; [nat_comp_assoc] is not
   consumed in this file.)

--------
幺半群结构不需要证明：它是 Construction/Deloop.v 的
 范畴 `XPROTECT1X` 的对象 Id[C] 的自同态幺半群。 的
 结合律和单位定律是通过 `XPROTECT2X` 自己的投影获得的
 [comp_assoc]、[id_left] 和 [id_right] — Instance/Fun.v 的字段
 [Fun] 释放——而不是从该文件的独立重述中释放
 [nat_comp_assoc]、[nat_id_left]、[nat_id_right]，它们是独立的
 推论。 （下面使用最后两个，用于 EH 路线的单位
 假设，它们是我们想要的； [nat_comp_assoc] 不是
 在此文件中消耗。）
*)
Definition centre_monoid : MonObject := hom_monoid ([C, C]) Id[C].

(*
The three data fields, definitionally.  [Set Primitive Projections] gives
   record eta, so the carrier equation is an equation of records.

--------
从定义上来说，这三个数据字段。[Set Primitive Projections] 提供记录 eta，因此载体方程是记录的方程。
*)

Example centre_monoid_setoid : mon_setoid centre_monoid = centre_setoid
  := eq_refl.

Example centre_monoid_carrier :
  carrier centre_monoid = (Id[C] ⟹ Id[C]) := eq_refl.

Example centre_monoid_unit :
  @mon_unit centre_monoid = @nat_id C C Id[C] := eq_refl.

Example centre_monoid_op :
  @mon_op centre_monoid = @nat_compose C C Id[C] Id[C] Id[C] := eq_refl.

(** ** Commutativity, directly from naturality / ** 交换律，直接来源于自然性 *)

(*
The whole content of the exercise, at a single object.  Read α's
   naturality square at the morphism `transform[β] x : x ~> x`; because
   `fmap[Id]` is definitionally the identity on morphisms, the square is
   already the commutation.  Only α's naturality is used.

--------
练习的全部内容针对单个对象。 读取 α
 态射 `transformXPROTECT0X x : x ~> x` 处的自然性平方； 因为
 `fmapXPROTECT1X` 定义上是态射的恒等式，平方为
 已经换刑了。 仅使用α的自然性。
*)
Lemma centre_commutes_at (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[α] x ∘ transform[β] x ≈ transform[β] x ∘ transform[α] x.
Proof.
  symmetry.
  exact (naturality[α] x x (transform[β] x)).
Qed.

(*
The centre is a COMMUTATIVE monoid: vertical composition of natural
   endotransformations of the identity functor is commutative.  This is the
   pinned constant of Mac Lane §II.5 Exercise 8 / Riehl Exercise 1.7.iv.

--------
这个中心是一个交换幺半群：恒等函子自然的内变换的垂直复合是交换的。这是 Mac Lane §II.5 习题 8 / Riehl 习题 1.7.iv 的固定常数。
*)
Theorem centre_commutative (α β : Id[C] ⟹ Id[C]) :
  nat_compose α β ≈[Fun] nat_compose β α.
Proof.
  intro x.
  exact (centre_commutes_at α β x).
Qed.

(*
The same statement read through the monoid packaging, so that a consumer
   holding [centre_monoid] can quote commutativity in the monoid's own
   vocabulary.

--------
同样的语句通过幺半群包装进行读取，以便持有 [centre_monoid] 的消费者可以用幺半群自身的词汇来引用交换律。
*)
Corollary centre_monoid_commutative (α β : carrier centre_monoid) :
  mon_op α β ≈ mon_op β α.
Proof. exact (centre_commutative α β). Qed.

End Centre.

(** ** The Eckmann–Hilton packaging / ** 埃克曼–希尔顿打包 *)

(*
The traditional route: exhibit two unital operations that interchange and
   invoke Theory/EckmannHilton.v.  Everything in this section is honest
   about being a consistency exhibit rather than an independent derivation;
   see the header, and see [centre_interchange_forces_commutative] at the
   end of the section for the machine-checked form of that claim.

--------
传统方法：展示两个可以互换的一元运算，并调用 Theory/EckmannHilton.v。本节中的所有内容都诚实地表明它是一个一致性展示，而不是独立推导；请参见标题，并参见本节末尾的 [centre_interchange_forces_commutative] 以获取该声明的机器检查形式。
*)

Section CentreEH.

Context {C : Category}.

(*
The first operation is vertical composition.  The second is the SAME
   composition with its arguments swapped — which, by
   [centre_vcomp_op_is_hcompose] below, is exactly the Godement horizontal
   composite in the other order, the two agreeing on components at the
   identity functor.

--------
第一个操作是垂直组合。第二个操作是相同的组合，但交换了其参数——根据下面的 [centre_vcomp_op_is_hcompose]，这正是 Godement 水平组合的另一种顺序，两者在恒等函子上的分量是一致的。
*)

Definition centre_vcomp (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose α β.

Definition centre_vcomp_op (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose β α.

(*
Components, definitionally: `f` composes in the given order, `g` in the
   opposite one.

--------
组件，从定义上来说：`f` 按给定顺序组合，`g` 按相反顺序组合。
*)

Example centre_vcomp_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp α β] x = transform[α] x ∘ transform[β] x := eq_refl.

Example centre_vcomp_op_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[β] x ∘ transform[α] x
  := eq_refl.

(** *** The second operation IS the horizontal composite, componentwise / *** 第二个操作是水平复合，按分量进行 *)

(*
[nat_hcompose ε η : J ◯ F ⟹ K ◯ G] lands at `Id ◯ Id`, not at `Id`, so
   the two transformations do not have the same TYPE and no equation between
   them can be written without a transport.  Componentwise they need none:
   `(Id ◯ Id) x` reduces to `x`, so both components inhabit `x ~> x` and the
   identification is [eq_refl].  This is stated componentwise deliberately;
   no isomorphism [nat_ρ]/[nat_λ] is inserted and none is claimed.

--------
[nat_hcompose ε η : J ◯ F ⟹ K ◯ G] 落在 `Id ◯ Id`，而不是 `Id`，因此这两个变换没有相同的类型，且在不经过传输的情况下无法在它们之间写出方程。按分量来说，它们不需要：`(Id ◯ Id) x` 化简为 `x`，因此两个分量都属于 `x ~> x`，且该识别是 [eq_refl]。这是有意按分量说明的；没有插入 [nat_ρ]/[nat_λ] 的同构，也没有声称存在同构。
*)

Example centre_hcompose_is_vcomp (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[nat_hcompose α β] x = transform[nat_compose α β] x := eq_refl.

Example centre_vcomp_op_is_hcompose (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[nat_hcompose β α] x := eq_refl.

(*
Both whiskerings against the identity functor are the identity on
   components, which is the other half of the same observation.

--------
对恒等函子进行的两个搅拌在分量上都是恒等的，这是同一观察的另一半。
*)

Example centre_whisker_left (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[Id[C] ⊳ α] x = transform[α] x := eq_refl.

Example centre_whisker_right (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[α ⊲ Id[C]] x = transform[α] x := eq_refl.

(** *** The seven hypotheses of [eh_comm] / *** [eh_comm]的七个假设 *)

(*
Respectfulness: both operations are [nat_compose] up to argument order,
   so both are [nat_compose_respects] (the second with its two arguments
   exchanged).

--------
尊重性：两个操作都是 [nat_compose]，顺序可变，所以两个都是 [nat_compose_respects]（第二个交换了它的两个参数）。
*)

Definition centre_vcomp_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp.
Proof. repeat intro; now apply nat_compose_respects. Qed.

Definition centre_vcomp_op_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp_op.
Proof. repeat intro; now apply nat_compose_respects. Qed.

(*
The four unit laws.  Both operations take [nat_id] as a two-sided unit —
   this is the coincidence of units that makes the Eckmann–Hilton argument
   applicable at all, and here it is not an accident of the construction but
   the fact that both operations ARE vertical composition.  The laws are
   Instance/Fun.v's [nat_id_left] and [nat_id_right], used crosswise for the
   opposite-order operation.

--------
四个单位定律。两种运算都将 [nat_id] 视为双边单位——这是单位的一致性，使得 Eckmann–Hilton 论证能够适用，而在这里，这并不是构造的巧合，而是因为两种运算本身就是垂直组合。定律是在 Instance/Fun.v 中的 [nat_id_left] 和 [nat_id_right]，交叉使用于顺序相反的运算。
*)

Definition centre_vcomp_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp nat_id α ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

Definition centre_vcomp_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp α nat_id ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op nat_id α ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op α nat_id ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

(*
The interchange law, in the orientation Theory/EckmannHilton.v states it:
   `f (g a b) (g c d) ≈ g (f a c) (f b d)`.

   Componentwise the goal is `(b ∘ a) ∘ (d ∘ c) ≈ (b ∘ d) ∘ (a ∘ c)`;
   reassociating both sides to `b ∘ (_ ∘ _) ∘ c` leaves exactly
   `a ∘ d ≈ d ∘ a`, and there is nothing to appeal to for that but the
   naturality square — i.e. [centre_commutes_at], which the proof therefore
   uses LITERALLY.  This is the disclosure the header promises: the
   interchange hypothesis of the EH route is not cheaper than its
   conclusion.

--------
在定向理论/埃克曼-希尔顿 (Eckmann-Hilton.v) 中，交换律是这样说明的：
   `f (g a b) (g c d) ≈ g (f a c) (f b d)`。

从分量的角度看，目标是 `(b ∘ a) ∘ (d ∘ c) ≈ (b ∘ d) ∘ (a ∘ c)`；
将两边重新结合为 `b ∘ (_ ∘ _) ∘ c` 后正好剩下
   `a ∘ d ≈ d ∘ a`，而对此没有其他可依赖的，除了自然性交换方 — 即 [centre_commutes_at]，因此证明中是字面上使用它的。这就是标题所承诺的披露：EH 路径的交换假设并不比其结论更容易。
*)
Lemma centre_interchange (a b c d : Id[C] ⟹ Id[C]) :
  centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
    ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d).
Proof.
  intro x.
  simpl.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity].
  exact (centre_commutes_at a d x).
Qed.

(** *** Commutativity via [eh_comm] / *** 通过 [eh_comm] 的交换性 *)

(*
All seven hypotheses discharged, the abstract argument applied.  The
   conclusion is [centre_commutative] again, reached the long way.

--------
所有七个假设都被驳回，抽象论证已应用。结论再次是 [centre_commutative]，是走了很长的路才得出的。
*)
Theorem centre_commutative_EH (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp β α.
Proof.
  exact (eh_comm centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(*
[eh_ops] — the Eckmann–Hilton conclusion that the two operations
   COINCIDE — degenerates here into commutativity a second time, since the
   second operation is the first with its arguments swapped.  Recording it
   makes the degeneration visible instead of leaving it implicit.

--------
[eh_ops] — 埃克曼–希尔顿结论，即两个运算
重合 — 在这里再次退化为交换律，因为第二个运算是将第一个运算的参数交换后的结果。记录它使这种退化变得可见，而不是保持隐含状态。
*)
Corollary centre_EH_ops (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp_op α β.
Proof.
  exact (eh_ops centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(*
Likewise [eh_units]: the two units coincide.  Here they were literally
   the same transformation to begin with, so the general theorem's first
   conclusion is [reflexivity] at this instance — another measurement of how
   degenerate the EH situation is at the centre.

--------
同样地，[eh_units]：这两个单元重合。这里它们一开始实际上就是相同的变换，所以一般定理的第一个结论在这一实例下是[reflexivity]——这是衡量EH情况在中心退化程度的另一种方式。
*)
Corollary centre_EH_units : (nat_id : Id[C] ⟹ Id[C]) ≈[Fun] nat_id.
Proof.
  exact (eh_units centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange).
Qed.

(** *** Why the EH route cannot be independent / *** 为什么 EH 路径不能独立 *)

(*
The claim, machine-checked.  Take the interchange law as a HYPOTHESIS —
   not the proved [centre_interchange], but any statement of that shape —
   and instantiate its second and third arguments at [nat_id].  The unit
   laws then collapse it directly to commutativity, with no padding
   argument, no [eh_units] step, and no appeal to Theory/EckmannHilton.v.
   So interchange for these two operations is not a weaker input than the
   conclusion it is supposed to produce, and the EH packaging above is a
   consistency exhibit rather than a second proof.

--------
该命题，经机器检验。将交换律作为一个假设——不是已证明的 [centre_interchange]，而是任何此类形式的陈述——并将其第二和第三个参数实例化为 [nat_id]。然后，单元律直接将其折叠为交换律，无需填充参数，无需 [eh_units] 步骤，也无需引用 Theory/EckmannHilton.v。因此，对于这两种运算的交换律并不比它所要生成的结论弱，上述 EH 封装是一个一致性示例，而不是第二个证明。
*)
Theorem centre_interchange_forces_commutative
  (inter : ∀ a b c d : Id[C] ⟹ Id[C],
      centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
        ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d))
  (α δ : Id[C] ⟹ Id[C]) :
  centre_vcomp α δ ≈[Fun] centre_vcomp δ α.
Proof.
  (*
Instantiate at (α, 1, 1, δ), writing 1 for [nat_id]:

       f (g α 1) (g 1 δ)  ≈  g (f α 1) (f 1 δ).

     Componentwise that is `(1 ∘ α x) ∘ (δ x ∘ 1) ≈ (1 ∘ δ x) ∘ (α x ∘ 1)`,
     and cancelling the four units leaves `α x ∘ δ x ≈ δ x ∘ α x`, which is
     the goal.  Only [id_left] and [id_right] are spent.

--------
在 (α, 1, 1, δ) 处实例化，为 [nat_id] 写入 1：

       f (g α 1) (g 1 δ)  ≈  g (f α 1) (f 1 δ)。

按分量表示为 `(1 ∘ α x) ∘ (δ x ∘ 1) ≈ (1 ∘ δ x) ∘ (α x ∘ 1)`，
取消四个单位后得到 `α x ∘ δ x ≈ δ x ∘ α x`，这就是目标。只有 [id_left] 和 [id_right] 被使用。
*)
  specialize (inter α nat_id nat_id δ).
  intro x.
  specialize (inter x).
  simpl in *.
  rewrite !id_left, !id_right in inter.
  exact inter.
Qed.

End CentreEH.

(** ** The centre of Sets is trivial / ** 集合的中心是平凡的 *)

(*
Mac Lane asks for the centre of Set.  The probe is the standard one: a
   point of a setoid X is the same thing as a morphism into X from the
   singleton, and naturality of α at that morphism pins α's component at X
   to the identity.

   Concretely, for `x : carrier X` let `pick x : 1 ~> X` be the constant map.
   Naturality of α at `pick x`, evaluated at the sole element `ttt`, reads

       pick x (α_1 ttt)  ≈  α_X (pick x ttt),

   whose left side is `x` (the map is constant) and whose right side is
   `α_X x`.  Note that the value of `α` at the singleton is never inspected:
   it is absorbed by the constancy of the probe, which is why the argument
   needs no decidability, no choice, and no extensionality.

--------
Mac Lane 询问 Set 的中心。探针是标准的：集合等价类 X 的一个点与从单元素集合到 X 的态射是同一件事，而 α 在该态射处的自然性将 α 在 X 处的分量固定为恒等映射。

具体来说，对于 `x : carrier X`，让 `pick x : 1 ~> X` 为常值映射。α 在 `pick x` 处的自然性，在唯一元素 `ttt` 上求值，表示为

    pick x (α_1 ttt)  ≈  α_X (pick x ttt),

其左边是 `x`（映射是常值的），右边是 `α_X x`。注意 `α` 在单元素集合上的值从不被检查：它被探针的常值性吸收，这也是为什么该论证不需要可判定性、不需要选择，也不需要外延性。
*)

(*
The singleton setoid used as the probe's domain is the carrier of
   [Sets_Terminal] (Instance/Sets.v), [poly_unit] under `=`.

   UNIVERSE ANNOTATION, and why it is not decoration.  `Sets@{o so}` has
   carriers at `o` and objects at `so` (Instance/Sets.v).  Written
   without the annotations below, universe minimization instantiates the
   probe's carrier as `poly_unit@{Set}` and, through the object type, pins
   `o := Set` — so the theorems would speak only of setoids whose carriers
   live in `Set`.  Naming `o` and `so` and writing `poly_unit@{o}` keeps
   both free, and the statements then apply to `Sets` at every level.

--------
用于探针域的单例集合等价关系是 [Sets_Terminal]（Instance/Sets.v）下 [poly_unit] 的载体，属于 `=`。

UNIVERSE 注解，以及为什么它不是装饰。`Sets@{o so}` 在 `o` 具有载体，在 `so`（Instance/Sets.v）具有对象。如果没有下面的注解，宇宙最小化会将探针的载体实例化为 `poly_unit@{Set}`，并通过对象类型固定 `o := Set`——因此定理只会讨论载体处于 `Set` 的集合等价关系。命名 `o` 和 `so` 并写作 `poly_unit@{o}` 可以保持两者自由，然后这些陈述适用于每个层级的 `Sets`。
*)
Program Definition centre_Sets_point@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) :
  ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) ~{Sets@{o so}}~> X := {|
  morphism := fun _ => x
|}.

(*
The probe's underlying function is given literally, so it computes; the
   [Program] wrapper touches only the respectfulness certificate.  Recorded
   because [centre_Sets_trivial] below relies on the reduction.

--------
探针的基本功能是字面上给出的，因此它会进行计算；[Program] 包装器只涉及尊重证书。记录下来，因为下面的 [centre_Sets_trivial] 依赖于该简化。
*)
Example centre_Sets_point_computes@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) (u : poly_unit@{o}) : centre_Sets_point x u = x := eq_refl.

(*
Pointwise form: every centre element of `Sets` acts as the identity on
   every point of every setoid.

--------
逐点形式：`Sets` 的每个中心元素在每个集合的每个点上都表现为恒等元。
*)
Theorem centre_Sets_trivial@{o so} (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}])
  (X : obj[Sets@{o so}]) (x : carrier X) : transform[α] X x ≈ x.
Proof.
  symmetry.
  exact (naturality[α] ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) X
           (centre_Sets_point x) ttt).
Qed.

(*
Packaged form: every centre element of `Sets` IS the identity
   transformation, in the hom-setoid of `[Sets, Sets]`.

--------
封装形式：`Sets`的每个中心元素都是恒等
 转化，在 `XPROTECT0X` 的 hom-setoid 中。
*)
Corollary centre_Sets_trivial_nat@{o so}
  (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Sets_trivial.
Qed.

(* Hence the centre of `Sets` is a singleton: it is the trivial monoid. / 因此，`Sets` 的中心是单元素的：它是平凡幺半群。 *)
Corollary centre_Sets_subsingleton@{o so}
  (α β : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] β.
Proof.
  transitivity (@nat_id Sets@{o so} Sets@{o so} Id[Sets@{o so}]).
  - apply centre_Sets_trivial_nat.
  - symmetry; apply centre_Sets_trivial_nat.
Qed.

(** ** The centre of Coq is trivial / ** Coq 的中心是平凡的 *)

(*
The same probe over Instance/Coq.v, where the hom-setoid is pointwise
   Leibniz equality (Instance/Coq.v), so the conclusion is an equation
   rather than an `≈`.  It costs nothing beyond changing the probe's
   codomain, and it is included because it is the reading a programmer
   expects: a polymorphic function `forall a, a -> a` is the identity.

--------
在 Instance/Coq.v 上使用相同的探针，其中同态集合是点对点的 Leibniz 相等（Instance/Coq.v），因此结论是一个方程而不是 `≈`。这除了改变探针的上域之外没有任何成本，它被包括在内是因为这是程序员所期望的阅读方式：一个多态函数 `forall a, a -> a` 是恒等函数。
*)

Theorem centre_Coq_trivial (α : Id[Coq] ⟹ Id[Coq])
  (X : obj[Coq]) (x : X) : transform[α] X x = x.
Proof.
  symmetry.
  exact (naturality[α] poly_unit X (fun _ => x) ttt).
Qed.

Corollary centre_Coq_trivial_nat (α : Id[Coq] ⟹ Id[Coq]) :
  α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Coq_trivial.
Qed.
