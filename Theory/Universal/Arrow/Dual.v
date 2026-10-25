Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Adjunction.Opposite.

Generalizable All Variables.

(*
NOTATION GUARD.  Three scopes declare the token `_ ^op` at the same level:
   category_scope (Construction/Opposite.v, [Opposite]), functor_scope
   (Functor/Opposite.v, [Opposite_Functor]) and adjunction_scope
   (Adjunction/Opposite.v, [Opposite_Adjunction]).  The last two files each
   [Open] their own scope as a side effect of being imported, so by the end of
   the [Require] block above the winning interpretation of `X^op` is the
   ADJUNCTION one.

   BE PRECISE ABOUT WHICH HALF OF THIS IS FORCED -- an earlier revision of
   this block was not, and claimed the [Open Scope] below is required.  It is
   NOT, in this file: [Bind Scope category_scope with Category]
   (Theory/Category.v) rescues every occurrence of `C^op` here, all of which
   sit in argument or ascription positions, and deleting the [Open Scope] line
   leaves the file compiling clean (measured).  The hazard is real in general
   -- a bare [Definition d := C^op.] after this Require block does fail, with
   `C` reported as expected to have type `?F ⊣ ?U` -- but this file contains
   no such occurrence.  So the [Open Scope] is DEFENSIVE, kept because it is
   cheap, exported, and useful to downstream importers who may write the bare
   form.

   What IS forced is the other half: `F^op` is rejected under either scope
   order ([Fail Definition fop := F^op.] succeeds with the guard in place), so
   every opposite FUNCTOR below is written [Opposite_Functor F] by name.  (The
   same family of hazard is recorded for Instance/Rng/Mod.v.)

--------
符号保护。三个作用域在同一级别声明了令牌 `_ ^op`：category_scope（Construction/Opposite.v，[Opposite]）、functor_scope（Functor/Opposite.v，[Opposite_Functor]）和 adjunction_scope（Adjunction/Opposite.v，[Opposite_Adjunction]）。最后两个文件在被导入时各自产生了 [Open] 的作用域，因此在上述 [Require] 块结束时，`X^op` 的最终解释是 ADJUNCTION 的那个。

准确说明哪一半是强制性的——这个代码块的早期版本并不是强制的，并且声称下面的 [Open Scope] 是必需的。它在这个文件中并不是必需的：[Bind Scope category_scope with Category] (Theory/Category.v) 拯救了这里每一个 `C^op` 的出现，这些都位于参数或类型指定位置，删除 [Open Scope] 这一行后文件仍能干净编译（经测量）。这种风险在一般情况下确实存在——在这个 Require 块之后单独使用 [Definition d := C^op.] 会出错，并且 `C` 会如期报告类型为 `?F ⊣ ?U`——但这个文件中没有这种情况。因此 [Open Scope] 是防御性的，保留它是因为它成本低、已导出，并且对下游导入者可能使用的裸形式有用。

被强制的是另一半：`F^op` 在任一作用域顺序下都会被拒绝（[Fail Definition fop := F^op.] 在防护存在时成功），因此下面每个相反的 FUNCTOR 都以 [Opposite_Functor F] 命名。（同一类风险在 Instance/Rng/Mod.v 中也有记录。）
*)
Open Scope category_scope.

(** * Couniversal arrows / * 宇宙箭头 *)

(*
nLab: https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   A couniversal arrow from a functor F : D ⟶ C to an object c : C -- Mac
   Lane's "universal arrow from F to c" (CWM 2nd ed., §III.1, p. 58) -- is a
   pair (a, ε) consisting of an object a : D and a morphism ε : F a ~> c, such
   that for every object d : D and every morphism h : F d ~> c there exists a
   unique g : d ~> a satisfying h ≈ ε ∘ fmap[F] g.  Equivalently, (a, ε) is a
   TERMINAL object of the comma category F ↓ =(c).

   That last sentence is not new here: it is the one Theory/Universal/Arrow.v
   already writes down in its own header -- "The dual notion, a universal
   arrow from F to c, is a terminal object of F ↓ =(c)" -- as a remark, with
   nothing in the tree carrying it.  This file carries it.

   Where a universal arrow is the pointwise form of a LEFT adjoint, with the
   arrows serving as the components of the unit, a couniversal arrow is the
   pointwise form of a RIGHT adjoint, with the arrows serving as the
   components of the counit.  That is the content of
   [RightAdjointFunctorFromCouniversalArrows] and
   [AdjunctionFromCouniversalArrows] below: a couniversal arrow to every
   c : C assembles into a right adjoint of F.

--------
nLab：https://ncatlab.org/nlab/show/universal+morphism
维基百科：https://en.wikipedia.org/wiki/Universal_property

从函子 F : D ⟶ C 到对象 c : C 的一个普遍箭头 —— Mac Lane 的“从 F 到 c 的普遍箭头”（CWM 第二版，§III.1，第58页） —— 是一对 (a, ε)，其中 a : D 为对象，ε : F a ~> c 为态射，并满足对于每一个对象 d : D 和每一个态射 h : F d ~> c，存在唯一的 g : d ~> a 使得 h ≈ ε ∘ fmap[F] g。等价地，(a, ε) 是余逗号范畴 F ↓ =(c) 的终端对象。

最后一句在这里并不新：它正是 Theory/Universal/Arrow.v 已经在自己的头部写下的内容——“对偶概念，从 F 到 c 的通用箭头，是 F ↓ =(c) 的终对象”——作为一个备注，而树中没有任何内容包含它。这个文件包含了它。

当一个通用箭头是左伴随的点态形式时，这些箭头作为单位元的分量；而协通用箭头是右伴随的点态形式，这些箭头作为余单位的分量。这就是下面 [RightAdjointFunctorFromCouniversalArrows] 和 [AdjunctionFromCouniversalArrows] 的内容：对于每一个 c : C 的协通用箭头组装成 F 的右伴随。
*)

(*
Why the dual is cheap here, and what it costs

   nLab:  https://ncatlab.org/nlab/show/opposite+category
   Paper: Mac Lane, "Duality for groups", Bull. Amer. Math. Soc. 56, 1950

   The couniversal notion is introduced as the formal dual and its theory
   left to the duality principle, and this file honours that: the
   definition is an INSTANTIATION of the primal class at the opposite
   categories,

       CouniversalArrow c F := @UniversalArrow (C^op) (D^op) c (F^op),

   after which every result of Theory/Universal/Arrow.v is available by
   instantiation rather than by a second proof.  What the file adds is the
   covariant reading, so that a consumer never types `op`: [coarrow_obj],
   [coarrow] and [ump_couniversal_arrows] are DEFINITIONAL op-reads,
   supplied by [:=] with no tactic at all, because `x ~{C^op}~> y` is
   literally `y ~{C}~> x` (Construction/Opposite.v), the object and
   morphism maps of `F^op` are literally those of `F`
   (Functor/Opposite.v), and composition in `C^op` is composition in `C`
   with its arguments exchanged.  The same device carries
   Comonad/Core.v over [Comonad := @Monad (C^op) (W^op)] and
   Structure/End.v over [Coend F := @End (C^op) (D^op) (F^op)] -- the
   definition lives in End.v, not in Structure/Coend.v, which is the calculus
   built on it.  This file applies the device again, and those two are the
   models it follows.

   The duality is not free everywhere, and the file measures rather than
   assumes.  Two boundaries are recorded.

   FIRST, the terminal-object reading is a THEOREM, not the definition.
   `@Initial (=(c) ↓ F^op)` computed in the opposite categories is NOT
   convertible with `@Terminal (F ↓ =(c))`: [Comma] stores its two
   indices as an ordered pair, so the first has objects over `1 ∏ D^op`
   and the second over `D ∏ 1`, and the product of categories is not
   symmetric on the nose.  [couniversal_arrow_terminal] and
   [couniversal_arrow_of_terminal] therefore convert in both directions
   through the universal mapping property, and Test/ProbeCouniversal.v
   pins the negative side.  This is the same accounting
   Structure/Initial.v makes for [initial_unique], where transporting
   the terminal statement would cost more than the direct argument.

   The bridge's round-trip behaviour is ASYMMETRIC, and both halves are
   recorded here rather than left for a reader to discover.  In one
   direction it is better than the file claims elsewhere: for an
   ARBITRARY [U], both [coarrow_obj] and [coarrow] survive
   [couniversal_arrow_of_terminal (couniversal_arrow_terminal U)] by
   [eq_refl] -- more general than Examples.v's [product_terminal_round],
   which records only the arrow and only at the product.  In the other
   direction it does not reduce at all: [couniversal_arrow_of_terminal]
   destructs its argument, so on a variable [T] the object component of
   [couniversal_arrow_terminal (couniversal_arrow_of_terminal T)] is
   stuck.  Neither statement is packaged as an isomorphism, and the
   "not a bijection" note in the WHAT IS NOT DELIVERED block below is
   about the ENCODING passage, not about this bridge.

   The mismatch is located precisely, and it is NOT the terminal/initial
   axis: [terminal_is_initial_op] below records by [eq_refl] that
   `@Terminal (F ↓ =(c))` IS `@Initial ((F ↓ =(c))^op)`, the house idiom
   costing nothing.  What differs is WHICH comma category, and
   Construction/Comma.v's [Cocomma] -- which the issue proposes as the
   route -- does not close the gap either: [Cocomma F =(c)] is neither
   the comma the op-side [arrow_initial] inhabits nor
   `(F ↓ =(c))^op` on the nose (both measured, both pinned in the probe
   file).  Hence the bridge is built, not asserted.

   SECOND, the adjunction assembles by duality but its counit does not
   REDUCE to the couniversal arrow.  [Opposite_Adjunction]
   (Adjunction/Opposite.v) turns the opposite-side left adjoint into the
   covariant right adjoint with `(C^op)^op = C` and `(F^op)^op = F`
   holding by [reflexivity], so [RightAdjointFunctorFromCouniversalArrows]
   is a `C ⟶ D` on the nose and its object action is [coarrow_obj] by
   [eq_refl] ([right_adjoint_obj]).  The counit, however, arrives as
   `coarrow ∘ fmap[F] id`, so [counit_couniversal] closes only up to `≈`
   -- one [fmap_id] and one [id_right] away from [eq_refl], and the
   residue is in the transpose, not in the [abstract]-opaque obligations
   of [AdjunctionFromUniversalArrows].

   The witnesses live in Theory/Universal/Arrow/Dual/Examples.v, kept
   separate so that consumers of the theory -- Mac Lane §IV.1 Theorem 2
   is the scheduled one -- do not inherit a dependency on
   Structure/Cartesian.v.

--------
为什么这里的双宿便宜，以及它的价格是多少

nLab：https://ncatlab.org/nlab/show/opposite+category
论文：Mac Lane，《群的对偶性》，美国数学学会公报，56卷，1950年

共宇概念被引入作为形式对偶，其理论留给对偶性原理，而这个文件就是对其的致敬：该定义是原始类在对偶范畴上的一个实例化，

CouniversalArrow c F := @UniversalArrow (C^op) (D^op) c (F^op),

之后，Theory/Universal/Arrow.v 的每个结果都可以通过实例化获得，而不是通过第二次证明。该文件添加的是协变读取，因此使用者永远不会键入 `op`：[coarrow_obj]、[coarrow] 和 [ump_couniversal_arrows] 是定义性操作读取，由 [:=] 提供，完全没有策略，因为 `x ~{C^op}~> y` 字面上就是 `y ~{C}~> x`（Construction/Opposite.v），`F^op` 的对象和态射映射字面上就是 `F` 的映射（Functor/Opposite.v），而 `C^op` 中的复合就是 `C` 中复合的参数交换版本。同一设备在 [Comonad := @Monad (C^op) (W^op)] 上携带 Comonad/Core.v，在 [Coend F := @End (C^op) (D^op) (F^op)] 上携带 Structure/End.v —— 定义存在于 End.v 中，而不是 Structure/Coend.v 中，后者是在其基础上构建的演算。这个文件再次应用了该设备，而这两个是它遵循的模型。

二元性并非在任何地方都是自由的，并且文件是测量的，而不是假设的。记录了两个边界。

首先，终端对象的读法是一个定理，而不是定义。在对立范畴中计算的 `@Initial (=(c) ↓ F^op)` 与 `@Terminal (F ↓ =(c))` 不可转换：[Comma] 将其两个指标存储为有序对，所以第一个是在 `1 ∏ D^op` 上的对象，第二个是在 `D ∏ 1` 上的对象，而范畴的积在本质上不是对称的。因此，[couniversal_arrow_terminal] 和 [couniversal_arrow_of_terminal] 通过通用映射性质在两个方向上转换，而 Test/ProbeCouniversal.v 锁定了负面的一侧。这与 Structure/Initial.v 为 [initial_unique] 做的处理相同，其中传递终端语句的代价将高于直接参数。

桥的往返行为是不对称的，这里记录了两个部分，而不是留给读者去发现。在一个方向上，它比文件在其他地方声称的要好：对于任意的 [U]，[coarrow_obj] 和 [coarrow] 都能通过 [eq_refl] 幸存于 [couniversal_arrow_of_terminal (couniversal_arrow_terminal U)] —— 比 Examples.v 的 [product_terminal_round] 更通用，后者只记录箭头并且仅在产品处。在另一个方向上，它根本不会减少：[couniversal_arrow_of_terminal] 会销毁其参数，因此在变量 [T] 上，[couniversal_arrow_terminal (couniversal_arrow_of_terminal T)] 的对象组件被卡住。没有任何陈述被打包为同构，下面的 WHAT IS NOT DELIVERED 块中的“不是双射”注释是关于 ENCODING 段落的，而不是关于这座桥。

不匹配的位置非常准确，并且它不是终端/初始轴：[terminal_is_initial_op] 下面由 [eq_refl] 记录，`@Terminal (F ↓ =(c))` 是 `@Initial ((F ↓ =(c))^op)`，房子习语一文不值。不同的是哪一种逗号范畴，而 Construction/Comma.v 的 [Cocomma] —— 问题提出作为解决途径的那个 —— 也没有弥合这个差距：[Cocomma F =(c)] 既不是操作侧 [arrow_initial] 所处的逗号，也不是 `(F ↓ =(c))^op` 的确切位置（两者都已测量，并固定在探针文件中）。因此，桥梁是建立出来的，而不是被断言的。

第二，该伴随通过对偶组装，但其余单位并不归约到共通箭头。[Opposite_Adjunction]（Adjunction/Opposite.v）将对面左伴随转变为协变右伴随，并且 `(C^op)^op = C` 和 `(F^op)^op = F` 由 [reflexivity] 保持，因此 [RightAdjointFunctorFromCouniversalArrows] 在本质上是 `C ⟶ D`，并且其对象作用由 [eq_refl]（[right_adjoint_obj]）实现 [coarrow_obj]。然而，余单位以 `coarrow ∘ fmapXPROTECT30X id` 形式到达，因此 [counit_couniversal] 只关闭到 `≈`——距离 [eq_refl] 还有一个 [fmap_id] 和一个 [id_right]，而残留在转置中，而不是在 [AdjunctionFromUniversalArrows] 的 [abstract] 不透明义务中。

这些证据存放在 Theory/Universal/Arrow/Dual/Examples.v 中，保持分离，以便理论的使用者——麦克·莱恩 §IV.1 定理 2 是计划中的定理——不会继承对 Structure/Cartesian.v 的依赖。
*)

(*
WHAT IS DELIVERED

   Both encodings, mirroring the primal file field for field:
   [CouniversalArrow], packaging the property with the object projected
   out, and [ACouniversalArrow], with the object a : D a parameter.  For
   each: the covariant accessors, the couniversal mapping property and
   its converse, the full mediator calculus ([cua_med] / [acua_med] with
   commutes / unique / id / comp), the canonical isomorphism of
   couniversal objects, and Awodey's Proposition 1.10 dualized
   ([couniversal_arrow_unique], [acouniversal_arrow_unique]).  Mac Lane's
   terminal-object reading in both directions.  The right adjoint and the
   adjunction, with the counit identified.  And -- an addition rather than
   a mirror, the primal file relating its two encodings nowhere -- the
   passage between the two encodings, both ways, each keeping the arrow
   and the object by [eq_refl].

   WHAT IS NOT DELIVERED

   * NO NOTATION.  The primal `c ⟿ F` is declared INSIDE
     [Section UniversalArrow] and so does not survive its [End]; there is
     no exported spelling to mirror, and inventing one is out of scope.

   * NO CONVERSE.  Mac Lane §IV.1 Theorem 2 -- that the counit of an
     adjunction is a couniversal arrow at every object, the converse of
     [AdjunctionFromCouniversalArrows] -- is deliberately left to the
     issue that owns it (#347), which is why the artifacts here sit at
     this path for it to import.

   * NO REPRESENTABILITY FACE.  Structure/UniversalProperty/Universal/
     Arrow.v identifies an [AUniversalArrow] with a hom-set isomorphism
     via Yoneda ([UniversalArrowIsUniversalProperty]); no dual of that is
     built here, and none is needed by the assembly.

   * THE ENCODING PASSAGE IS NOT A BIJECTION.  Its two round trips are
     recorded on the ARROW and the OBJECT only; nothing is claimed about
     the uniqueness data, and no setoid isomorphism is stated.

--------
交付的内容是什么

两种编码，镜像原始文件的字段对应关系：
   [CouniversalArrow]，将属性与投影出来的对象打包，
   以及 [ACouniversalArrow]，其对象是一个 : D a 参数。 对于每一种：协变访问器、对宇映射性质及其逆、完整的中介计算（[cua_med] / [acua_med] 与交换 / 唯一 / 单位 / 组合）、对宇对象的标准同构，以及 Awodey 命题 1.10 的对偶化（[couniversal_arrow_unique], [acouniversal_arrow_unique]）。 Mac Lane 的终对象阅读在两个方向。 右伴随及其伴随，并识别其余单位。 并且——这是增加而非镜像——原始文件与其两种编码未直接关联——两种编码之间的转换，双向，每种都通过 [eq_refl] 保留箭头和对象。

未交付的内容

* 无符号。原始的 `c ⟿ F` 在 [Section UniversalArrow] 内声明，因此不会在其 [End] 中存活；没有可对应的导出拼写，发明一个超出范围。

* 不逆。Mac Lane §IV.1 定理 2——即一个伴随的余单位在每个对象上都是一个余通用箭头，[AdjunctionFromCouniversalArrows] 的逆命题——有意留待拥有它的问题 (#347) 处理，这也是为什么这里的工件放在此路径以便导入的原因。

* 无法表示的面。Structure/UniversalProperty/Universal/Arrow.v 通过 Yoneda（[UniversalArrowIsUniversalProperty]）识别了一个 [AUniversalArrow] 与一个同态集同构；这里没有构建它的对偶，并且装配也不需要对偶。

* 编码路径不是一一对应的。它的两次往返仅记录在箭头和对象上；关于唯一性数据没有任何声明，也没有说明集合同构。
*)

Section CouniversalArrow.

Context {C : Category}.
Context {D : Category}.

(** ** The comma-packaged encoding / ** 逗号打包编码 *)

(*
A couniversal arrow from F to c.  Definitionally a [UniversalArrow] in the
   opposite categories; every accessor below reads it back covariantly.

--------
从 F 到 c 的一个共通箭头。在对偶范畴中，本质上是一个 [UniversalArrow]；下面的每个访问器都协变地读取它。
*)
Definition CouniversalArrow (c : C) (F : D ⟶ C) : Type :=
  @UniversalArrow (C^op) (D^op) c (Opposite_Functor F).

(*
Mirrors [Existing Class Comonad] in Comonad/Core.v: typeclass resolution
   keys on the head constant of a goal and does not unfold this definition, so
   without the declaration a couniversal arrow in scope would not be found for
   the implicit arguments of the accessors below.  Goals headed by
   [UniversalArrow] are untouched, the two heads being distinct.

--------
在 Comonad/Core.v 中，Mirrors [Existing Class Comonad]：类型类解析依赖于目标的头部常量，并且不会展开此定义，因此如果没有声明，作用域中的共通箭头将无法被找到以用于下面访问器的隐式参数。以 [UniversalArrow] 为头的目标不受影响，这两个头是不同的。
*)
Existing Class CouniversalArrow.

Section Accessors.

Context {c : C}.
Context {F : D ⟶ C}.
Context (U : CouniversalArrow c F).

(*
The couniversal object a : D.  Objects of `D^op` ARE objects of `D`, so
   this is [arrow_obj] with no transport.

--------
余范对象 a : D。 `D^op` 的对象是 `D` 的对象，所以这是没有传输的 [arrow_obj]。
*)
Definition coarrow_obj : D := @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U.

(*
The couniversal morphism ε : F a ~> c.  Its op-side type is
   `c ~{C^op}~> (F^op) a`, which is literally `F a ~{C}~> c`; the covariant
   ascription below is accepted by conversion alone.

--------
余宇射 ε : F a ~> c。它的对偶类型是 `c ~{C^op}~> (F^op) a`，字面意思是 `F a ~{C}~> c`；下面的协变赋值仅通过转换就被接受。
*)
Definition coarrow : F coarrow_obj ~{C}~> c :=
  @arrow (C^op) (D^op) c (Opposite_Functor F) U.

End Accessors.

(*
No [Arguments] command is needed -- or would survive: [Arguments] inside a
   [Section] is discharged at its [End].  Both accessors take c and F
   implicitly already, from the implicit [Context] binders of [Accessors], and
   that survives; likewise for every [{c}]/[{F}] below.

--------
不需要 [Arguments] 命令——而且也无法存活：[Section] 中的 [Arguments] 会在其 [End] 处被释放。两个访问器已经隐式地从 [Accessors] 的隐式 [Context] 绑定中获取 c 和 F，并且这些绑定可以存活；下面的每一个 [{c}]/[{F}] 也是一样。
*)

(*
The couniversal mapping property: any h : F d ~> c factors as
   h ≈ coarrow ∘ fmap[F] g through a unique g : d ~> coarrow_obj.  This is
   [ump_universal_arrows] read in the opposite categories -- the op-side
   composite `fmap[F^op] g ∘[C^op] arrow` IS `coarrow ∘[C] fmap[F] g` -- and
   so is supplied by [:=], with no proof step of its own.

--------
余宇映射性质：任意 h : F d ~> c 可以分解为
   h ≈ coarrow ∘ fmap[F] g，通过唯一的 g : d ~> coarrow_obj。这在对偶范畴中是
   [ump_universal_arrows] 读取的——对偶侧的
   复合 `fmapXPROTECT2X g ∘XPROTECT3X arrow` 是 `coarrow ∘XPROTECT4X fmapXPROTECT5X g`——因此由 [:=] 提供，并且不需要自身的证明步骤。
*)
Definition ump_couniversal_arrows {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) {d : D} (h : F d ~{C}~> c) :
  ∃! g : d ~{D}~> coarrow_obj U, h ≈ coarrow U ∘ fmap[F] g :=
  @ump_universal_arrows (C^op) (D^op) c (Opposite_Functor F) U d h.

(*
Conversely, the couniversal mapping property reconstructs the couniversal
   arrow.  Again a definitional op-read of [universal_arrow_from_UMP].

--------
相反，余普遍映射性质重构了余普遍箭头。再次对 [universal_arrow_from_UMP] 进行定义性的反向读取。
*)
Definition couniversal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D)
  (ε : F d ~{C}~> c)
  (u : ∀ (d' : D) (f : F d' ~{C}~> c), ∃! g : d' ~{D}~> d, f ≈ ε ∘ fmap[F] g)
  : CouniversalArrow c F :=
  @universal_arrow_from_UMP (C^op) (D^op) c (Opposite_Functor F) d ε u.

(** ** The terminal-object reading (Mac Lane §III.1 Definition 3) / ** 终端对象的读法（Mac Lane §III.1 定义 3） *)

(*
Mac Lane defines a couniversal arrow from F to c as a TERMINAL object of
   the comma category F ↓ =(c), and that reading is delivered here as a pair
   of conversions rather than as the definition, for the reason the header
   gives: the opposite-side comma category indexes its objects by `1 ∏ D^op`
   where this one indexes by `D ∏ 1`, and [Product] of categories is not
   symmetric on the nose.  Test/ProbeCouniversal.v pins that boundary.

   The two constructions below are the exact duals of [arrow_initial] and
   [universal_arrow_from_UMP], run through the couniversal mapping property.

--------
Mac Lane 将从 F 到 c 的共通箭头定义为逗号范畴 F ↓ =(c) 的终对象，而这里的解读是作为一对转换而非定义，理由如标题所述：对侧的逗号范畴通过 `1 ∏ D^op` 索引其对象，而此处则通过 `D ∏ 1` 索引，并且范畴的 [Product] 并非字面上的对称。Test/ProbeCouniversal.v 验证了这一边界。

下面的两个构造是 [arrow_initial] 和 [universal_arrow_from_UMP] 的精确对偶，通过共通映射性质运行。
*)

(*
Locating the mismatch: it is NOT the terminal/initial axis.  `Initial K`
   is notation for `@Terminal (K^op)` (Structure/Initial.v) and
   `(K^op)^op = K` holds by conversion (Construction/Opposite.v), so the
   terminal object of F ↓ =(c) IS an initial object of its opposite, for
   free.  What the op-instantiation cannot supply is the COMMA CATEGORY.
   Convertibility of types, not an equation between morphisms.

--------
定位不匹配：它不是末端/初始范畴。`Initial K` 是 `@Terminal (K^op)`（Structure/Initial.v）的记号，而 `(K^op)^op = K` 通过转换（Construction/Opposite.v）成立，因此 F ↓ =(c) 的末端对象就是其对偶范畴的初始对象，免费提供。op-实例化无法提供的是逗号范畴。类型的可转换性，而不是态射之间的等式。
*)
Corollary terminal_is_initial_op {c : C} {F : D ⟶ C}
  (T : @Terminal (F ↓ =(c))) : @Initial ((F ↓ =(c))^op).
Proof. exact T. Defined.

Definition couniversal_arrow_terminal {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) : @Terminal (F ↓ =(c)).
Proof.
  unshelve eapply Build_Terminal.
  - (* the terminal object is the couniversal pair (a, ε) / 终端对象是共普遍对 (a, ε) *)
    exact (((coarrow_obj U, ttt); coarrow U)).
  - (* the unique arrow into it is the UMP mediator / 进入它的独特箭头是UMP调解器 *)
    intros [[d u] h]; simpl in *.
    exists (unique_obj (ump_couniversal_arrows U h), ttt).
    simpl.
    (* [simpl] has already reduced fmap[=(c)] ttt to id[c] / [simpl] 已经将 fmap[=(c)] ttt 减少到 id[c] *)
    rewrite id_left.
    symmetry.
    exact (unique_property (ump_couniversal_arrows U h)).
  - (*
two arrows into it agree: the D-components by UMP uniqueness, the
       1-components because `1` has exactly one arrow

--------
两个箭头指向它一致：D 分量因为 UMP 唯一性，1 分量因为 `1` 恰好有一个箭头
*)
    intros [[d u] h] [[f1 f2] Hf] [[g1 g2] Hg]; simpl in *.
    rewrite ?fmap_id, ?id_left in Hf, Hg.
    split.
    + rewrite <- (uniqueness (ump_couniversal_arrows U h) f1 (symmetry Hf)).
      exact (uniqueness (ump_couniversal_arrows U h) g1 (symmetry Hg)).
    + now destruct f2, g2.
Defined.

(*
The transported structure chooses the couniversal object on the nose --
   what makes [couniversal_arrow_terminal] a transport rather than a bare
   existence claim, in the idiom of [Terminal_iso_obj] (Structure/Initial.v).
   Convertibility of OBJECTS, not an equation between morphisms.

--------
被传输的结构精确选择范宇对象——这使得 [couniversal_arrow_terminal] 成为一种传输而不是单纯存在声明，在 [Terminal_iso_obj]（Structure/Initial.v）的表达习惯中。是对象的可转换性，而不是态射之间的方程。
*)
Corollary couniversal_arrow_terminal_obj {c : C} {F : D ⟶ C}
  (U : CouniversalArrow c F) :
  `1 (@terminal_obj _ (couniversal_arrow_terminal U)) = (coarrow_obj U, ttt).
Proof. reflexivity. Qed.

(* ... and back: a terminal object of F ↓ =(c) is a couniversal arrow. / ... 和回：F ↓ =(c) 的终端对象是一个共通箭头。 *)
Definition couniversal_arrow_of_terminal {c : C} {F : D ⟶ C}
  (T : @Terminal (F ↓ =(c))) : CouniversalArrow c F.
Proof.
  destruct T as [t one one_unique].
  destruct t as [[a u] ε]; simpl in *.
  unshelve eapply (couniversal_arrow_from_UMP c F a ε).
  intros d' f.
  (*
every factorization of f through ε satisfies the comma square, whose
     =(c)-leg computes to id[c].  Kept as a bare square proof rather than as a
     packaged comma morphism so that the pairs below are literal sigmas: the
     [fst `1] projections of an opaque hypothesis would not reduce.

--------
f 通过 ε 的每一个分解都满足逗号方格，其 =(c)-支计算为 id[c]。保持为一个裸方格证明而不是作为一个封装的逗号态射，以便下面的对是字面上的 σ：不透明假设的 [fst `1] 投影不会约简。
*)
  assert (sq : ∀ v : d' ~{D}~> a, f ≈ ε ∘ fmap[F] v →
                 ε ∘ fmap[F] v ≈ id{C} ∘ f).
  { intros v Hv.
    rewrite id_left.
    now symmetry. }
  destruct (one (((d', ttt); f))) as [[g1 g2] Hg]; simpl in Hg.
  rewrite id_left in Hg.
  unshelve eexists g1.
  - now symmetry.
  - intros v Hv.
    exact (fst (one_unique (((d', ttt); f))
                           ((g1, ttt); sq g1 (symmetry Hg))
                           ((v, ttt); sq v Hv))).
Defined.

(** ** Uniqueness up to a unique isomorphism / ** 至多唯一同构的唯一性 *)

(*
The duals of the mediator calculus added to Theory/Universal/Arrow.v for
   Awodey's Proposition 1.10.  Each is the primal statement read in the
   opposite categories, so each is supplied by [:=] or by a one-line [exact];
   note that the ARGUMENT ORDER swaps, since the op-side mediator
   `arrow_obj U1 ~{D^op}~> arrow_obj U2` is covariantly a morphism
   `coarrow_obj U2 ~> coarrow_obj U1`.

--------
为了 Awodey 的命题 1.10，将中介子演算的对偶添加到 Theory/Universal/Arrow.v 中。每一个都是在相反范畴中读出的原始陈述，因此每一个都由 [:=] 提供或由一行 [exact] 提供；请注意，参数顺序发生了交换，因为 op 端的中介 `arrow_obj U1 ~{D^op}~> arrow_obj U2` 在协变意义上是一个态射 `coarrow_obj U2 ~> coarrow_obj U1`。
*)

Section CouniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

(*
The canonical mediating morphism: the unique factorization of the FIRST
   couniversal arrow through the SECOND (dual to the primal orientation).

--------
典范中介态射：第一个对普遍箭通过第二个箭的唯一分解（与原始方向的对偶）。
*)
Definition cua_med (U1 U2 : CouniversalArrow c F)
  : coarrow_obj U1 ~{D}~> coarrow_obj U2 :=
  @ua_med (C^op) (D^op) c (Opposite_Functor F) U2 U1.

Lemma cua_med_commutes (U1 U2 : CouniversalArrow c F) :
  coarrow U2 ∘ fmap[F] (cua_med U1 U2) ≈ coarrow U1.
Proof. exact (@ua_med_commutes (C^op) (D^op) c (Opposite_Functor F) U2 U1). Qed.

(* Any morphism commuting with the two couniversal arrows IS the mediator. / 与两个余普遍箭头交换的任何态射都是中介者。 *)
Lemma cua_med_unique (U1 U2 : CouniversalArrow c F)
      (g : coarrow_obj U1 ~{D}~> coarrow_obj U2) :
  coarrow U2 ∘ fmap[F] g ≈ coarrow U1 → cua_med U1 U2 ≈ g.
Proof.
  exact (@ua_med_unique (C^op) (D^op) c (Opposite_Functor F) U2 U1 g).
Qed.

Lemma cua_med_id (U1 : CouniversalArrow c F) : cua_med U1 U1 ≈ id.
Proof. exact (@ua_med_id (C^op) (D^op) c (Opposite_Functor F) U1). Qed.

Lemma cua_med_comp (U1 U2 U3 : CouniversalArrow c F) :
  cua_med U2 U3 ∘ cua_med U1 U2 ≈ cua_med U1 U3.
Proof. exact (@ua_med_comp (C^op) (D^op) c (Opposite_Functor F) U3 U2 U1). Qed.

(*
The two mediators are mutually inverse, so the couniversal objects are
   isomorphic.  [Isomorphism_Opposite] reads the op-side isomorphism back
   into `(D^op)^op`, which IS `D`; it exchanges [to] and [from], which is
   exactly what makes the [to] component come out as [cua_med U1 U2].

--------
这两个中介是相互逆的，因此余普遍对象是同构的。[Isomorphism_Opposite] 将对侧同构读回到 `(D^op)^op` 中，而 `(D^op)^op` 就是 `D`；它交换了 [to] 和 [from]，这正是使 [to] 组件变为 [cua_med U1 U2] 的原因。
*)
Definition couniversal_arrow_iso (U1 U2 : CouniversalArrow c F)
  : coarrow_obj U1 ≅ coarrow_obj U2 :=
  @Isomorphism_Opposite (D^op) _ _
    (@universal_arrow_iso (C^op) (D^op) c (Opposite_Functor F) U1 U2).

Corollary couniversal_arrow_iso_to (U1 U2 : CouniversalArrow c F) :
  to (couniversal_arrow_iso U1 U2) ≈ cua_med U1 U2.
Proof. reflexivity. Qed.

Corollary couniversal_arrow_iso_from (U1 U2 : CouniversalArrow c F) :
  from (couniversal_arrow_iso U1 U2) ≈ cua_med U2 U1.
Proof. reflexivity. Qed.

Lemma couniversal_arrow_iso_unique (U1 U2 : CouniversalArrow c F)
      (v : coarrow_obj U1 ≅ coarrow_obj U2) :
  coarrow U2 ∘ fmap[F] (to v) ≈ coarrow U1 →
  couniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply cua_med_unique.
Qed.

(*
Awodey's Proposition 1.10, dualized: exactly one isomorphism of the
   couniversal objects carries the second couniversal arrow to the first.

--------
Awodey 的命题 1.10，对偶化：恰好有一个余普遍对象的同构将第二个余普遍箭头映射到第一个。
*)
Program Definition couniversal_arrow_unique
        (U1 U2 : CouniversalArrow c F) :
  Unique (fun i : coarrow_obj U1 ≅ coarrow_obj U2 =>
            coarrow U2 ∘ fmap[F] (to i) ≈ coarrow U1) := {|
  unique_obj      := couniversal_arrow_iso U1 U2;
  unique_property := cua_med_commutes U1 U2
|}.
Next Obligation. exact (couniversal_arrow_iso_unique U1 U2 v X). Qed.

End CouniversalArrowUnique.

(** ** From couniversal arrows to a right adjoint / ** 从共普遍箭头到右伴随 *)

Context (F : @Functor D C).

(*
A couniversal arrow from F to every object c : C assembles into a right
   adjoint of F.  The object map sends c to its couniversal object, and the
   morphism map sends f : x ~> y to the unique factorization of f ∘ coarrow
   through coarrow_obj y.  Both are read off [Opposite_Functor] applied to the
   primal assembly, so `C ⟶ D` is the type on the nose -- no comparison
   functor and no transport.

--------
从 F 到每个对象 c : C 的一个对普遍箭头可以组装成 F 的一个右伴随。对象映射将 c 发送到它的对普遍对象，而态射映射将 f : x ~> y 发送到 f ∘ 对箭头通过 coarrow_obj y 的唯一分解。这两者都是直接应用 [Opposite_Functor] 于原始组合读出来的，因此 `C ⟶ D` 是精确类型 —— 没有比较函子，也没有迁移。
*)
Definition RightAdjointFunctorFromCouniversalArrows
  (H : forall c : C, CouniversalArrow c F) : @Functor C D :=
  Opposite_Functor
    (@LeftAdjointFunctorFromUniversalArrows (C^op) (D^op)
       (Opposite_Functor F) H).

(*
The object action is [coarrow_obj] by convertibility -- what makes the
   op-route usable rather than merely type-correct.

--------
对象动作是通过可转换性 [coarrow_obj] —— 这使得操作路径可用，而不仅仅是类型正确。
*)
Corollary right_adjoint_obj (H : forall c : C, CouniversalArrow c F) (c : C) :
  fobj[RightAdjointFunctorFromCouniversalArrows H] c = coarrow_obj (H c).
Proof. reflexivity. Qed.

(*
The induced functor is genuinely right adjoint to F, with the couniversal
   arrows serving as the components of the counit.  [Opposite_Adjunction]
   supplies the whole proof: `(C^op)^op = C` and `(F^op)^op = F` both hold by
   [reflexivity], so the dual of the opposite-side adjunction lands at
   `F ⊣ RightAdjointFunctorFromCouniversalArrows H` with nothing to
   transport.

--------
诱导函子是真正的 F 的右伴随，而协普遍箭头作为余单位的组成部分。[Opposite_Adjunction] 提供了完整的证明：`(C^op)^op = C` 和 `(F^op)^op = F` 都由 [reflexivity] 成立，因此对偶的对边伴随到达 `F ⊣ RightAdjointFunctorFromCouniversalArrows H`，没有任何需要传输的东西。
*)
Definition AdjunctionFromCouniversalArrows
  (H : forall c : C, CouniversalArrow c F) :
  F ⊣ RightAdjointFunctorFromCouniversalArrows H :=
  Opposite_Adjunction
    (@LeftAdjointFunctorFromUniversalArrows (C^op) (D^op)
       (Opposite_Functor F) H)
    (Opposite_Functor F)
    (@AdjunctionFromUniversalArrows (C^op) (D^op) (Opposite_Functor F) H).

(*
The counit of that adjunction is the couniversal arrow.  Only up to `≈`:
   the transpose delivers `coarrow ∘ fmap[F] id`, which is one [fmap_id] and
   one [id_right] short of [eq_refl].  See the header's second boundary; the
   negative half is pinned in Test/ProbeCouniversal.v.

--------
该伴随的余单位是余通用箭头。仅限于 `≈`：
   转置提供了 `coarrow ∘ fmapXPROTECT0X id`，它距离 [eq_refl] 差一个 [fmap_id] 和一个 [id_right]。见头文件的第二个边界；负半部分固定在 Test/ProbeCouniversal.v 中。
*)
Lemma counit_couniversal (H : forall c : C, CouniversalArrow c F) (c : C) :
  @counit C D F (RightAdjointFunctorFromCouniversalArrows H)
          (AdjunctionFromCouniversalArrows H) c ≈ coarrow (H c).
Proof.
  unfold counit; simpl.
  rewrite fmap_id.
  apply id_right.
Qed.

(** ** The direct encoding / ** 直接编码 *)

(*
The same notion stated directly, with the couniversal object a : D given as
   a parameter rather than projected out.  Definitionally [AUniversalArrow] in
   the opposite categories, exactly as [CouniversalArrow] is [UniversalArrow]
   there.

--------
相同的概念直接陈述，具有共通对象 a : D 作为参数而不是被投射出来。在对偶范畴中按定义 [AUniversalArrow]，正如 [CouniversalArrow] 在那里是 [UniversalArrow] 一样。
*)
Definition ACouniversalArrow (c : C) (G : D ⟶ C) (a : D) : Type :=
  @AUniversalArrow (C^op) (D^op) c (Opposite_Functor G) a.

Existing Class ACouniversalArrow.

(* The couniversal morphism ε : F a ~> c, covariantly. / 共变上的通用态射 ε : F a ~> c。 *)
Definition couniversal_arrow {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) : G a ~{C}~> c :=
  @universal_arrow (C^op) (D^op) c (Opposite_Functor G) a U.

(*
... and its universal property, in the orientation the primal field has
   ([fmap ∘ arrow ≈ f] there, [arrow ∘ fmap ≈ f] here).

--------
... 及其泛性质，在取向上原始场具有 ([fmap ∘ arrow ≈ f]那里, [arrow ∘ fmap ≈ f]这里)。
*)
Definition couniversal_arrow_couniversal {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) {d : D} {f : G d ~{C}~> c} :
  Unique (fun g : d ~{D}~> a => couniversal_arrow U ∘ fmap[G] g ≈ f) :=
  @universal_arrow_universal (C^op) (D^op) c (Opposite_Functor G) a U d f.

(*
Two couniversal arrows at the same object are equivalent when their
   underlying morphisms agree; the op-read of [AUniversalArrowEquiv].

--------
当两个指向同一对象的共宇箭头的底层态射一致时，它们是等价的；[AUniversalArrowEquiv] 的反向读取。
*)
#[export] Instance ACouniversalArrowEquiv (c : C) (G : D ⟶ C) (a : D) :
  Setoid (ACouniversalArrow c G a) :=
  @AUniversalArrowEquiv (C^op) (D^op) c (Opposite_Functor G) a.

Section ACouniversalArrowUnique.

Context {c : C}.
Context {G : D ⟶ C}.

Definition acua_med {a b : D} (U1 : ACouniversalArrow c G a)
           (U2 : ACouniversalArrow c G b) : a ~{D}~> b :=
  @aua_med (C^op) (D^op) c (Opposite_Functor G) b a U2 U1.

Lemma acua_med_commutes {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) :
  couniversal_arrow U2 ∘ fmap[G] (acua_med U1 U2) ≈ couniversal_arrow U1.
Proof.
  exact (@aua_med_commutes (C^op) (D^op) c (Opposite_Functor G) b a U2 U1).
Qed.

Lemma acua_med_unique {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (g : a ~{D}~> b) :
  couniversal_arrow U2 ∘ fmap[G] g ≈ couniversal_arrow U1 → acua_med U1 U2 ≈ g.
Proof.
  exact (@aua_med_unique (C^op) (D^op) c (Opposite_Functor G) b a U2 U1 g).
Qed.

Lemma acua_med_id {a : D} (U1 : ACouniversalArrow c G a) : acua_med U1 U1 ≈ id.
Proof. exact (@aua_med_id (C^op) (D^op) c (Opposite_Functor G) a U1). Qed.

Lemma acua_med_comp {a b e : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (U3 : ACouniversalArrow c G e) :
  acua_med U2 U3 ∘ acua_med U1 U2 ≈ acua_med U1 U3.
Proof.
  exact (@aua_med_comp (C^op) (D^op) c (Opposite_Functor G) e b a U3 U2 U1).
Qed.

Definition acouniversal_arrow_iso {a b : D} (U1 : ACouniversalArrow c G a)
        (U2 : ACouniversalArrow c G b) : a ≅ b :=
  @Isomorphism_Opposite (D^op) _ _
    (@auniversal_arrow_iso (C^op) (D^op) c (Opposite_Functor G) a b U1 U2).

Lemma acouniversal_arrow_iso_unique {a b : D} (U1 : ACouniversalArrow c G a)
      (U2 : ACouniversalArrow c G b) (v : a ≅ b) :
  couniversal_arrow U2 ∘ fmap[G] (to v) ≈ couniversal_arrow U1 →
  acouniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply acua_med_unique.
Qed.

Program Definition acouniversal_arrow_unique {a b : D}
        (U1 : ACouniversalArrow c G a) (U2 : ACouniversalArrow c G b) :
  Unique (fun i : a ≅ b =>
            couniversal_arrow U2 ∘ fmap[G] (to i) ≈ couniversal_arrow U1) := {|
  unique_obj      := acouniversal_arrow_iso U1 U2;
  unique_property := acua_med_commutes U1 U2
|}.
Next Obligation. exact (acouniversal_arrow_iso_unique U1 U2 v X). Qed.

End ACouniversalArrowUnique.

(** ** The two encodings agree / ** 这两种编码一致 *)

(*
Theory/Universal/Arrow.v carries both encodings but never relates them;
   here the passage is cheap in both directions, so it is supplied.  Note the
   orientations of the two universal properties differ by a [symmetry]
   ([h ≈ ε ∘ fmap g] in the comma-packaged form, [ε ∘ fmap g ≈ f] in the
   direct one), which is the whole content of the two proofs.

--------
Theory/Universal/Arrow.v 同时包含两种编码，但从未将它们关联起来；这里该转换在两个方向上都是简单的，因此提供了它。注意两个泛性质的取向相差一个 [symmetry]（在逗号打包形式中为 [h ≈ ε ∘ fmap g]，在直接形式中为 [ε ∘ fmap g ≈ f]），这就是两个证明的全部内容。
*)

Definition ACouniversalArrow_of_CouniversalArrow {c : C} {G : D ⟶ C}
  (U : CouniversalArrow c G) : ACouniversalArrow c G (coarrow_obj U).
Proof.
  unshelve econstructor.
  - exact (coarrow U).
  - intros d f.
    unshelve eexists (unique_obj (ump_couniversal_arrows U f)).
    + symmetry; exact (unique_property (ump_couniversal_arrows U f)).
    + intros v Hv.
      exact (uniqueness (ump_couniversal_arrows U f) v (symmetry Hv)).
Defined.

Definition CouniversalArrow_of_ACouniversalArrow {c : C} {G : D ⟶ C} {a : D}
  (U : ACouniversalArrow c G a) : CouniversalArrow c G.
Proof.
  unshelve eapply (couniversal_arrow_from_UMP c G a (couniversal_arrow U)).
  intros d' f.
  unshelve eexists (unique_obj (@couniversal_arrow_couniversal c G a U d' f)).
  - symmetry.
    exact (unique_property (@couniversal_arrow_couniversal c G a U d' f)).
  - intros v Hv.
    exact (uniqueness (@couniversal_arrow_couniversal c G a U d' f) v
             (symmetry Hv)).
Defined.

(* The passage keeps the arrow on the nose in one direction ... / 这段文字保持箭头在鼻子上朝一个方向... *)
Corollary ACouniversalArrow_of_CouniversalArrow_arrow {c : C} {G : D ⟶ C}
  (U : CouniversalArrow c G) :
  couniversal_arrow (ACouniversalArrow_of_CouniversalArrow U) = coarrow U.
Proof. reflexivity. Qed.

(* ... and in the other. / ... 在另一个里面。 *)
Corollary CouniversalArrow_of_ACouniversalArrow_arrow {c : C} {G : D ⟶ C}
  {a : D} (U : ACouniversalArrow c G a) :
  coarrow (CouniversalArrow_of_ACouniversalArrow U) = couniversal_arrow U.
Proof. reflexivity. Qed.

Corollary CouniversalArrow_of_ACouniversalArrow_obj {c : C} {G : D ⟶ C}
  {a : D} (U : ACouniversalArrow c G a) :
  coarrow_obj (CouniversalArrow_of_ACouniversalArrow U) = a.
Proof. reflexivity. Qed.

End CouniversalArrow.

Arguments CouniversalArrow {C D} c F.
Arguments ACouniversalArrow {C D} c G a.
