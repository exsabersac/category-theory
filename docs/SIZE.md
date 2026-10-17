# 大小与基础 (Size and foundations)

本文说明本库如何处理 Mac Lane《Categories for the Working Mathematician》§I.6 中的问题——宇宙、小集合、类、大范畴——以及为何他的若干定义在此没有对应物。

书目**仅按位置引用**。撰写本文时未查阅印刷正文；位置记录各项在何处陈述，下文关于*本库*的每一断言都对照源码核对，并给出文件与行号。

---

## 简短回答

Mac Lane 固定 ZFC 加上一个 Grothendieck 宇宙 `U`，当集合、函数或范畴落在 `U` 内时称为**小**。本库不声明宇宙、不声明成员关系、也不声明大小公理。`U` 所做的工作改由**宇宙多态**完成：`Class Category@{o h p | h <= p}`（`Theory/Category.v`）给每个范畴各自三个层级——

| 层级 | 住在那里的东西 | 字段 |
|---|---|---|
| `o` | 对象 | `obj : Type@{o}` |
| `h` | 每个 hom 集 | `hom : obj → obj → Type@{h}` |
| `p` | hom-setoid 的证明 | `homset : ∀ X Y, Setoid@{h p} (X ~> Y)` |

——约束求解器在每个使用点强制分层。经审计的结论是：核心理论完全不需要大小公理（`docs/AXIOMS.md`）。

自该 issue 的工作起，*词汇*也已存在：`Theory/Size.v` 声明了 `Small` 与 `LocallySmall`；此前树中任何地方都没有声明（`Theory/Lawvere/Sets.v` 顺便记录过缺口——「库没有小性机制」）。

---

## Mac Lane §I.6，逐项

### def1 — 宇宙 `U`

**故意没有对应物。** 没有带闭包条件的 `Universe` 对象，也没有成员关系。Coq 自身的累积层级 `Type@{i}` 扮演该角色，但它是元理论的特征而非理论中的对象：不能在 Coq 内部量化层级，因此 `U` 不能是变量。

实际差别：Mac Lane 的 `U` 是*一个*固定宇宙，扩大它是刻意行为。这里每个构造都是多态的，故同时存在于**每一**层级，层级由推断在每个使用点选定。

### def2 — 小集合与小函数

部分有，且比摘要行暗示的更少。*小集合*变成「指定层级上的类型」，可直接写成 `Type@{u}`——但**未声明小集合谓词**。`Small` 只是*范畴*上的谓词；它使用相对层级的观念，而非提供该观念本身。同样没有小*函数*的概念：层级 `u` 上类型之间的函数自动住在 `u`。

### def4 — 小范畴

**`Small`（`Theory/Size.v`）。** 依 Awodey Definition 1.11 与 Riehl Definition 1.1.6，当对象与箭头都在严格更低层级有匹配副本时，范畴是小的：

```coq
Class Small@{o h p uo uh up | h <= p, uh <= up, uo < o, uh < h} (C : Category@{o h p})
```

全部内容在 `uo < o` 与 `uh < h`。没有它们，对每个 `C` 都可把 `obj[C]` 与 `hom` 自身交回以消解 `Small C`。这不是断言式论证：`Test/Size.v` 的 `A253_trivial_small` 正好写了这种消解，且被**拒绝**。

对象按 **`ObjEq`** 匹配（`Theory/Size.v` 中声明的层级多态恒等类型——*不是* stdlib `=`）。Hom 按 **setoid 同构**匹配（两方向都尊重 `≈`）。

两种选择都非风格问题。态射不能用 `=`，因 CLAUDE.md 禁止在其上用。对象也不能用，且有独立且更残酷的原因适用于**两半**：stdlib `eq` 在 Coq 8.19/8.20 上钉在全局宇宙，在带显式宇宙约束子句的定义内提及它会得到 `Universe constraints are not implied by the ones declared: o <= eq.u0`，binder 没有语法可消解。对象在本库没有 setoid，故 `=` 不可用时需要*某种*恒等类型，而层级多态谓词需要层级多态的恒等——故有 `ObjEq`，沿用 `Lib/Setoid.v` 的 `poly_unit@{u}` 惯用法。

### def5 — 类

**没有对应物。** 类是 `U` 的子集，需要成员关系。此处无对应；「类大小」的汇集只是更高层级上的类型。同样没有*真类*：它区分的——大到不能作为元素——改由宇宙不一致性表达。

### def6 — 大范畴

**没有作为谓词的对应物**，这是值得点名的真实不对称。`Small` 是可假设或可推出的谓词。「大」在任何可用意义上都不是其否定：对给定 `C` 反驳 `Small C` 需要说明在*任何*更低层级都不存在 resizing，这是关于元理论的陈述，不是 Coq 命题。因此树可以说「此范畴是小的」，不能说「这个不是」。

### remark1 — `Set` 不是自身的对象

这里该文档所针对的 issue **双重失误**，纠正是此处最有趣的形式内容。

Issue 要求 `Fail Check` 见证：「`Sets` 作为自身的对象、`Cat` 作为自身的对象」是宇宙不一致。

**第一：`Check (Cat : obj[Cat])` 成功。** 根本不是自成员见证。`Cat` 是宇宙多态的，elaborator 在*不同*层级实例化两处出现；实际检查的是 `Cat@{i…} : obj[Cat@{j…}]`，后者严格高于前者。`Set Printing Universes` 显示两个不同实例，`About Cat`：`Cat@{u u0 u1 u2 u3} : Category@{u u0 u0}` 且 `u2 < u`、`u3 < u`。因此 `Fail Check (Cat : obj[Cat])` 甚至编不过——命令不会失败。**这是设计的定理，不是失败**，正是 Riehl 的「`Cat` 是 `CAT` 的对象」（见下文 §1.3）。

演示必须**在两侧钉住同一实例**：

```coq
Fail Definition B253_cat_self@{a b c d e} : obj[Cat@{a b c d e}] := Cat@{a b c d e}.
```

这被拒绝，且仅因宇宙——归属在形状上类型正确，因为 `obj[Cat]` *就是* `Category` 而 `Cat` *就是*一个 `Category`，只有约束求解器能拒绝。这是 Mac Lane 该注记的真正形式对应，也是 `Instance/Cat.v` 文首短文所说「由 elaborator 抓住的宇宙不一致，而非要用公理排除的悖论」之意。

**第二：对 `Sets` 根本不是宇宙问题。** `obj[Sets]` 是 `SetoidObject`——载体配上 setoid——而 `Sets` 是 `Category`。范畴不是 setoid，故 `Sets : obj[Sets]` 是**普通类型错误**，无论何层级皆然。钉实例改变不了什么。

### remark2 — 哪些公理在起作用

`docs/AXIOMS.md` 是审计。标题结论：`Theory/`（排除 `Theory/Coq/`）、`Structure/`、`Construction/` 中每个携带证明的常量**零公理**；具体实例层（`Instance/`、`Theory/Coq/`）使用 stdlib 公理，在彼处枚举。尤其任何地方都未声明宇宙公理——分层是结构性的。

### remark3 — 无集合的替代

Mac Lane 的两个指针**实际上都已形式化**，使本项不止于映射：

- *未定义项上的范畴公理* — `Theory/Metacategory.v`，仅箭头公理化。其文首说了与本文相同的点：「它一度标记的大小区分，在本库中改由宇宙多态承载。」
- *`Set` 的初等 topos 公理* — `Structure/Topos.v` 的 `ElementaryTopos`，由 `FinSet_Topos` 居住。

---

## Awodey

### §1.8 Definition 1.11 — 小

匹配上文 `Small`：对象 `C₀` 与箭头 `C₁` 都是集合。**箭头**半边说明为何 `Small` 需要两个约束而不只是 hom 约束——总箭头汇集捆绑端点，故其层级至少是对象的层级。`Theory/Size.v` 的 `TotalMor` 即该汇集。

### §1.8 Definition 1.12 — 局部小

`LocallySmall`（`Theory/Size.v`）。此处情况真正**双边**，两边都有记录：

- 库*提供*的比书中约定**更强**。`Class Category` 的 `homset` 字段（`Theory/Category.v`）给每个范畴固定层级的 hom-setoid，故局部小性由构造成立，非局部小范畴不可表达。这是 `locally_small_ambient`，写成**引理**而非散文。
- 库*缺少*的是陈述该区分所需的谓词。这正是 `LocallySmall` 所提供。

因第一点，`LocallySmall` 以**非严格** `uh <= h` 声明，使环境实例存在；在严格更小的 `uh` 上实例化才是有内容的读法。对比之下 `Small` 全程严格。两种选择都不是疏忽。

### §8.3 Remark 8.4 — Yoneda 大小三分法

Awodey 的三种情形，对照本树：

| 情形 | Awodey | 此处 |
|---|---|---|
| (i) `C` 小 ⇒ `Sets^(C^op)` 局部小 | 需要小性 | 现可表述；*未证明* — 见下 |
| (ii) 即使 `Sets^(C^op)` 非局部小，`Hom(y C, P) ≅ P C` 仍是集合 | 有趣情形 | **被预设，非被推出** |
| (iii) `C` 非局部小 ⇒ `y` 不可定义 | — | **不会出现**：局部小性内建于 `Class Category` |

情形 (ii) 值得强调。树内 `Yoneda_Lemma` 并不*推出* `Hom(y C, P)` 是集合——它**预设**这一点，且不可避免：其 `≅` 两侧必须已是 `Sets`-对象才能通过类型检查，经由 `Functor/Hom.v` 中声明的 coercion。相关地，同一文件对*任意*无边条件的 `C` 定义 `Hom (C : Category) : C^op ∏ C ⟶ Sets`，故 hom 汇集总落在环境层级的 `Sets` 中。

**两种情形都未在 Coq 中陈述。** 本节仅为文档，且是 #253 未完成而非已交付的复选框：

- 情形 (i) 现因词汇就位而*可陈述*，但**未证明** — 需要从 `C` 的对象层级计算自然变换类型的层级，超出本 issue 范围。
- 情形 (ii) 是**描述，非形式化**。描述准确 — `Functor/Hom/Yoneda.v` 陈述 `Yoneda_Lemma : ∀ A : C, Presheaves [Hom ─,A] F ≅ F A`，两侧经 `Functor/Hom.v` 的 coercion 由构造即为 `Sets`-对象 — 但记录树内引理预设该内容，不等于推出它。

---

## Riehl

### §1.1 Remark 1.1.5 — 刻意分歧

Riehl 采用可数不可达塔的工作约定，使每一层都是可按需扩大的 Grothendieck 宇宙，**而不是**用宇宙层级参数化定义。

这与本库的方法论选择*相反*，值得记为分歧而非遗漏。Riehl 固定一层并在被迫时扩大；这里什么都不固定——每个定义都是多态且与层级无关，求解器在每个使用点选层级。两者都无对错之分；代价是 Riehl 的约定让陈述更可读，本库的约定让陈述无公理。

已核对：`rg -i 'Grothendieck universe|inaccessible|V_kappa|proper class|Russell'` 只返回散文命中，全在 `Instance/Cat.v` 文首短文——**任何地方都未声明宇宙公理**；树中仅有的 `Parameter` 是 `Instance/ZX.v` 中三个文档化的 ZX `Phase`。同一短文已解释自成员由多态而非大小公理阻挡。

### §1.1 Definition 1.1.6 — 小，以及带 `dom`/`cod` 的箭头包装

小性半边是 `Small`。*包装*半边——对象集、态射集，以及 `dom`、`cod`、`id` 且 `dom` 与 `cod` 收回 `id`——是 `Theory/Size.v` 中的 `ArrowQuiver` 与 `ArrowQuiverOfCat`。

两种呈现都给出，因为差别恰在**收回定律住在何处**：

- 树中 `Quiver`（`Construction/Free/Quiver.v`）是**指标化**呈现，`edges : nodes → nodes → Type`，其中 `dom` 与 `cod` 由指标携带。它完全没有恒等选取，故不提供 Riehl 收回的任一半，此前树中也不存在自反 quiver。
- `ArrowQuiver` 是 Riehl 实际陈述的**非指标化**呈现。那里收回是候选必须满足的真正等式——此处它们由 `obj_refl`（`ObjEq` 构造子）成立，因为恒等箭头存储其端点。

这是库的表述使书中公理*消失*而非证明它的情形，值得记录。

### §1.1 Definition 1.1.7 — 局部小

见上文 Awodey 1.12。Riehl 的用法——「Example 1.1.3 中的范畴都不是小的，但每个都是局部小的」——在此命运不对称：第二句是 `locally_small_ambient`（引理）；第一句**不可陈述**，原因见 Mac Lane def6。

### §1.3 — 两层 `Cat` 与 `CAT`

Riehl 划出两层：`Cat` 以*小*范畴为对象，局部小但不小；`CAT` 以*局部小*范畴为对象，自身非局部小，并接收来自 `Cat` 的包含，其中 `Cat` 是其对象。

**本库把该区分渲染为单一多态构造，且现已有机器检查事实支撑而非仅靠论证。** 只有一个 `Cat`，声明于 `Instance/Cat.v`，且 `Check (Cat : obj[Cat])` **成功** — 在两个不同宇宙实例上，如上 remark1 所示。故「`Cat` 是 `CAT` 的对象」不是要另建的一层；它就是多态 `Cat` 已说的话，`CAT` 是下一实例上的 `Cat`。没有要定义的 `Cat'`，在 `LocallySmall` 上定义第二层也不会产生新东西，因为**每个**范畴在环境层级满足 `LocallySmall`（`locally_small_ambient`）。

一并记录：`Cat` 的 hom-setoid **就是**自然同构（`Instance/Cat.v`），故 `≅[Cat]` 已指*等价*，而非范畴同构——Riehl 所倚重的区分。真正的范畴同构须在 `StrictCat`（`Instance/StrictCat.v`）中陈述。

---

## 小性默默缺席之处

有一处值得提醒读者，因它是隐藏小性量词的最强候选：`Structure/Complete.v` 写着

```coq
Definition Complete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Limit F.
```

它量化**所有**范畴而无边条件——经典定义只要求*小*极限。约束它的不是假设，而是 `F : D ⟶ C` 对 `D` 强制的宇宙实例化。本文记录该局面的形状；不断言有何不对，此处也无断言依赖它。

该实例化不再只是形状。库对此的唯一权威说明是 **`Structure/Complete.v` 文首的大小注记**，本文在两者可能分歧的每一点上都 defer 于它。注记陈述（并测量了拒绝）：载体在 `Type@{u}` 上的 `Prop`-值关系自身在 `Type@{u}`，而 `Type`-值关系落在 `Type@{u+1}`；`Adjunction/GAFT.v` 把完备性假设应用到解集指标上的离散范畴，故指标宇宙*就是* `Complete` 的形状对象宇宙，同证明中全体自同态的等化子把它推到环境 hom 宇宙，而 `Sets_Complete` 把它封在载体宇宙；因此以具体代数范畴对象上的 Σ 为指标的解集高一个宇宙，以 `Type`-值同余为指标的亦然。六条逃脱路径均已编译并被拒绝，列于彼处。

库的回答不是小性谓词，而是特定 setoid 的性质：`PropEquiv`（`Lib/Setoid/Propositional.v`），即载体的 `≈` 在逻辑上是命题——经典数学称载体为*集合*之意。自 2026-09-17 起，`CMon`、`Ab`、`RMod R`、`Grp`、`Rig`、`Ring`、`Rng`、`Rg` 的对象记录携带它，故其项模型上的同余是载体大小的，并恰在伴随函子定理要求的宇宙为解集指标。自 #450 起，`Instance/Variety/Free.v` 的 `SetoidOpAlgebra` 亦然，每个 setoid 簇 `SVariety E` 的对象记录（字段 `soa_prop`），且 `Grp`、`Rng`、`SVariety E` 的余极限以同样方式在对角上得到（`Instance/Grp/Colimit.v`、`Instance/Rng/Colimit.v`、`Instance/Variety/Colimit.v`；大小注记第 4 项的 ADDENDUM (#450)），自 #454 起 `RMod R` 的亦然（`Instance/Mod/Colimit.v`；ADDENDUM (#454)）。`Theory/Size.v` 的 `SmallType` 与 `Adjunction/GAFT/Resize.v` 的 `SmallUpToIso`/`SmallCovering` 是随后可*陈述* Mac Lane §V.7 基数子句的词汇，而 `Instance/Mod/TensorAFT.v` 是证明该子句的唯一处。精确阅读范围：`PropEquiv` 是 setoid 的性质，从不改变 `Class Setoid`；`≈` 在全库保持 `Type`-值，因在 `Cat` 中 `F ≈ G` 是同构族；上文 `Small` 与 `LocallySmall` 不受影响——此处仍未给树 Mac Lane def2 所要、本文仍记为缺席的小集合谓词。

---

## 摘要表

| 项 | 状态 |
|---|---|
| MacLane I.6 def1（宇宙） | 无对应物 — 多态，故意 |
| def2（小集合/函数） | 观念存在（`Type@{u}`）；**未声明小集合谓词** |
| def4（小范畴） | **`Small`**，内容由被拒的平凡消解证明 |
| def5（类、真类） | 无对应物 — 需要成员关系 |
| def6（大范畴） | **不可陈述** — 否定是元理论断言 |
| remark1（`Set` 非自成员） | **已纠正**：朴素检查*成功*；钉住形式被拒；`Sets` 情形是类型错误 |
| remark2（起作用的公理） | `docs/AXIOMS.md` — 核心为零 |
| remark3（无集合替代） | **均已形式化**：`Theory/Metacategory.v`、`Structure/Topos.v` |
| Awodey 1.11（小） | `Small` |
| Awodey 1.12（局部小） | `LocallySmall` + `locally_small_ambient` |
| Awodey 8.4（Yoneda 三分） | (iii) 不会出现；(ii) 经 `Functor/Hom.v` coercion 预设；(i) 开放 |
| Riehl 1.1.5（宇宙约定） | 记为刻意分歧 |
| Riehl 1.1.6（小 + 包装） | `Small` + `ArrowQuiver`/`ArrowQuiverOfCat`（两者都提供；其*等价*未建立） |
| Riehl 1.1.7（局部小） | `locally_small_ambient`；「非小」半边不可陈述 |
| Riehl 1.3（`Cat`/`CAT`） | 单一多态构造 — 由 `Check (Cat : obj[Cat])` 见证 |
| 解集大小条件 | **不是谓词**：`Structure/Complete.v` 大小注记陈述之，`PropEquiv`（`Lib/Setoid/Propositional.v`）为具体代数范畴（且自 #450 起为每个 setoid 簇 `SVariety E`，其 `SetoidOpAlgebra` 携带 `soa_prop`）消解之，`SmallType`/`SmallUpToIso`（`Theory/Size.v`、`Adjunction/GAFT/Resize.v`）是 Mac Lane §V.7 基数子句的词汇 |
