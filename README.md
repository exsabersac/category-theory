# Coq 中的范畴论 (Category Theory in Coq)

本开发用 Coq 编码范畴论，主要目标是：能够表示与操作范畴论中的项，并把这些项在各种目标范畴中实现出来。

- 支持版本：[Coq](https://github.com/coq/coq/) 8.19–8.20 与 [Rocq](https://github.com/coq/coq/) 9.0–9.1。
- 部分内容依赖 [Coq-Equations](https://github.com/mattam82/Coq-Equations) 1.2.4–1.3.1。

## 构建 (Building)

最简单的方式是用 [Nix](https://nixos.org/)：

    nix build

默认针对 Rocq 9.1。其他版本：

    nix build .#category-theory_8_20
    nix build .#category-theory_9_0

进入带齐依赖的开发 shell：

    nix develop

之后可用标准 Makefile：

    make          # 构建全部
    make clean    # 清理构建产物
    make install  # 安装库

开发用额外目标：

    make lint           # 检查 admitted 证明与 TODO
    make format-check   # 检查行尾空白
    make format         # 修复行尾空白
    make timing         # 带每文件计时构建
    make timing-report  # 显示上次 timing 构建中最慢的文件
    make check          # 运行全部检查

安装 pre-commit hooks（需 [Lefthook](https://github.com/evilmartians/lefthook)）：

    lefthook install

## 使用 (Usage)

建议在开发中的 `_CoqProject` 里加入：

    -R <本库路径> Category

然后用下面方式引入库的核心部分：

    Require Import Category.Theory.

## 库结构 (Library structure)

本库大致分为这些主要部分：

  - 核心 `Theory`：范畴、函子、自然变换、伴随、Kan 扩张等。

  - 范畴的 `Structure`：通过与某普遍性质相关的态射，揭示范畴的内部结构。

  - 范畴的 `Construction`：在已有范畴之上构造新范畴，引入外部结构。

  - 各类 `Functor`、`Natural.Transformation`、`Adjunction` 与 `Kan.Extension` 的“种”（species）；例如带幺半结构的范畴引出保持该结构的幺半函子，进而有保持幺半映射性质的幺半变换。

  - `Instance` 目录定义各种具体范畴；有些较一般（如适用于任意 `PreOrder` 的预序范畴），但多数并不用其他范畴定义，或足够特殊。

  - 当某个概念（如极限）可用更基础的项定义时，该版本会放在派生概念的子目录中，例如 `Category.Structure.Limit` 与 `Category.Limit.Kan.Extension`。这样用来表明思想之间的关系；例如：`Category.Construction.Comma.Natural.Transformation`。因此同名文件很常见，父目录用来表达意图。

覆盖范围已延伸到经典内容的很大一部分：带（余）分解的余单子、Beck 单子性定理、正交分解系统与正则范畴、（余）端与带 Day 卷积的双函子演算、展示范畴与 Grothendieck 构造、加性与阿贝尔结构、带 mates 对应的双范畴、带 companions 与 conjoints 的伪双重范畴、带 Sets-加权极限的充实范畴论、一般与特殊伴随函子定理以及反射子范畴与正交局部化、Lawvere 理论、对称多范畴与 operad、以及以骨骼有限集上完全可计算见证给出的初等 topos 理论——全部无公理。

### 编程子库 (Programming sub-library)

在 `Theory.Coq` 中有一个子库，延续了 [coq-haskell](https://github.com/jwiegley/coq-haskell/) 的工作。该子库面向程序员，做 Coq 类型与函数范畴中的“应用范畴论”，目标是模仿 Haskell monad 层级对 Coq 用户的用处（类似 ext-lib）。部分记号也向 ext-lib 靠拢。

与常见做法不同、也是本工作的主要贡献是：这些结构的定律**不**在子库里直接定义。程序员通过证明：从其定义到（专门化到 Coq 范畴的）一般单子定义（见 `Theory.Monad`）存在一个映射，来说明其 Monad 是合法的。这样可借助其余范畴论库完成证明义务，同时尽量保持程序侧简单。

例如，定义两个 Applicative 的复合很容易；难的是从该简单定义证明它确实是 Applicative。在 coq-haskell 里做过，但需要一些 Ltac 技巧控制证明大小：

```
Program Instance Compose_ApplicativeLaws
  `{ApplicativeLaws F} `{ApplicativeLaws G} : ApplicativeLaws (F \o G).
Obligation 2. (* ap_composition *)
  (* Discharge w *)
  rewrite <- ap_comp; f_equal.
  (* Discharge v *)
  rewrite <- !ap_fmap, <- ap_comp.
  symmetry.
  rewrite <- ap_comp; f_equal.
  (* Discharge u *)
  apply_applicative_laws.
  f_equal.
  extensionality y.
  extensionality x.
  extensionality x0.
  rewrite <- ap_comp, ap_fmap.
  reflexivity.
Qed.
```

这段证明的问题在于：它只针对 Coq 上的 applicative 自函子这一特例。更一般的事实是：任意幺半范畴中任意两个松弛幺半函子也可复合。为何不借助该证明，说明我们在 Coq 中的程序侧 applicative 由构造即合法？

新子库正是这样做的。更一般的证明已经完成（太大不便粘贴），可直接引用以得到所需结论：

```
(* The composition of two applicatives is itself applicative. We establish
   this by appeal to the general proofs that:

   1. every Coq functor has strength;
   2. (also, but not needed: any two strong functors compose to a strong
      functor; if it is a Coq functor it is known to have strength); and
   3. any two lax monoidal functors compose to a lax monoidal functor. *)

Theorem Compose_IsApplicative
  `(HF : EndoFunctor F)
  `(AF : @Functor.Applicative.Applicative _ _ (FromAFunctor HF))
  `(HG : EndoFunctor G)
  `(AG : @Functor.Applicative.Applicative _ _ (FromAFunctor HG)) :
  IsApplicative (Compose_IsFunctor HF HG)
    (@Compose_Applicative
       F HF (EndoApplicative_Applicative HF AF)
       G HG (EndoApplicative_Applicative HG AG)).
Proof.
  construct.
  - apply (@Compose_LaxMonoidalFunctor _ _ _ _ _ _ _ _ AF AG).
  - apply Coq_StrongFunctor.
Qed.
```

该证明会拉入若干实例，以说明 Coq 范畴是笛卡尔、闭的，从而是闭幺半的，等等。

希望这能成为对 Coq 程序员简单有用的计算构造，与范畴论对这些结构的一般结论（例如上述幺半函子复合）的良性结合。

## 对偶 (Duality)

核心理论的定义方式使得“对偶的对偶”对 Coq 仅靠化简即可看清（即范畴、函子、自然变换、伴随、同构等的对偶之对偶中，“C^op^op = C”可由 reflexivity 得到）。

为此需要一些人为构造，例如把范畴的结合律以对称形式再写一遍，自然变换的自然性条件同理。构造这些对象时证明义务会重复，但换来陈述整个结构对偶时不必再写一套。

因此，例如余单子的定义可缩成一行：

    Definition Comonad `{M : C ⟶ C} := @Monad (C^op) (M^op).

多数对偶构造类似；例外是 `Initial` 与 `Cocartesian`。核心类虽仍用对偶构造定义，但提供了另一套表面语法与定理集（例如用 `a + b` 表示余积），让读者少一点困惑。由对偶可知 `0 + X ≅ X` 就是对偶范畴中的 `1 × X ≅ X`，但用不同记号更容易看出：在**同一**范畴里这两个同构并不相同。这一点很重要，因为 Coq 常隐藏隐式参数，读者不易察觉对偶是否介入。

## 设计决策 (Design decisions)

本库的一些特性与选择：

  - 全程用类型类呈现概念。当某个类型类实例过于一般、会与其他实例重叠时，改写成定义，之后可用 `Existing Instance` 加入实例解析。

  - 所有定义都在 Type 中，除了在 `Prop` 上定义的具体范畴实例（例如箭头为异质关系的 `Rel`）外，核心中不用 `Prop`。

  - 核心理论不使用任何公理；公理只在个别范畴实例中出现，主要是 `Coq` 范畴。

  - Hom 集定义为计算相关的 homsetoid（即用 `crelation`）。为此使用了本库自定义的 `Setoid` 变体；同样，`Sets` 范畴实际上是这类 setoid 的范畴。这增加了建立定义时的证明工作——每一层都要保持等价关系——但使范畴在“两箭头何时等价”上更灵活。

## 记号 (Notations)

库中大量记号，目的是让复杂构造对读过现代范畴论文本的人显得熟悉。主要记号包括：

 - `≈`：等价；几乎从不用相等。
 - `≈[Cat]`：某范畴（此处为 `Cat`）中箭头之间的等价；仅在类型推断失败、既要推断参数类型又要找等价类型类实例时需要。
 - `≅`：同构；用 `to` 或 `from` 取方向。
 - `≊`：专用于 `Sets` 中 hom 集之间的同构。
 - `iso⁻¹`：同构的反向。
 - `X ~> Y`：对象之间的波浪箭头表示态射。
 - `X ~{C}~> Y`：波浪箭头也可标明意图中的范畴。
 - `id[C]`：许多已知态射可标明意图范畴；有时打印格式也会用。
 - `C ⟶ D`：范畴之间的长右箭头表示函子。
 - `F ⟹ G`：函子之间的长双箭头表示自然变换。
 - `f ∘ g`：小实心圆点表示态射复合，或一般的水平复合。
 - `f ∘[Cat] g`：复合可标明意图范畴，帮助类型推断。
 - `f ○ g`：较大空心圆表示函子复合。
 - `f ⊙ g`：带点的较大圆表示同构的复合。
 - `f ∙ g`：实心复合点表示自然变换的复合，或一般的垂直复合。
 - `f ⊚ g`：内外两圆表示伴随的复合。
 - `([C, D])`：方括号中的一对范畴是函子的另一种类型写法，即 `Fun(C, D)` 中的对象。
 - `F ~{[C, D]}~> G`：函子范畴中的箭头是自然变换。
 - `F ⊣ G`：转角符表示伴随。
 - 笛卡尔范畴用 `△` 作 `fork`，用 `×` 作积。
 - 余笛卡尔范畴用 `▽` 作 `merge`，用 `+` 作余积。
 - 闭范畴用 `^` 作指数，用 `≈>` 作内部 hom。
 - 作为对象，数字 `0` 与 `1` 指初始与终对象。
 - 作为范畴，数字 `0` 与 `1` 指 `Cat` 的初始与终对象。
 - 范畴的积可用 `∏` 写出，不必拉入 `Cat` 的笛卡尔定义。
 - 范畴的余积可用 `∐` 写出，不必拉入 `Cat` 的余笛卡尔定义。
 - 函子的积写作 `F ∏⟶ G`，结合积与函子记号；余积同理 `∐⟶`。
 - 两函子的逗号范畴写作 `(F ↓ G)`。
 - 箭头范畴写作 `C⃗`。
 - 切片范畴用 Unicode 斜杠 `C̸c`（普通 `/` 不算运算符）。
 - 余切片范畴用 `c ̸co C`，避免歧义。

## 未来方向 (Future directions)

### 计算求解器 (Computational Solver)

范畴论中有些等价关系很容易陈述与证明，但若在 Coq 里只靠符号重写会很慢。例如：

    (f ∘ g) △ (h ∘ i) ≈ split f h ∘ g △ i

解法是展开 `split`，再重写使 `fork`（此处为 `△`）吸收左侧项，利用复合的结合律，再按积的普遍性质化简。如此反复直到平凡完成。

虽好陈述，也容易写成 tactic，但当相关项的类型很大时会极慢；经验上单次 rewrite 有时要数秒。

该求解器的目标是把上述等价按基本运算具体化（reify），再利用范畴论定律，把等价计算成约化项之间在指标上的等式。这叫**计算反射** (computational reflection)：解只依赖项的范畴结构，不依赖其类型。

构造不当的结构会直接解失败；但我们是对良类型表达式反射以得到交给求解器的结构，再加上求解器的可靠性证明，可知可解且良类型的项总给出正确解。这样把问题转到只有指标、没有类型的域，在那里解结构问题，再靠可靠性证明回到带完整类型的域。

### 编译到范畴 (Compiling to categories)

`Tools/Abstraction` 中已开始把单态 Gallina 函数编译成“范畴论项”，再用 Coq 的类型类实例解析在任意支持的目标范畴中实例化。

这是 Conal Elliott 想法的 Coq 实现（他先在并面向 Haskell 实现）。希望范畴这一媒介能提供一种可靠方式，把 Gallina 项搬到其他句法域，而不依赖 Coq 的 extraction。

## 新手教程 (Beginner tutorials)

本 fork 的 `docs/tutorials/` 提供一套**简体中文**入门教程，教你如何浏览与使用本库（不是范畴论教材）：

- [教程索引](docs/tutorials/INDEX.md)
- 00 [仓库概览与学习路线](docs/tutorials/00-overview.md)
- 01 [环境搭建与编译](docs/tutorials/01-setup.md)
- 02 [第一个证明游走](docs/tutorials/02-first-walk.md)
- 03 [常用结构](docs/tutorials/03-structures.md)
- 04 [伴随与 Monad](docs/tutorials/04-adjunction-monad.md)
- 05 [Instance 实例库](docs/tutorials/05-instances.md)
- 06 [如何扩展](docs/tutorials/06-extending.md)

建议从索引按顺序读；Coq 标识符与 `Require` 路径保持英文。日常请固定同一 Coq 版本（推荐 Platform 8.20），避免混用 `.vo`。

## 许可证 (License)

本库以 BSD-3-Clause 许可提供，副本见 [`LICENSE.md`](LICENSE.md)。可自由用于任何目的（含专有衍生作品），只要在衍生作品中保留许可证副本。回指本仓库的致谢非必需，但非常欢迎。

John Wiegley

---

**中文翻译说明**：本分支 `zh-CN` 将文档与注释译为简体中文，便于阅读；Coq 标识符、模块名、`Require` 路径与 API 名称保持英文不变。
