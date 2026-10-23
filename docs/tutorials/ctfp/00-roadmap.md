# 00 · 路线图：这套教程在干什么

**CTFP / DaoFP**：概念与编程直觉的来源（只引章节号/标题，不抄正文）。  
**本库**：[exsabersac/category-theory](https://github.com/exsabersac/category-theory)（上游 jwiegley）。  
**Haskell 笔记**：[haskell-algebra-notes](https://github.com/exsabersac/haskell-algebra-notes)。

## 先说结论

CTFP 教你用「对象 + 箭头 + 复合」想问题；DaoFP 用可运行的 Haskell / Agda 味草稿把同一套词条写一遍。本库做第三件事：**把这些词条变成 Coq 的 typeclass，每条定律都是可检查的证明义务**。

读完 01–12，你应能：

1. 听到「积 / 函子 / 自然变换 / 伴随 / Monad」时，立刻对应到本库哪个 `Class`、哪几个字段；
2. 在 CoqIDE 里打开对应 `.v`，看懂 Goal 里 `≈` 在比什么，知道该 `rewrite` 哪个字段、何时丢给 `cat`；
3. 分清易混概念（**EM 代数 ≠ F-代数**、**极限锥 ≠ 任意锥**、**闭范畴草稿 ≠ CCC**）。

## 两本书各自贡献什么（不替代原书）

| 来源 | 你该用它补什么 | 本教程怎么用 |
|------|----------------|--------------|
| CTFP Part 1（1.1–1.10） | 复合动机、类型≈对象、积/余积、函子、自然变换、函数类型 | 01–05 的「故事」骨架 |
| CTFP Part 2–3 | 极限、Yoneda、伴随、Monad、F-代数、End/Kan、Lawvere | 06–11 |
| DaoFP §1–9 | 从空白板到自然变换：引入/消去规则、对偶、可表 | 与 CTFP 交叉印证，例子更「类型论」 |
| DaoFP §10–20 | 伴随、代数/余代数、效果、Applicative、Monad、End、Kan | 08–11 加厚；Applicative/Comonad 标为缺口 |
| 你的笔记 | 初始代数、Free、Kan、Lawvere、幺半、Optics | 篇末链接；机制与 Demo 对照 |

若某概念在两本书里切入角度不同（例如 Monad：程序员 `>>=` vs 范畴 `η/μ`），教程会**两者都讲**，再落到本库选的编码。

## 本库设计的三块拼图

### 1. E-category：hom 是 setoid

Coq 默认相等是 Leibniz `=`，函数外延与商类型都不免费。本库选择：每个 `hom X Y` 自带等价关系 `≈`（字段 `homset`），复合必须 `Proper`（`compose_respects`）。这叫 **E-category**（充实到 setoid 上的范畴）。

你处处会碰到：

- 重写态射用 **setoid rewriting**（`rewrite` 在 `≈` 上），不是只靠 `=`；
- 定义任何「在态射上的运算」都要交 `Proper` 证明——`Program` + 默认 `Obligation Tactic`（`cat_simpl`）常能帮你消；
- 好处：`Instance/Sets.v` 可以**不靠函数外延公理**——两个函数点点相等即可视为同一态射。

### 2. Typeclass 字典：概念 = `Class` + 定律字段

| 口头说法 | 库里落点 | 典型「数据」 | 典型「定律」 |
|----------|----------|--------------|--------------|
| 范畴 | `Theory.Category.Category` | `obj`,`hom`,`id`,`compose` | `id_left`,`comp_assoc`,`compose_respects` |
| 函子 | `Theory.Functor.Functor` | `fobj`,`fmap` | `fmap_id`,`fmap_comp`,`fmap_respects` |
| 自然变换 | `Natural.Transformation.Transform` | `transform` | `naturality`（及 `_sym`） |
| 伴随 | `Theory.Adjunction.Adjunction` | `adj`（hom-setoid 同构） | 四条自然性 |
| 单子 | `Theory.Monad.Monad` | `ret`,`join` | 单位/结合 + 自然性 |
| 终/积/指数 | `Structure.*` | 对象 + 中介态射 | `*_unique` / `ump_*` |

证明时 Goal 几乎总是某个 `≈`。**先认字段名，再谈战术。**

### 3. 目录分工

```
Theory/        核心定义（Category, Functor, Monad, Adjunction, Kan, Lawvere…）
Structure/     范畴上「有某种结构」（Terminal, Cartesian, Limit, Monoidal…）
Construction/  从旧范畴造新范畴（Opposite, Product, Free, FAlg…）
Functor/       函子的种与特例（Hom, Yoneda, Applicative…）
Adjunction/    伴随的变体与定理
Monad/         Kleisli、EM、与伴随的互化
Instance/      具体范畴（Sets, Cat, Coq, FinSet…）
```

```coq
Require Import Category.Theory.          (* 汇入常用 Theory *)
Require Import Category.Theory.Category. (* 或精确导入 *)
Require Import Category.Theory.Functor.
```

`_CoqProject` 必须有 `-R . Category`（或等价 `-Q`）。

## 证明习惯（全教程通用）

1. **看 Goal 的形状**：是 `f ≈ g`、还是 `Proper ...`、还是同构的两个方向？
2. **优先用定义里的字段**：`id_left`、`ump_products`、`naturality`、`to_adj_nat_l`……这些是「概念本身」，比瞎 `auto` 有教学价值。
3. **再考虑库战术**：
   - `cat`：标准化简 + `autorewrite with categories` + `auto with category_laws`；
   - `cat_simpl`：更激进，常作 `Program` 的 Obligation Tactic；
   - `proper` / `equivalence`：专门消 `Proper` / `Equivalence`。
4. **`Program Definition` / `Program Instance`**：义务出现在 *Obligations* 面板；用 `Next Obligation` 逐个看，不要一次 `Admit`。
5. **对偶技巧**：余×× 常是 `C^op` 里的 ××；看 `Construction/Opposite.v` 如何对调 `comp_assoc` / `comp_assoc_sym`。

### 迷你示例：`one_comp`（终对象）

`Structure/Terminal.v` 里有：

```coq
Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.
```

**Goal 起初**：`one ∘ f ≈ one`（两边都是 `x ~> 1`）。  
**一步**：`apply one_unique`——终对象的 UMP 说「进到 `1` 的任意两条箭头 `≈`」。  
不需要展开 `one` 的具体定义。这就是「用字段说话」的范例；后面积、伴随、Yoneda 同一套路。

## CTFP 进度 ↔ 本教程

| CTFP 大致位置（标题） | 打开 |
|----------------------|------|
| 1.1–1.3 Composition / Types / Great and Small | [01](01-category.md) |
| 1.5–1.6 Products / ADTs | [02](02-products.md) |
| 1.9 Function Types | [03](03-closed.md) |
| 1.7–1.8 Functors / Functoriality | [04](04-functor.md) |
| 1.10 Natural Transformations | [05](05-natural.md) |
| 2.2 Limits and Colimits | [06](06-limits.md) |
| 2.4–2.6 Representable / Yoneda | [07](07-yoneda.md) |
| 3.2–3.3 Adjunctions / Free-Forgetful | [08](08-adjunction.md) |
| 1.4 Kleisli；3.4–3.6、3.8–3.9 Monad / F-Alg / EM | [09](09-monad-algebra.md) |
| 3.10–3.12、3.15 Ends / Kan / Monoidal | [10](10-monoidal-kan-ends.md) |
| 3.14 Lawvere；2.3 Free Monoids；代数侧 | [11](11-lawvere-free.md) |
| 想看 Sets/Cat/Coq 实例 | [12](12-instances.md) |

## CoqIDE / VsCoq 起步（30 秒）

1. 打开仓库根，确认 `_CoqProject` 含 `-R . Category`。
2. 固定 **Coq Platform 8.20**（与 `.vo` 一致；不要混 brew 9.3）。
3. 打开 `Theory/Category.v`，跳过文首长注释，停在 `Class Category`，逐步向下解释。
4. Goal 窗口里看到 `≈`，就明白：你在证 setoid 相等。
5. 打开 `docs/AUTOMATION.md` 扫一眼 `cat` 会做什么、**不会**做什么。

下一篇：[01 范畴与态射](01-category.md)
