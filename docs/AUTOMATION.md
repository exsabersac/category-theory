# Tactic 与 hint 数据库参考

本库导出证明自动化的一页契约。下游项目可依赖下列名称与行为在非主版本间保持稳定；未列出的内容视为库内部实现，可能不经通知变更。

## Tactics

多数 tactic 在 `Lib/Tactics.v`（由 `Require Import Category.Lib.` 传递加载；该导入本身是每个库文件的首个 import）。

**例外：** `Ltac normal` 定义在 `Functor/Bifunctor.v`，**不在** `Lib/Tactics.v`。若在自己代码中使用 `normal`，需显式 `Require Import Category.Functor.Bifunctor.`。

| Tactic        | 元数      | 用途                                                       | 关闭 / 推进        | 稳定性     |
|---------------|------------|---------------------------------------------------------------|----------------------------|---------------|
| `cat`         | 无参     | 范畴定律目标的标准化简：`simplify` + `autorewrite with categories` + `auto with category_laws` + `try reflexivity`。 | 多数态射层上的等词 `≈` 目标。 | 稳定        |
| `cat_simpl`   | 无参     | 更激进：`program_simpl`、`autounfold`，再分派到 `equivalence` / `proper` / `respectful` 消解，最后 `cat`。作为全库默认 `Obligation Tactic`。 | 所有标准 `Program` obligation。 | 稳定        |
| `proper`      | 无参     | 消解 `Proper _ _` 目标。`repeat intro; simpl; try cat; intuition`。 | 多数 `Proper`/`respectful` 实例。 | 稳定        |
| `equivalence` | 无参     | 消解 `Equivalence` 目标。`constructor; repeat intro; simpl; try cat; intuition; try solve [reflexivity \| (symmetry; eassumption)]; auto with category_laws`。显式 reflexivity/symmetry 与末尾窄数据库是刻意的：用宽 `auto with *` 触达无模式的 stdlib hint（`solve_crelation`）在已发布 Rocq 上能关这两条定律，在 Rocq master 上不行（issue #213）。 | 多数 setoid `Equivalence` 证明。 | 稳定        |
| `construct`   | 无参     | `unshelve econstructor; simpl; intros` — 构造 record 值，每个字段留作子目标。 | Record 引入步骤。 | 稳定        |
| `normal`      | 无参     | 把复合链规范成左结合形式，用 `comp_assoc` 的正向。（注意：与下方 `categories` rewrite DB 相反，后者规范成右结合。）定义在 `Functor/Bifunctor.v`（非 `Lib/Tactics.v`）。 | 复合规范化。 | 稳定        |
| `simplify`    | 无参     | 库在 `cat` / `cat_simpl` 内使用的结构 tactic 前奏。 | Match 与拆分目标。    | 内部*     |
| `inv`         | 假设 | `inversion H; subst; try clear H`。                            | 假设销毁。     | 稳定        |
| `spose F as X` | 项 + 标识符 | `pose proof F as X; simpl in X` — 把 `F` 以化简后形式放入上下文。 | 引理实例化步骤。   | 稳定        |
| `sapply F`    | 项       | Cb 化简后的 `apply F`。                                       | 引理应用。          | 稳定        |
| `srewrite F`  | 项       | Cb 化简后的 `rewrite F`。                                     | 引理驱动的 rewrite。       | 稳定        |
| `srewrite_r F` | 项      | Cb 化简后的 `rewrite <- F`。                                  | 反向 rewrite。  | 稳定        |
| `isomorphism` | 无参     | `_ ≅ _` 目标求解器（见 `Theory/Isomorphism.v`）。         | 同构构造。           | 稳定        |

`*`「内部」表示我们保持 API 可用，但下游应优先用更高层包装 `cat` / `cat_simpl`。

## Hint 数据库

| 数据库         | 内容                                                                                          | 定义于                              |
|------------------|---------------------------------------------------------------------------------------------------|------------------------------------------|
| `categories`     | 范畴定律 rewrite：`id_left`、`id_right`、`comp_assoc`（仅右结合方向以规范化；正向会循环）、`fmap_id` 等。 | `Theory/Category.v`、`Lib/Tactics2.v`   |
| `category_laws`  | 针对 `Reflexive`/`Symmetric`/`Transitive`/`Proper`/`equiv` 的 `Hint Extern`。              | `Lib/Tactics.v`                          |
| `core`           | 标准 Coq + 库为 `Equivalence`/`Proper`/`Reflexive`/`Symmetric`/`Transitive` 安装的扩展。 | `Lib/Tactics.v`（经由 `Hint Extern 1`）。 |

`cat` 与 `cat_simpl` 都会查阅 `categories`（经 `autorewrite`）与 `category_laws`（经 `auto`）。

## 推荐的下游约定

若依赖本库并想加自己的自动化：

1. **不要污染 `categories`。** 留给库的范畴定律恒等式。用自己前缀的数据库（`mylib_kernels`、`mylib_rewrite_specs` 等）。
2. **包装而非替换 `cat` / `cat_simpl`。** 下游 `solve_mylib` 通常应以 `; cat` 或 `; cat_simpl` 结尾，落到库的原始自动化。
3. **不要对抗库的 `Obligation Tactic`。** 库在 `Lib/Tactics.v` 设 `#[global] Obligation Tactic := cat_simpl.`。在自己文件里若需不同默认，用 `#[local] Obligation Tactic := …` — 绝不要 `#[global]`。
4. **在类型类上下文很重的文件里避免 `Set Default Proof Using "All"`。** 这会迫使每个证明项捕获作用域内全部 section 变量，证明项巨大，并可能在类型类密集代码（如触及 `Hypergraph` 的）中触发内存爆炸。改用逐证明的 `Proof using ...`，只列最少 section 变量。（注意 `"Type*"` **不是**解药：它仍会捕获 tactic 步骤碰到的每个类型相关 section 变量，在类型类密集代码里几乎等于全部。）

   **已知例外：** 目前七个文件使用 `Set Default Proof Using "All"` — 五个
   `Construction/DecoratedCospan/{Category,Symmetric,Monoidal,
   Braided,Hypergraph}.v`（各带 11 变量 `Context` 块），以及 `Construction/Localization/Universal.v` 与
   `Construction/Reflective/Idempotent.v`。逐证明 `Proof using` 重构可行但繁琐；当前每文件内存开销约 7 GB，对库的 CI 预算勉强可接受。
   同类新文件**不要**跟这个模式 — 从一开始就用逐证明 `Proof using`。
5. **优先扁平投影，避免深嵌套。** 用 `scfa_mu (scfa X)`，不要 `@mu _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _
   (@scfa_commutative _ _ _ (scfa X))))`。提供扁平投影正是为了让目标状态可读。

## `cat` **不会**做的事

- 需要非平凡范畴结构推理的目标（如 Frobenius、hypergraph 特有的 spider 定律）。那些请直接用 `Structure/Monoidal/Hypergraph/Spider.v` 中的引理。
- 超出 `categories` 已注册范围的幺半连贯性（associator / unitor）消去。对严格幺半约化，目前仍是手工步骤。
- 代数藏在不透明 `Program` 生成的 `existT` 包装后的目标 — 先用 `cbn` 或 `simpl` 展开。

## 拿不准时

`cat_simpl` 是库导出的最高功率关闭器。若 `cat_simpl` 无进展，下一步试手动 `spose` 相关引理，再跟一小段 `rewrite` 链。

## 稳定性承诺

上表 tactic 在本库未来所有发布中将以相同表面语法继续存在。其*实现*可能加强（我们可能让 `cat` 更聪明）；不会删除或改名。若将来有 tactic 取代其中之一，旧名会成为新 tactic 的 `Tactic Notation` 别名。
