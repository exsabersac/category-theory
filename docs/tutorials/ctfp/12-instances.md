# 12 · Sets / Cat / Coq 实例落地

**CTFP / DaoFP**：无「Coq 库」专章；落地靠具体范畴。本篇讲 `Instance/` 与 `Theory/Coq/`。

## 1. 为何读实例

抽象字段变成可计算/可证对象：`≈` 比什么、`fmap` 是哪段函数。

| 路径 | 内容 |
|------|------|
| `Instance/Sets.v` | setoid 对象的「集合」范畴精神 |
| `Instance/Cat.v` | 范畴的范畴 |
| `Instance/Coq*` / `Theory/Coq*` | Gallina 编程结构 |
| `Instance/FinSet/` | 有限集；接 Lawvere |

## 2. Sets 走读（CoqIDE）

1. `Category` 实例：`obj`/`hom`/`equiv`（常点点）。  
2. `Sets_Terminal` / `Initial`：`one_unique` 如何「算」出来。  
3. 积 / 幺半实例：对照 [02](02-products.md)、[10](10-monoidal-kan-ends.md)。  
4. 设计目标：尽量不靠函数外延公理。

抽象证明写 `apply one_unique`；实例证明写点点相等——体会分层。

## 3. Cat 走读

对象=范畴，态射=函子；`≈` 可能是自然同构级（以源码为准）。E-category 再次关键。

## 4. Coq / Theory.Coq

选 `option`/`list`：看 `fmap`/`ret`/`join`，跟 Monad 义务如何 `simpl` 关掉。

## 5. 闭合检查表

| 概念 | 在 Sets 上指认 |
|------|----------------|
| 终/积/指数 | `()` / 笛卡尔积 / 函数 |
| 函子/Monad | 容器 map / option·list |
| 自然变换 | 多态分量 |

## 6. 综合练习（box）

1. `Require Import Category.Instance.Sets.` 试 `1`、`×`。  
2. 重放 `terminal_unique` 理解。  
3. option 的 `join_ret` 自写 `simpl` 证明。  
4. 默写 01–11 的 Class 名打勾。  

工作流：box 改→推 GitHub→本机 pull；**不用 Cursor 云端 agent**。



## 8. Sets 深走读脚本

打开 `Instance/Sets.v`，按序打勾：

1. [ ] `SetoidObject` / carrier / 相等如何定义。  
2. [ ] `Category` 实例的 `compose` / `id`。  
3. [ ] `compose_respects` 证明策略（proper? 点点?）。  
4. [ ] `Sets_Terminal`：`terminal_obj` 是什么；`one`；`one_unique` Proof 全文读懂。  
5. [ ] `Sets_Initial` 对偶。  
6. [ ] 积或 Monoidal 实例：`fork`/`exl` 是否真是 pair 投影。  
7. [ ] （若有）指数 / CCC 片段。  
8. [ ] 任取一 Corollary 在 Sets 上特化，对比抽象证明长度。

## 9. Cat 深走读脚本

1. [ ] 对象类型 = `Category`？  
2. [ ] 态射 = `Functor`？  
3. [ ] 相等 = 自然同构还是点点？  
4. [ ] 恒等 = Id 函子；复合 = 函子复合。  
5. [ ] 任一条定律义务：是否回到 [04](04-functor.md)/[05](05-natural.md)。

## 10. Coq 编程线脚本

1. [ ] `Theory/Coq/Functor.v` 的 `fmap`。  
2. [ ] `Theory/Coq/Monad.v` 的 `ret`/`bind` 或 `join`。  
3. [ ] `Instance/Coq/` 下一个具体类型。  
4. [ ] 把该实例的 `join_fmap_ret` 逐步证明贴进笔记（自写，不抄库外书）。

## 11. 全系列验收（给自己打分）

对每个概念：口头定义 / 本库 Class 名 / Sets 上例子 / 一个证明字段 —— 四项全能算过关。

| 概念 | 口 | Class | Sets例 | 字段 |
|------|----|-------|--------|------|
| 范畴 | | Category | | id_left |
| 积 | | Cartesian | | ump_products |
| 指数 | | Closed | | ump_exponents |
| 函子 | | Functor | | fmap_comp |
| 自然变换 | | Transform | | naturality |
| 极限 | | Limit | | ump_limits |
| Yoneda | | Yoneda_Lemma | | to/from |
| 伴随 | | Adjunction | | adj |
| Monad | | Monad | | join_ret |
| EM | | TAlgebra | | t_id |
| Kan | | LocalRightKan | | ump_ran |
| Lawvere | | LawvereTheory | | law_of_nat |


## 7. 系列之后

缺口：Applicative、Comonad、Ends→Optics。导航：[../INDEX.md](../INDEX.md)。
