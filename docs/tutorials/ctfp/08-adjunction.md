# 08 · 伴随

**CTFP**：3.2 *Adjunctions*；3.3 *Free/Forgetful Adjunctions*。  
**DaoFP**：`10-Adjunctions`（柯里化、对角与积/余积、单位/余单位、三角恒等式、极限作为伴随）。

> 原创教学复述；不摘录书中正文。

## 1. 书侧故事：三种面孔

伴随 `F ⊣ U` 常有三种等价包装：

1. **Hom 自然同构**：`C(F x, y) ≅ D(x, U y)`；  
2. **单位 / 余单位** `η : Id ⟹ U F`，`ε : F U ⟹ Id` + 三角恒等式；  
3. **普遍箭头**：自由对象视角。

CTFP 主例：自由—遗忘（列表/幺半群等）与（在 CCC 里）柯里化。DaoFP 把对角函子与积/余积、极限的伴随说法排成谱系。笔记 [Kan扩展/左伴随作为右Kan](https://github.com/exsabersac/haskell-algebra-notes/tree/main/docs/Kan%E6%89%A9%E5%B1%95) 给出更高观点——本篇先钉 Hom 定义。

## 2. 编程直觉

```text
自由 ⊣ 遗忘：生成元／语法  vs  忘结构
柯里化：      (− × y) ⊣ (−)^y
η ~ return/pure 放入；ε ~ 求值/折叠
```

## 3. 本库：`Theory/Adjunction.v`

```coq
Class Adjunction := {
  adj {x y} : Isomorphism Sets (hom (F x) y) (hom x (U y))
    where "⌊ f ⌋" := (to adj f) and "⌈ f ⌉" := (from adj f);

  to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) :
    ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) :
    ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;
  from_adj_nat_l ... ;
  from_adj_nat_r ...
}.
```

`Build_Adjunction'`：只交 `adj` + 两个 `to_adj_nat_*`，另两向由同构单性推出。  
目录 `Adjunction/`：变体与定理（Hom、Compose、FullFaithful、Representability…）。

## 4. CoqIDE 证明走读

### 4.1 记号

`f : F x ~> y` 时 `⌊f⌋ : x ~> U y`。先看类型再点战术。

### 4.2 跟 `Build_Adjunction'`

1. `unshelve eapply Build_Adjunction`；  
2. 填 `to_adj_nat_*`；  
3. `from_adj_nat_*`：设 `f' := from (adj …) f`，用 `injectivity_is_monic`，`rewrite iso_to_from`、`to_adj_nat_l` 等。  

逐步跟完是本课最有价值的 IDE 练习。

### 4.3 造 η / ε

精神：`η_x := ⌊id[F x]⌋`，`ε_y := ⌈id[U y]⌉`。  
自然性 Goal 化成 `*_nat_*` 的特例。三角恒等式：

```text
ε_{F x} ∘ fmap[F] η_x ≈ id
fmap[U] ε_y ∘ η_{U y} ≈ id
```

若库已定义 `unit`/`counit`，跟证明；否则 Scratch 自写一条。

### 4.4 自由—遗忘实例

在 `Instance/` 或 `Adjunction/` 搜 Free/Forgetful：看 `adj` 如何对「插入生成元」编码。对照 CTFP 3.3 故事，义务以字段为准。

### 4.5 积与对角

DaoFP：`Δ ⊣ (−×−)`（精神）。若本库有实例，对照 `fork`；若无，用 `Cartesian` 自证 Hom 级双射作练习。

## 5. 易混对比

| 说法 | 澄清 |
|------|------|
| 左伴随保极限 | 错；左保**余**极限，右保极限 |
| 有 η、ε 即伴随 | 还需三角（或等价 Hom 自然同构） |
| ⌊⌋ 方向 | 以 `to`/`from` 类型为准 |
| 伴随唯一 | 自然同构下唯一 |

## 6. CoqIDE 检查清单

1. [ ] 解释 `adj` 与 ⌊⌋/⌈⌉。  
2. [ ] 读四条自然性。  
3. [ ] 跟完 `Build_Adjunction'`。  
4. [ ] η/ε 定义或自造。  
5. [ ] 扫 `Adjunction/` 目录。  
6. [ ] （可选）笔记「左伴随作为右Kan」标题级对照。



## 7. 更细的 CoqIDE 会话：Build_Adjunction'

1. 打开 `Theory/Adjunction.v`，跳到 `Build_Adjunction'`。  
2. 逐步进入 Proof。  
3. 第一个 `from_adj_nat_*` Goal 出现时暂停，写下：  
   - 当前已知？  
   - 要用 `to` 的单性转到哪条已证自然性？  
4. 观察 `iso_to_from` 如何消去 `to∘from`。  
5. 全部结束后，不看屏幕默写四条 `*_nat_*` 的类型。

## 8. 三角恒等式纸上作业

不打开文件，画两条：

```text
F  --Fη-->  FUF  --εF-->  F
U  --ηU-->  UFU  --Uε-->  U
```

标成分为 `≈ id`。然后再到源码搜 `triangle` / `counit` / `unit` 验证自己的记号是否与库一致（允许不一致，以库为准改正）。

## 9. 书侧对照

| CTFP/DaoFP 主题 | 本课 |
|-----------------|------|
| Hom 定义 | §3 |
| 自由遗忘 | §4.4 |
| 柯里化伴随 | 接 [03](03-closed.md) |
| 单位余单位 | §4.3 |
| 极限作伴随 | 接 [06](06-limits.md) |
| 左伴随与 Kan | 笔记 + [10](10-monoidal-kan-ends.md) |


下一篇：[09 Monad 与代数](09-monad-algebra.md)
