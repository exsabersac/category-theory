# 04 · 伴随、Monad、阅读路径

先抓住 **Theory 里的定义**，再按需下到 `Adjunction/`、`Monad/` 子树。

## 伴随：`Theory/Adjunction.v`

本库默认用 **hom-set 形式**（Kan）：左伴随 `F : D ⟶ C`、右伴随 `U : C ⟶ D`，

```coq
Class Adjunction := {
  adj {x y} :
    (* (F x ~> y)  ≊  (x ~> U y)   在 Sets 里作为 setoid 同构 *)
    @Isomorphism Sets {| carrier := hom (F x) y; … |}
                 {| carrier := hom x (U y); … |};
  to_adj_nat_l … ; to_adj_nat_r … ;
  from_adj_nat_l … ; from_adj_nat_r …
}.
```

转置记号：`⌊f⌋` = `to adj f`，`⌈f⌉` = `from adj f`。  
单位 / 余单位是恒等的转置；三角恒等式在文件中作为推论出现。

注意：该文件 `Require Import Category.Instance.Sets`，因为 hom 集同构住在 `Sets` 里。

### 还有哪些「伴随的写法」

| 路径 | 内容 |
|------|------|
| `Adjunction/Natural/Transformation.v` | 单位–余单位（`Adjunction_Transform`） |
| `Adjunction/Natural/Transformation/Universal.v` | 与 hom 形式互译 |
| `Adjunction/Diagonal/Product.v` 等 | 对角 ⊣ 积 等具体伴随 |
| `Adjunction/Continuity.v` | 右伴随保极限等 |
| `Adjunction/GAFT.v`、`SAFT.v` | 一般 / 特殊伴随函子定理 |
| `Adjunction/README.md` | 子树导读 |

记号：`F ⊣ U`（见 README 记号节）。

## 单子：`Theory/Monad.v`

自函子 `M : C ⟶ C` 上的 join/return 呈现：

```coq
Class Monad := {
  ret  {x} : x ~> M x;           (* η *)
  join {x} : M (M x) ~> M x;     (* μ *)
  fmap_ret … ;                   (* η 的自然性 *)
  join_fmap_join … ;             (* 结合律 *)
  join_fmap_ret … ; join_ret … ; (* 单位律 *)
  join_fmap_fmap …               (* μ 的自然性 *)
}.
```

`bind` 定义为 `join ∘ fmap f`，并带 Haskell 风格记号 `>>=`（在 morphism scope）。

余单子不对偶重写一遍，而是：

```coq
(* 概念上：Comonad := Monad 在 C^op 上对 M^op *)
```

实现细节见 `Theory/Monad.v` 末尾与 `Comonad/`。

## 伴随 → 单子

经典事实：每个伴随给出自函子上的单子。库中对应：

- `Monad/Adjunction.v`（文首注释里的 `Adjunction_Monad`）
- 反过来：Kleisli / Eilenberg–Moore 分解在 `Monad/Kleisli/`、`Monad/Eilenberg/`、`Monad/Algebra.v`
- Beck 单子性：`Monad/Monadicity/`

## 建议阅读路径

```
Theory/Adjunction.v
    ├─（可选）Adjunction/Natural/Transformation.v
    ├─ Adjunction/Diagonal/Product.v   (* 具体例子 *)
    └─ Monad/Adjunction.v              (* 伴随诱导单子 *)
         ↓
Theory/Monad.v
    ├─ Monad/Kleisli.v
    ├─ Monad/Algebra.v
    └─ 需要再进 Monadicity / Strong / …
```

程序员向的 Coq 应用层在 `Theory/Coq/`（把一般结构连到 Gallina）；那是另一条线，等核心 Theory 走顺再进。

## 阅读时盯住的三件事

1. **谁是左、谁是右**：`F` 与 `U` 的方向写在 `Context` 里，看错方向后面全拧。
2. **相等仍是 `≈`**：自然性、三角、单子律全部在 setoid 上。
3. **定义分散是故意的**：`Theory/` 给最薄核心；定理与「种」进同名顶层目录，避免一个文件爆炸。

下一篇：[05 Instance 实例库](05-instances.md)
