# 06 · 如何扩展：写自己的 Instance 或引理

你要加的是「又一个具体范畴 / 又一个结构实例 / 几条引理」，按现有分层放，别改标识符风格去迁就中文。

## 放哪里

| 你要加的东西 | 建议位置 |
|--------------|----------|
| 新的具体范畴 | `Instance/YourName.v`（或合适子目录） |
| 某范畴上的 Terminal / Cartesian / … | 紧跟该 Instance 文件，或 `Instance/…` 子模块 |
| 对任意范畴成立的引理 | 靠近定义：`Theory/`、`Structure/`、`Adjunction/`… |
| 造新范畴的通用构造 | `Construction/` |
| 仅局部试验 | 自己的 scratch，或 fork 上单独分支；确认后再迁入 |

文件头通常：

```coq
Require Import Category.Lib.
Require Import Category.Theory.Category.
(* 再按需 Theory.Functor / Structure.Terminal / … *)

Generalizable All Variables.
```

## 命名与风格（跟邻居学）

- **类型类 / 定义**：英文，Pascal 或库内既有拼写（`Terminal`、`fmap_comp`、`Sets_Terminal`）。
- **实例**：`CategoryName_Structure`，例如 `Sets_Terminal`、`Sets_Initial`。
- **不要重命名**上游已有标识符；中文只写在注释里。
- 态射证明目标用 `≈`；需要时证明 `Proper` / 用 `compose_respects`、`fmap_respects`。
- 宇宙：核心定义多是 `{o h p}`；具体代数范畴有时要手工钉宇宙（见 `CLAUDE.md` / `Structure/Complete.v` 文首）。新手先抄同目录相似实例的宇宙写法。

## 最小「新范畴」骨架

```coq
Require Import Category.Lib.
Require Import Category.Theory.Category.

(* 1. 准备对象类型、hom、Setoid 实例 *)
(* 2. 给出 id、compose，证明定律 *)

Program Definition MyCat : Category := {|
  obj     := …;
  hom     := …;
  homset  := …;
  id      := …;
  compose := …;
  compose_respects := …;
  (* id_left / id_right / comp_assoc / comp_assoc_sym
     常由 Program 义务或手写证明填 *)
|}.
```

若义务成对出现，记得库偏好 **同时留下 `comp_assoc_sym`**（或使用 `Build_Category'` 一类辅助），以便对偶顺利。

有终对象时再：

```coq
Program Instance MyCat_Terminal : @Terminal MyCat := {|
  terminal_obj := …;
  one := …;
  one_unique := …
|}.
```

## `_CoqProject` 与编译

- 新文件若要进官方构建集，需加入根目录 `_CoqProject`（上游用很长的文件列表）。个人实验可以暂时只靠：

  ```bash
  coqc -R . Category Instance/MyCat.v
  ```

- 提交前在**同一 Coq 版本**下编过；不要提交「用 9.x 编、别人 8.20 打不开」的 `.vo`（`.vo` 一般本就不该进 git；本库 `.gitignore` 已忽略构建产物）。

## 证明习惯

1. 先 `Search` 已有引理（`one_unique`、`ump_products`、`fmap_comp`…）。
2. 范畴等式优先试 `cat` / `cat_simpl`（`Lib/Tactics.v`），再手写 `rewrite`。
3. 目标里出现 `Proper`、`respectful` 时，想想哪一层忘了 `≈` 的尊重性。
4. 大定理写成「在 … 结构假设下的条件句」，具体模型放 `Instance/`——与 `docs/INHABITATION.md` 的分层一致。

## 文档与分支

- 注释用简体可以，但保持与邻居文件同样的「文首动机 + nLab 链接」风格更佳。
- 本教程所在分支：`docs/beginner-tutorials`；中文翻译主干：`zh-CN`。改文档与改证明分开提交更清晰。

## 做完自检

- [ ] `Require` 路径都以 `Category.` 开头  
- [ ] 没有引入与 Platform 8.20 / 你声明版本不符的语法  
- [ ] 实例名不与现有 `Sets_` / `Cat_` 冲突  
- [ ] 若触及公理，在注释或 `docs/AXIOMS.md` 意识下说明  

回到索引：[INDEX.md](INDEX.md)
