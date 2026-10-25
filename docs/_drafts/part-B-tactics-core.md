# Part B：核心战术（小白导读草稿）

> 仓库：`category-theory`，分支：`docs/coq-commands-guide`  
> 本篇只讲**证明过程中常用的核心战术**（intros / rewrite / apply / destruct …）。  
> 示例优先取自 `Theory/Category.v`、`Theory/Functor.v`、`Theory/Isomorphism.v`、`Lib/Tactics.v`，并夹少量 `Structure/*` 短片段。  
> **未改任何 `.v` 文件**；本文件为草稿，未提交。

## 阅读前：本库里的「相等」≈ setoid

本库的同态相等几乎一律是 **setoid 等价** `≈`（`Lib/Setoid.v` 的 `equiv`），不是 Coq 内建的 `=`。

- `rewrite` / `rewrite <-`：在本库里**通常也能**改写 `≈`，因为 `≈` 配了 `Equivalence` / `Proper` 实例（见 `Lib/Tactics.v` 里的 hint、`proper` / `equivalence` 战术）。
- `setoid_rewrite`：更「显式」地走 generalized rewriting；在复杂上下文、需要 `at n` 定点、或普通 `rewrite` 卡在 `Proper` 时用（见 `Theory/Bicategory/Pseudofunctor.v`）。
- 库封装：`srewrite` / `srewrite_r` / `sapply`（`Lib/Tactics.v`）先把引理 `pose proof` 出来、`cbn` 再 rewrite/apply，方便处理带投影的 setoid 引理。

---

### `intros` / `intro`

**做什么**  
把目标里最外层的 `∀` / `→`（以及部分 `∀` 式依赖积）**引入假设上下文**。`intro` 一次引入一个（可命名）；`intros` 可一次引入多个，也可带模式。

**常见语法**
```coq
intro.                 (* 自动起名 *)
intro H.               (* 命名为 H *)
intros.                (* 尽量引入全部 *)
intros x y H.          (* 依次命名 *)
intros [H _].          (* 引入后立刻按构造子拆开 *)
intros ? ?.            (* 用 ? 表示「随便起名」 *)
repeat intro.          (* 反复 intro，常见于 Proper/Equivalence 义务 *)
```

**何时用 / 何时别用**  
- **用**：Proof 一开头把量词/蕴含变成假设；配合 `constructor; repeat intro` 证 `Proper` / `Equivalence`。  
- **别用**：目标其实该 `apply`/`refine` 填构造子时，不要先盲目 `intros` 把结构拆乱；已有同名假设时注意命名冲突。

**仓库示例**
```coq
(* Theory/Category.v — id_unique_left *)
Proof. intro H; rewrite <- (id_left u); apply H. Qed.

(* Theory/Category.v — id_unique：引入后立刻拆合取 *)
Proof. intros [H _]; now apply id_unique_left. Qed.

(* Lib/Setoid.v — Equivalence 义务里常见写法 *)
constructor; repeat intro.
```

**易混点**  
- `intro` vs `intros`：功能同类；`intros` 更常写、可带复杂模式。  
- `intros.`（无参数）会一直引入到「不能再引」；想只引一部分请显式写名字/模式。  
- `Generalizable All Variables`（本库大量使用）会让许多 `Variables` 自动成隐式，Proof 里看到的 `intros` 往往只处理**显式**前提。

---

### `reflexivity`

**做什么**  
当目标是「某等价关系下自己等于自己」时直接关闭：对 `=` 用 `eq_refl`；对本库的 `≈` 则用 `Equivalence` 的 `Reflexive` 实例。

**常见语法**
```coq
reflexivity.
try reflexivity.       (* 不行就跳过，常见于自动化脚本 *)
```

**何时用 / 何时别用**  
- **用**：两边已经化简成相同形态；或 `rewrite` 系列之后收尾。  
- **别用**：两边只是「看起来像」但差一层定义/`≈` 尚未对齐时——先 `simpl`/`unfold`/`rewrite`，不要空等 `reflexivity`。

**仓库示例**
```coq
(* Theory/Category.v — Build_Category'_Coq *)
intros; try reflexivity.

(* Theory/Category.v — comp_left 战术 *)
apply compose_respects; [reflexivity|].

(* Theory/Functor.v *)
rewrite !comp_assoc.
...
reflexivity.
```

**易混点**  
- 对本库：`reflexivity` 成功往往依赖 `≈` 的 `Reflexive` hint（`Lib/Tactics.v`：`Hint Extern 4 (equiv ?A ?A) => reflexivity`）。  
- 若失败，先检查目标到底是 `=` 还是 `≈`，以及是否缺 `Proper`/`Equivalence` 实例。

---

### `simpl`

**做什么**  
按定义做**计算化简**（δ/ι/ζ/β 等可计算归约），可作用于目标或假设。

**常见语法**
```coq
simpl.                 (* 化简目标 *)
simpl in H.            (* 化简假设 H *)
simpl in *.            (* 目标 + 所有假设 *)
simpl X.               (* 只化简与 X 相关的部分，视版本/用法而定 *)
cbn. / cbn in H.       (* 更可控的现代替代，本库 srewrite 里常用 *)
```

**何时用 / 何时别用**  
- **用**：`destruct` 记录/Σ 类型后投影还「包着」；`Program`/`refine {| ... |}` 后字段义务需要露出定义。  
- **别用**：大目标上盲目 `simpl` 可能把式子胀得不可读；此时优先 `cbn`、定点 `unfold f`，或库里的 `cat`/`cat_simpl`。

**仓库示例**
```coq
(* Theory/Isomorphism.v — to_equiv_implies_iso_equiv *)
destruct f as [tof fromf tofrom_eqf fromto_eqf],
    g as [tog fromg tofrom_eqg fromto_eqg].
simpl in *.

(* Theory/Functor.v — Ltac functor *)
Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).
```

**易混点**  
- `simpl` ≠ `unfold`：前者做可计算归约；后者强制展开指名定义（即使标记为 `Opaque` 也另说）。  
- 本库自定义 `simpl_eq`（`Lib/Tactics.v`）专门展开 `eq_rect`/`eq_sym` 等，别和裸 `simpl` 混为一谈。

---

### `rewrite` / `rewrite <-` / `setoid_rewrite`

**做什么**  
用一条「等式/等价」引理，把目标（或假设）里的子项替换成另一边。  
- `rewrite H`：把 `H : LHS ≈ RHS`（或 `=`）中的 **LHS 换成 RHS**（左→右）。  
- `rewrite <- H`：右→左。  
- `setoid_rewrite`：走 setoid/generalized rewriting 通路，支持更细的 `at` 定位，且明确按 `Proper` 形态改写。

**常见语法**
```coq
rewrite H.
rewrite <- H.
rewrite H, H0.              (* 连续多条 *)
rewrite !H.                 (* 尽可能多次 *)
rewrite <- !comp_assoc.     (* 方向 + 多次 *)
rewrite H in Hyp.           (* 改假设 *)
rewrite (comp_assoc f g h). (* 先特化再改 *)
setoid_rewrite H.
setoid_rewrite <- H at 1.   (* 只改第 1 处匹配 *)
```

**何时用 / 何时别用**  
- **用**：目标中已经出现引理左边；范畴律 `id_left`/`comp_assoc`/`iso_to_from` 等链式变形。  
- **别用**：两边类型/setoid 对不上、或缺 `Proper` 时硬 `rewrite` 会报错——先 `apply compose_respects`、补实例，或改用 `setoid_rewrite` / `srewrite`。  
- 需要「先把复杂引理规范化再改」时，优先库封装 `srewrite`/`srewrite_r`（`Lib/Tactics.v`）。

**仓库示例**
```coq
(* Theory/Category.v *)
Proof. intro H; rewrite <- (id_left u); apply H. Qed.

(* Theory/Isomorphism.v — 典型同构计算 *)
rewrite <- (id_right g1).
rewrite <- (id_right g2).
rewrite <- !(iso_from_to iso).
rewrite !comp_assoc.

(* Theory/Bicategory/Pseudofunctor.v — 显式 setoid_rewrite + at *)
setoid_rewrite <- (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F z))) at 1.
...
setoid_rewrite (pfmap_comp (@pf1 _ _ G (pf0 F x) (pf0 F z))) at 1.

(* Lib/Tactics.v — 库封装 *)
Ltac srewrite F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite H; clear H.
```

**易混点**  
- **`rewrite` vs `setoid_rewrite`**：本库多数日常证明直接 `rewrite` 即可（因为 `≈` + `Proper` 齐）；遇到上下文深、`at` 定点、或 `rewrite` 提示缺 morphism 时再用 `setoid_rewrite`。  
- `rewrite !H` 的 `!` 是「尽量多次」，不是逻辑非。  
- `rewrites`（`Theory/Category.v`）是本库自定义 Ltac，会自动把上下文里的 `≈` 假设扫进目标并 `clear`——别和单次 `rewrite` 搞混。

---

### `apply` / `eapply`

**做什么**  
用引理/假设「匹配」当前目标：把目标换成引理的前提（若干子目标）。`eapply` 允许引理里部分参数先留成存在元（evar），稍后再填。

**常见语法**
```coq
apply H.
apply (f x y).
apply H in Hyp.            (* 正向改写假设：Hyp 变成 f 的结论形态 *)
apply H; [tac1|tac2].      (* 多个前提分别处理 *)
eapply H.                  (* 宽松匹配，生成 evar *)
unshelve eapply (_ ; _).   (* 与 Σ/依赖对构造常用 *)
```

**何时用 / 何时别用**  
- **用**：目标**恰好是**某引理结论（可差可推断的隐式参数）；如 `apply compose_respects`、`apply id_left`。  
- **别用**：结论对不上却硬套——应先 `rewrite` 对齐，或改用 `refine`/`assert`。  
- 参数推断不出时用 `eapply`，但要尽快 `exact`/`shelve`/`unshelve` 填元，避免 evar 泄漏。

**仓库示例**
```coq
(* Theory/Category.v *)
apply compose_respects; [reflexivity|].
apply compose_respects; auto : category_laws.

(* Theory/Isomorphism.v *)
apply to_equiv_implies_iso_equiv, iso_from_to.

(* Theory/Functor.v *)
unshelve eapply (_ ; _).
```

**易混点**  
- `apply H in Hyp` 方向是「把 Hyp 推过 H」，不是「用 H 证明目标」。  
- `apply` 失败常见原因：缺 `Proper`、宇宙/隐式参数、或目标其实是 `≈` 而引理是 `=`（或相反）。  
- 本库 `sapply` = `pose proof` + `cbn` + `apply`，专治「投影还没算开」的 setoid 引理。

---

### `exact`

**做什么**  
提供一个**完整项**，其类型必须**定义等价于**当前目标，然后立刻关闭该目标。不做额外搜索/改写。

**常见语法**
```coq
exact t.
exact (iso_compose _ X1).
exact I.                   (* True 的唯一构造子 *)
```

**何时用 / 何时别用**  
- **用**：手里已经有（或拼好）正确类型的项；`refine` 填洞后的收尾；`match`/`Ltac` 分支里给出具体证明项。  
- **别用**：还差一点点改写/化简时——先 `rewrite`/`simpl`，或改用 `apply`（允许剩前提）。

**仓库示例**
```coq
(* Theory/Functor.v *)
exact (fmap[F] (to X) ... ).   (* 字段赋值语境中常见 *)
exact Hfg.
exact (e _ _ _).

(* Theory/Isomorphism.v *)
exact (iso_compose _ X1).

(* Lib/Tactics.v — simplify *)
| [ |- () ] => exact tt
```

**易混点**  
- `exact` vs `assumption`：前者你点名项；后者在上下文里**搜索**同类型假设。  
- `exact` vs `apply`：`apply H` 在 H 仍有前提时会留下子目标；`exact H` 要求 H 已经完整。

---

### `assumption`

**做什么**  
在上下文中查找与目标**可统一**的假设，找到就用来关闭目标（类似对某个 `H` 做 `exact H`）。

**常见语法**
```coq
assumption.
```

**何时用 / 何时别用**  
- **用**：拆开合取/存在后，某一侧子目标已经原样躺在假设里。  
- **别用**：还需要改写才能对齐时——`assumption` **不会** `rewrite`。自动化里更常见 `now assumption` / `trivial` / `auto`。

**仓库示例**
```coq
(* Theory/Isomorphism.v *)
intro eq. split; [ assumption | ].
...
unfold iso_equiv; split; assumption.
```

**易混点**  
- 只认「类型能 unify」的假设，不认「差一次 `symmetry`/`rewrite`」的近亲——那种用 `eassumption` 或先变换。  
- `Lib/Tactics.v` 的 `equivalence` 里用了 `eassumption`，比裸 `assumption` 更宽松。

---

### `destruct`

**做什么**  
按归纳/记录/合取/析取等的构造子**案例拆分**一个项或假设，生成若干子目标（或在上下文中换成字段）。

**常见语法**
```coq
destruct H.
destruct H as [H1 H2].
destruct f as [tof fromf ? ?].
destruct p, q.                 (* 连续拆多个 *)
destruct m as [epic].
destruct H eqn:E.              (* 记住等式 E : 原式 = 某构造子 *)
```

**何时用 / 何时别用**  
- **用**：手里是 `∧`/`*`/`∃`/`sigT`/`Isomorphism` 记录、或枚举/`True`/`False`；想命名字段。  
- **别用**：对递归 inductives 需要归纳假设时用 `induction`；只想反演等式时考虑 `inversion`（本库 `inv` = `inversion; subst; try clear`）。

**仓库示例**
```coq
(* Theory/Isomorphism.v *)
destruct f as [tof fromf tofrom_eqf fromto_eqf],
    g as [tog fromg tofrom_eqg fromto_eqg].
simpl in *.
destruct m as [epic]. apply epic.

(* Theory/Functor.v — 等式证明常用 *)
intros a a' b b' p q t; destruct p, q; reflexivity.
```

**易混点**  
- `destruct` 对 `=` 假设有时会丢「怎么证出来的」信息；需要依赖式相等信息时用 `inversion`/`dependent destruction`（进阶）。  
- `as` 模式个数必须匹配构造子参数，否则报错。

---

### `induction`

**做什么**  
对归纳类型做**结构归纳**：拆案例的同时生成**归纳假设**（IH）。

**常见语法**
```coq
induction n.
induction n as [|n IH].
induction xs as [|x xs IH]; intros ...
induction n eqn:E.
```

**何时用 / 何时别用**  
- **用**：目标对 `nat`/`list`/`Fin` 等归纳数据成立；需要 IH。  
- **别用**：只是拆记录/`∧`——用 `destruct` 更干净，不会冒出无用的 IH。本库核心范畴证明较少直接 `induction`，更多出现在 `Lib/IList.v`、`Lib/NETList.v`、`Lib/Setoid/Propositional.v`。

**仓库示例**
```coq
(* Lib/IList.v *)
generalize dependent As.
induction n; intros.

(* Lib/Setoid/Propositional.v *)
intro xs; induction xs as [|x xs IH]; intros [|y ys] H;
```

**易混点**  
- `induction H` 若 H 是假设，会把 H 清掉并可能**泛化**依赖 H 的假设——常用 `revert`/`generalize dependent` 先整理再归纳。  
- 与 `destruct`：有没有 IH 是核心差别。

---

### `unfold` / `fold`

**做什么**  
- `unfold f`：把定义 `f` 在目标/假设中**展开**成其体。  
- `fold t`：尝试把目标中「已展开成 t 之体」的子项**折回**成记号 `t`（`unfold` 的弱逆）。

**常见语法**
```coq
unfold f.
unfold f in H.
unfold f, g.
unfold transport_r at 1 2.   (* 只展开第 1、2 处 *)
fold (transport_r ...).
```

**何时用 / 何时别用**  
- **用**：定义挡住了 `rewrite`/`apply`；或展开后要展示与另一记号相同再 `fold` 回去保持可读。  
- **别用**：可用 `simpl`/`cbn` 算开时不必强行 `unfold`；乱 `unfold` 会让目标膨胀。

**仓库示例**
```coq
(* Theory/Isomorphism.v *)
unfold iso_equiv; split; assumption.

(* Theory/Functor.v *)
unfold transport_r. rewrite eq_sym_involutive.
fold (transport_r (λ z : obj[D], fobj[y] x1 ~{ D }~> z) (x0 y0)).
...
unfold transport_r at 1 2. rewrite transport_relation_exchange.
```

**易混点**  
- `fold` **不保证**总能折回去（匹配失败则不变）。  
- `Hint Unfold`（`Lib/Tactics.v`）会让 `auto`/`cat_simpl` 自动展开某些定义——交互证明时若「突然展开」，检查 hint。

---

### `assert` / `pose` / `remember`

**做什么**  
在上下文中**引入中间结果**，不直接改目标结构：  
- `assert (H : T).`：先证明子目标 `T`，再得到假设 `H`。  
- `assert (H := t).`：直接用项 `t` 作为证明（不另开子目标）。  
- `pose (x := t).` / `pose proof t as H.`：把项/证明放进上下文（可命名）。  
- `remember t as x.`：引入 `x` 与等式 `Heqx : x = t`，把目标里的 `t` 换成 `x`（便于归纳/改写时钉住形态）。

**常见语法**
```coq
assert (H : P). { ... }          (* 或下一行子目标 *)
assert (H := lemma args).
pose (f := fun x => ...).
pose proof (uniqueness (H x) f I) as Hf.
remember (complicated_term) as h.
```

**何时用 / 何时别用**  
- **用**：大证明拆引理；同一事实要用两次；`remember` 固定复杂态射后再 `rewrite`。  
- **别用**：一次性就能 `rewrite (lemma ...)` 时，不必先 `assert`；`pose` 太多会污染上下文——用完 `clear`。

**仓库示例**
```coq
(* Theory/Isomorphism.v *)
assert (m := iso_to_epic f).

(* Structure/Terminal.v *)
pose proof (uniqueness (H x) f I) as Hf.
pose proof (uniqueness (H x) g I) as Hg.
now rewrite <- Hf, <- Hg.

(* Structure/Terminal.v — assert 带证明 *)
assert (Hf : to i ∘ (from i ∘ f) ≈ f)
  by (rewrite comp_assoc, iso_to_from; apply id_left).

(* Structure/Monoid.v — remember *)
remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
assert (h ≈ split ... ) by (rewrite Heqh; unfork; cat).
rewrite X; clear X Heqh h.

(* Lib/Tactics.v *)
Tactic Notation "spose" uconstr(H) "as" ident(X) :=
  pose proof H as X; simpl in X.
```

**易混点**  
- `assert (H := t)` vs `pose proof t as H`：几乎同效；后者更常用于「已有证明项」。  
- `remember` 一定带出 `Heqx`；改写后记得 `clear Heqx`/`subst`，否则上下文臃肿。  
- `set (x := t)`（见下节相关）类似 `pose`，但更偏「局部定义」。

---

### `subst`

**做什么**  
在上下文中找形如 `x = t` 或 `t = x`（`x` 为变量）的等式，把所有 `x` **替换成 `t`** 并清掉该等式。

**常见语法**
```coq
subst.          (* 能替的都替 *)
subst x.        (* 只替与 x 相关的等式 *)
```

**何时用 / 何时别用**  
- **用**：`inversion`/`destruct eqn` 之后清理；本库 `inv H := inversion H; subst; try clear H`。  
- **别用**：等式是 `≈` 而不是 `=` 时 **`subst` 无效**——应用 `rewrite`/`rewrites`。依赖很重的等式乱 `subst` 可能导致非法类型。

**仓库示例**
```coq
(* Lib/Tactics.v *)
Ltac inv H := inversion H; subst; try clear H.

(* Lib/NETList.v 等 *)
inversion H; subst; clear H.
destruct post; subst;
```

**易混点**  
- 本库主线是 `≈`，所以日常范畴证明里 `subst` 出现频率低于 `rewrite`；多见于 `Lib/*` 数据结构与 `=`。  
- `subst` 后变量名消失，调试时若「假设没了」先看是不是被替掉了。

---

### `clear`

**做什么**  
从上下文中**删除**指定假设/变量（及其依赖允许时），减轻噪音或避免 `auto` 误用。

**常见语法**
```coq
clear H.
clear H H0 x.
clear - H.          (* 清掉除 H 以外能清的（慎用） *)
clearbody x.        (* 保留变量，去掉其 := 定义体 *)
```

**何时用 / 何时别用**  
- **用**：`rewrite H; clear H` 防止重复改写；`remember` 用完后清 `Heqh`；Ltac 自动化扫假设时边用边清（见 `rewrites`）。  
- **别用**：后面还要用就别清；有依赖时 `clear` 会失败——先清依赖者或改用 `clearbody`。

**仓库示例**
```coq
(* Theory/Category.v — rewrites 战术片段 *)
| [ H : ?X ≈ ?Y |- context[?X] ] => rewrite !H; clear H
| [ H : ?X ≈ ?Y |- context[?X] ] => srewrite H; clear H

(* Structure/Monoid.v *)
rewrite X; clear X Heqh h.

(* Lib/Tactics.v — sapply/srewrite 用完即清 *)
let H := fresh "H" in pose proof F as H; cbn in H; apply H; clear H.
```

**易混点**  
- `clear H` 失败 ≠ 假设不存在，常常是「别的假设依赖 H」。  
- `clearbody`（如 `Theory/Isomorphism.v` 的 `clearbody f1 g1`）与 `clear` 不同：变量还在，只是变成不透明假设。

---

### `rename`

**做什么**  
给上下文中的假设/变量**换名**，不改变类型或证明内容。

**常见语法**
```coq
rename x into y.
rename x into F, y into G, x0 into eq_ob.
```

**何时用 / 何时别用**  
- **用**：`intros`/`destruct` 自动起名成 `x0`/`y1` 后，改成有语义的 `F`/`G`/`eq_ob`，提高可读性。  
- **别用**：想改的是**目标里的式子**而不是绑定名——那是 `change`/`set`/`remember` 的事。

**仓库示例**
```coq
(* Theory/Functor.v *)
rename x into F, y into G, x0 into eq_ob, x1 into x, y0 into y.
refine ((snd (transport_adjunction ...)) _).
...
rename x into F, y into G, z into H, x1 into F_eq_ob_G,
  e0 into F_eq_ob_G_resp_mor, ...
```

**易混点**  
- 新名字不能与已有标识冲突。  
- `rename` 不改变「谁依赖谁」，只改打印名。

---

### `generalize` / `specialize` / `revert`

**做什么**  
- `generalize t`：把项 `t` 重新变成目标前的 `∀`（「再抽象回去」）。  
- `generalize dependent x`：连同依赖 `x` 的假设一并泛化（归纳前常用）。  
- `specialize (H args)`：把假设 `H` 的部分量词**实例化**，就地更新 `H`。  
- `revert H`：把假设 `H` 变回目标上的前提（`intros` 的逆）；常用于调整归纳顺序。

**常见语法**
```coq
generalize n.
generalize dependent As.
specialize (epic y (f ∘ section) id).
specialize (H x) as Hx.     (* 视版本；或先 pose proof *)
revert H.
revert x y H.
```

**何时用 / 何时别用**  
- **用**：`induction` 前把依赖变量 `revert`/`generalize dependent`；`specialize` 收窄通用假设以便 `apply`。  
- **别用**：只是想用一次特化结果——`apply (H args)` / `rewrite (H args)` 往往更短，不必改上下文。

**仓库示例**
```coq
(* Theory/Isomorphism.v *)
specialize (epic y (f ∘ section) id).
intros.
apply epic.
rewrite <- comp_assoc.
rewrite section_comp; cat.

(* Lib/IList.v *)
generalize dependent As.
induction n; intros.

(* Lib/FMapExt.v *)
revert H.
...
revert y.
```

**易混点**  
- `specialize` **改写**原假设；若还要保留通用版，先用 `pose proof (H args) as H'`。  
- `revert` 顺序要小心：先 `revert` 依赖者。  
- `generalize t` 得到的是「∀ 新绑定，目标里出现该绑定」；名字通常是自动生成的。

---

### `change`

**做什么**  
把目标（或假设）中的某个子项**换成定义相等（convertible）的另一写法**。不生成证明义务——Coq 必须能看出两边可转换。

**常见语法**
```coq
change t with u.
change t with u in H.
change (iso_sym (iso_sym f)) in * .   (* 视具体目标形态 *)
```

**何时用 / 何时别用**  
- **用**：形态上可转换，但 `rewrite` 匹配不到（如包了 `iso_sym (iso_sym _)`）；为应用 `Proper` 实例摆好外观。  
- **别用**：两边**不可转换**时——那是 `replace`/`assert`+`rewrite` 的工作。

**仓库示例**
```coq
(* Theory/Isomorphism.v — from_equiv_implies_iso_equiv *)
set (f1 := iso_sym f).
set (g1 := iso_sym g).
change f with (iso_sym (iso_sym f)).
change g with (iso_sym (iso_sym g)).
change (iso_sym f) with f1.
change (iso_sym g) with g1.
clearbody f1 g1. clear f g.
```

**易混点**  
- `change` 成功 ⟺ 定义相等；失败不要硬猜，用 `replace` 并给出证明。  
- 与 `unfold`：`change` 常用来换成**另一个已有名字**的等价写法，而不一定展开定义体。

---

### `replace`

**做什么**  
把目标中的 `t` **换成** `u`，并留下子目标 `t = u`（或你指定的关系），需另行证明。

**常见语法**
```coq
replace t with u.
replace t with u by tac.     (* 顺手用 tac 证相等 *)
replace t with u in H.
```

**何时用 / 何时别用**  
- **用**：知道两边相等但**不是**定义相等（`change` 失败）；想局部改写又不想动全局 `rewrite` 方向。  
- **别用**：已有现成 `≈`/`=` 引理时，直接 `rewrite` 更短；本库主线更常 `rewrite`/`assert`+`rewrite`。

**仓库示例**
```coq
(* Tools/Abstraction.v *)
replace x with y by auto.

(* Theory/Coq/List/Proofs.v *)
replace [y, z & zs] with ([y] ++ [z & zs]).

(* Instance/Rng/Coequalizer.v *)
replace a with (b + k * 2)%Z by lia.
```

**易混点**  
- 默认留下的是 `=` 义务；若你真正需要 `≈`，往往手写 `assert (t ≈ u)` 再 `rewrite`。  
- `replace ... by tac` 的 `tac` 失败则整个战术失败。

---

### `refine`

**做什么**  
给出一个**带洞 `_` 的证明项骨架**，Coq 把每个洞变成子目标。比 `apply` 更灵活，常用来填 Record/`{| ... |}`。

**常见语法**
```coq
refine (Build_Category' ...).
refine {| to := _; from := _ |}.
unshelve refine (...).     (* 洞变成普通目标，而不是 shelved *)
refine (iso_compose _ X).
```

**何时用 / 何时别用**  
- **用**：构造 `Category`/`Functor`/`Isomorphism` 等记录；部分参数想稍后证明。  
- **别用**：简单目标用 `apply`/`exact` 即可；洞太多会难管理——配合 `simpl; intros` 或本库 `functor`/`construct` 宏。

**仓库示例**
```coq
(* Theory/Category.v *)
unshelve refine (Build_Category' (@Basics.arrow)
                                 (@Datatypes.id) (@Basics.compose));
intros; try reflexivity.
- refine {| equiv := fun f g => ∀ x, f x = g x |}.

(* Theory/Functor.v *)
refine {| to   := fmap[F] (to X)
        ; from := fmap (from X) |}.
Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).

(* Theory/Isomorphism.v *)
refine (iso_compose _ (iso_sym X)).
```

**易混点**  
- `_` 与 `?x`：refine 洞默认可能被 shelve；`unshelve` 强制立刻变成可见子目标（本库极常见）。  
- `refine` 后常需 `simpl; intros` 清理义务，见 `cat_simpl` / `Obligation Tactic`。

---

### `constructor` / `econstructor`

**做什么**  
对目标类型，尝试应用其**第一个能匹配的构造子**。`econstructor` 更宽松，允许构造子参数含 evar（类似 `apply` vs `eapply`）。

**常见语法**
```coq
constructor.
constructor; repeat intro.
econstructor.
unshelve econstructor; simpl; intros.   (* 本库 construct *)
```

**何时用 / 何时别用**  
- **用**：目标是 `Equivalence`、`Proper`、`∧`、单构造子 Record/`Class` 义务；本库 `equivalence`/`proper`/`construct` 的核心步骤。  
- **别用**：多构造子且需要特定那一个时，写 `apply Build_xxx` / `left`/`right` 更清晰；归纳证明的「归纳步骤」不该只靠盲 `constructor`。

**仓库示例**
```coq
(* Lib/Setoid.v *)
constructor; repeat intro.
- reflexivity.
- symmetry. now apply X.
- now rewrite X, X0.

(* Lib/Tactics.v *)
Ltac equivalence := constructor; repeat intro; simpl; try cat; intuition; ...
Ltac construct := unshelve econstructor; simpl; intros.

(* Theory/Functor.v *)
constructor; intros x y f g Hfg.
apply (fmap_inj (F:=G)).
...
exact Hfg.
```

**易混点**  
- `constructor` 选的是**类型检查能过**的构造子，不一定是你心里想的那个。  
- 与 `refine {| ... |}`：记录字段多时 `refine` 更可控；`econstructor` 适合「先撑开再逐个填」。

---

### `now`

**做什么**  
`now tac` ≈ 执行 `tac`，然后用 `easy` 尝试立刻关掉剩余简单目标（直觉上：「做完这步就该显然了」）。失败则整个战术失败。

**常见语法**
```coq
now apply H.
now rewrite X, X0.
now reflexivity.          (* 略冗余，但可见 *)
now (unfold transport_r).
try solve [ now transitivity (to y0) | now ... ].
```

**何时用 / 何时别用**  
- **用**：短义务收尾（`Program` Next Obligation、`equivalence` 分支）；表达「证完关键一步后应由 `≈`/`auto` 解决」。  
- **别用**：后面其实还有非平凡子目标时——`now` 会直接失败；改用 `tac; cat` / `tac; try reflexivity`。

**仓库示例**
```coq
(* Theory/Category.v *)
now transitivity (y x0).
now rewrite X, X0.
Proof. intros [H _]; now apply id_unique_left. Qed.

(* Theory/Isomorphism.v *)
now apply iso_sym_proper.
Next Obligation. now firstorder. Qed.

(* Theory/Functor.v *)
destruct p. now unfold transport_r.
now cat.
```

**易混点**  
- `now tac` 不是「tac 的别名」；它**额外**要求收尾成功。  
- 与 `by tac`（ssreflect）思想相近但本库主线是标准库战术 + 自建 `cat`。  
- 调试时若 `now rewrite H` 失败，拆开写成 `rewrite H; easy` / `rewrite H; cat` 看卡在哪。

---

## 本篇战术速查（与本库习惯）

| 战术 | 本库里最常见搭档 |
|------|------------------|
| `intros`/`intro` | `constructor; repeat intro`、`proper`/`equivalence` |
| `rewrite`/`rewrite <-` | `comp_assoc`、`id_left`、`iso_to_from`、`rewrites`、`srewrite` |
| `setoid_rewrite` | 双范畴等深上下文 + `at n`（`Pseudofunctor.v`） |
| `apply`/`eapply` | `compose_respects`、`cat`、`sapply` |
| `refine`/`unshelve` | `Build_Category'`、`functor`、`{| to := ..; from := .. |}` |
| `constructor`/`econstructor` | `equivalence`、`construct` |
| `simpl`/`unfold`/`fold` | `cat_simpl`、`transport`/`transport_r` |
| `assert`/`pose`/`remember` | `Terminal.v`、`Monoid.v`、`spose` |
| `now` | 短 Obligation 收尾、`now cat` |

## 相关文件

- `Lib/Setoid.v` — `≈` / `Setoid` / `Equivalence`
- `Lib/Tactics.v` — `cat`、`equivalence`、`proper`、`srewrite`、`construct`、`inv`、`spose`
- `Theory/Category.v` — `comp_left`/`comp_right`/`rewrites`
- `Theory/Functor.v`、`Theory/Isomorphism.v` — 大量日常战术范例
- `Structure/Terminal.v`、`Structure/Monoid.v` — `pose`/`assert`/`remember` 短例

