# Part C：逻辑战术 · 自动化 · 查询/求值

> 草稿。仓库：`category-theory`，分支：`docs/coq-commands-guide`。
> 扫描范围：`Theory/`、`Lib/`、`Structure/`、`Functor/`、`Instance/`、`Adjunction/` 等；示例优先短且可读的文件。
> 每条指令固定五段：**做什么 / 常见语法 / 何时用·何时别用 / 仓库示例 / 易混点**。
> 相关已有文档：[`docs/AUTOMATION.md`](../AUTOMATION.md)（库自定义 tactic 与 hint DB）、[`docs/NOTATION.md`](../NOTATION.md)（记号）。

---

## 1. 逻辑战术

### `split`

**做什么**

把目标里的「合取」拆成两个（或多个）子目标。典型目标形态：

- `A /\ B`、`A ∧ B`（本库 `Lib/Foundation.v` 把 `∧` 记成 `prod`）
- `A ↔ B`、`A <-> B`
- `A * B`（作为命题时，与合取同类）
- Record / 多字段构造目标（有时也用手写 `split`，但本库更常 `construct` / `econstructor`）

本质：对合取引入规则（`conj`）或对可拆类型做构造。

**常见语法**

```coq
split.                 (* 目标 A /\ B → 两个子目标 A、B *)
split; intros.         (* 拆开后再引入假设 *)
split; [ tac1 | tac2 ].
```

**何时用 / 何时别用**

- **用**：目标明确是「并且 / 双向 / 一对」时，第一步就 `split`，让证明树对齐目标结构。
- **别用**：目标是析取 `A \/ B`（要用 `left`/`right`）；目标是存在量词（要用 `exists`）；目标已是原子等式/态射等式（优先 `reflexivity` / `cat` / `rewrite`）。

**仓库示例**

`Theory/Category.v` 里把「定义域/陪域与复合」的双向命题直接拆开，再用 `auto` 收尾：

```coq
(* Theory/Category.v *)
Corollary dom_comp {x y z : C} (g : y ~> z) (f : x ~> y) :
  dom g = cod f ↔ dom (g ∘ f) = dom f.
Proof. split; auto. Qed.
```

`Lib/Datatypes.v` 里 `split` 嵌套使用（外层 `↔`，内层再拆）：

```coq
(* Lib/Datatypes.v *)
split; intros.
  split; intros;
  apply H; apply in_or_app.
    left; trivial.
  right; trivial.
```

**易混点**

- `split` 拆的是**目标**；上下文里已有的 `H : A /\ B` 要用 `destruct H`（或 `destruct H as [H1 H2]`），不是 `split H`。
- 本库 `simplify`（见 `Lib/Tactics.v`）内部已对 `_ ∧ _` / `_ /\ _` / `_ ↔ _` 目标自动 `split`，所以很多地方你看不到手写 `split`，而是被 `cat` / `cat_simpl` 吃掉了。
- 目标是 `sig` / `sigT` / `exists` 时，不要用 `split`，用 `exists` 或 `eexists`。

---

### `left` / `right`

**做什么**

证明析取目标 `A \/ B`（或本库记号 `A ∨ B`，底层是 `sum`）时，选择走左支或右支：

- `left` ≡ 提供 `A` 的证明（构造 `or_introl` / `inl`）
- `right` ≡ 提供 `B` 的证明（构造 `or_intror` / `inr`）

**常见语法**

```coq
left.                  (* 目标 A \/ B → 只需证 A *)
right.                 (* 目标 A \/ B → 只需证 B *)
left; assumption.
right; auto.
```

**何时用 / 何时别用**

- **用**：目标是析取，且你已经知道该走哪一边（常见于 `match`/`destruct` 后的分支、或 `in_or_app` 这类引理的前件）。
- **别用**：目标是合取（用 `split`）；你还不确定哪一边成立时，先 `destruct` 假设再决定，而不是瞎猜 `left`/`right`。

**仓库示例**

`Lib/Datatypes.v`：为了把元素放进 `app` 的左/右列表：

```coq
(* Lib/Datatypes.v *)
apply H; apply in_or_app.
  left; trivial.
right; trivial.
```

`Theory/Metacategory/ETAC.v` 在递归证明里按归纳假设选边：

```coq
(* Theory/Metacategory/ETAC.v *)
+ left; exact (IHp1 _ _ _ _ Hρ Hσ H).
+ right; exact (IHp2 _ _ _ _ Hρ Hσ H).
```

**易混点**

- `left`/`right` 是**证明战术**，不要和范畴里的「左单位 `id_left` / 右单位 `id_right`」、或同构里的「左逆 / 右逆」术语混淆——那些是定义名，不是战术。
- 对 `sumbool`（`{A} + {B}`，如 `eq_dec` 的结果）做模式匹配时，也会看到 `left H` / `right H`，那是**构造子模式**，不是战术调用。
- 选错边会导致后续无法关闭；若两边都可能，通常应回到假设上 `destruct`，而不是硬选。

---

### `exists`（战术）

**做什么**

证明存在量词目标 `exists x, P x` / `∃ x, P x` / `sigT` 时，给出一个具体见证（witness），把目标收成 `P witness`。

注意：本库在 `Lib/Foundation.v` 里把 `'exists' x .. y , p` 记成 `sigT` 链，并提供 `∃` 记号——所以你在目标里看到的「存在」常常是依赖对，而不一定是 `ex`。

**常见语法**

```coq
exists 0.                    (* 给出 nat 见证 *)
exists (fobj[F] c).
exists (fun x => iso_id).
eexists.                     (* 先放 evar，稍后再实例化 *)
exists {| to := d; from := d' |}.   (* 给 record 见证 *)
```

**何时用 / 何时别用**

- **用**：目标以 `exists` / `∃` / `sig` / `sigT` 开头，且你已经知道见证是什么（或能用 `eexists` 延后）。
- **别用**：目标是全称 `∀`（用 `intros` / `intro`）；目标是合取（用 `split`）。也不要把「上下文里的存在假设」当成目标——那要用 `destruct` / `elim`。

**仓库示例**

`Structure/UniversalProperty/Universal/Arrow.v`：直接给出函子复合作为见证：

```coq
(* Structure/UniversalProperty/Universal/Arrow.v *)
exists ((Curried_Hom C c) ◯ U).
intro a.
```

`Structure/AbCategory.v` 多处用常值同构族：

```coq
(* Structure/AbCategory.v *)
exists (fun x => iso_id).
```

`Theory/Functor.v` 在 `match` 战术脚本里也会出现 `exists iso`（作为分支动作的一部分）。

**易混点**

- 战术 `exists t` ≠ 记号 `exists x, P`。前者是证明步骤，后者是命题语法。
- 见证类型必须匹配；若依赖参数很多，优先 `eexists` 或 `unshelve eexists`，再逐步填。
- 本库大量 `Program` / `construct` 会自动为 record 字段留洞，不一定手写 `exists`。

---

### `discriminate`

**做什么**

当上下文（或目标）里出现「两个**不同构造子**相等」的荒谬等式（如 `Some x = None`、`true = false`、`0 = S n`）时，直接关闭目标。底层依赖构造子不相交（no confusion）。

**常见语法**

```coq
discriminate.              (* 从当前目标/上下文找荒谬等式 *)
discriminate H.            (* 明确指出假设 H *)
intros H; discriminate H.
destruct (eq_dec a b); [|discriminate]; subst.
```

**何时用 / 何时别用**

- **用**：分支里已经得到不可能的构造子等式；或 `option`/`bool`/`nat` 等归纳类型上的矛盾。
- **别用**：等式两边是同一构造子（要用 `injection` / `inversion`）；等式是 setoid 的 `≈` 而不是 `=`（`discriminate` 只管 Leibniz `=`）。

**仓库示例**

`Lib/Datatypes.v` 在 `option` setoid 的义务里，用 `intuition; discriminate` 清掉交叉情况：

```coq
(* Lib/Datatypes.v — option_setoid *)
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
```

`Theory/Natural/Transformation/Arrows.v`：证明两个平行箭头不可等同：

```coq
(* Theory/Natural/Transformation/Arrows.v *)
Lemma par_one_two_distinct : ¬ (par_one ≈ par_two).
Proof. intros H; unfold par_one, par_two in H; simpl in H; discriminate. Qed.
```

`Lib/NETList.v` 典型写法：`eq_dec` 失败分支直接 `discriminate`。

**易混点**

- 先 `simpl` / `unfold` 把定义打开，否则荒谬等式可能藏在定义后面，`discriminate` 找不到。
- 依赖等式（`existT` 包着的）有时要先 `injection` / `inversion` 再 `discriminate`。
- 与 `contradiction` / `exfalso` 的分工：`discriminate` 专打构造子冲突；一般逻辑假用后两者。

---

### `inversion`

**做什么**

对假设做「按构造反演」：根据归纳类型的构造子，把假设拆成可能的情形，并生成相应的等式（常伴随 `subst`）。比单纯 `destruct` 更强——会分析等式约束，丢掉不可能分支。

**常见语法**

```coq
inversion H.
inversion H; subst.
inversion H; subst; clear H.
inversion_clear H.          (* 反演后清掉原假设 *)
dependent inversion H.      (* 依赖情形，较少用手写 *)
```

本库封装：`Lib/Tactics.v` 中

```coq
Ltac inv H := inversion H; subst; try clear H.
```

**何时用 / 何时别用**

- **用**：假设是归纳谓词 / 归纳等式（`Forall`、自定义归纳关系、构造子等式），需要取出内层信息或排除不可能情形。
- **别用**：只是普通 record / 合取（用 `destruct` 更干净）；对很大的归纳会生成大量等式，证明项臃肿——有时改用 `destruct` + `discriminate` 更可控。

**仓库示例**

`Lib/Datatypes.v`：

```coq
(* Lib/Datatypes.v *)
now inversion H0.
(* … *)
induction xs, ys; simpl; intros; auto; try inv H.
```

`Lib/NETList.v`：

```coq
inversion H.
inversion H; subst; clear H.
apply inj_pair2 in H2; auto.
```

**易混点**

- `inversion` vs `destruct`：`destruct` 机械拆构造子；`inversion` 还会利用等式，自动杀掉不可能分支。
- `inversion` 常留下 `H0`、`H1`… 一串等式，记得 `subst` 或改用 `inv` / `inversion_clear`。
- 依赖类型上的 `inversion` 可能需要 `eq_rect` / `inj_pair2`（公理相关，见 `docs/AXIOMS.md` 若涉及）。

---

### `injection`

**做什么**

当假设是「同一构造子下的等式」`C a1 … an = C b1 … bn` 时，推出分量等式 `a1 = b1`、…、`an = bn`（构造子单射）。不会拆分支，只「往里看一层」。

**常见语法**

```coq
injection H.                 (* 把分量等式推到目标前件，再 intros *)
injection H as H1 H2.
injection H; intros; subst.
now injection H.
injection H as <-.           (* 直接 subst 进上下文，较新写法 *)
```

**何时用 / 何时别用**

- **用**：`Some a = Some b`、`S n = S m`、`(_, _) = (_, _)`、`Fin.FS x = Fin.FS y` 等。
- **别用**：不同构造子（用 `discriminate`）；已经是原子等式；对依赖构造子有时 `injection` 不够干净，仓库里会改用局部逆函数（见下例注释）。

**仓库示例**

`Instance/FinSet/Skeleton.v`：

```coq
(* Instance/FinSet/Skeleton.v *)
Lemma FS_injective {n : nat} (x y : Fin.t n) : Fin.FS x = Fin.FS y → x = y.
Proof.
  intro H.
  apply (f_equal fin_pred_option) in H.
  simpl in H.
  now injection H.
Qed.
```

`Instance/Top/Hausdorff.v` 常见组合：`injection … as <-` 后接 `exfalso`。

`Instance/WalkingIso.v`：`injection H as H.` / `now injection H.`

**易混点**

- `injection` ≠ `f_equal`：前者从「构造子等式」推分量；后者把已知等式「推到函数外面」。二者常联用。
- `injection H` 默认把新等式放到**目标**上（变成蕴含），通常要紧跟 `intros` / `as …`。
- 依赖配对 `existT` 上，单纯 `injection` 可能只得到异质等式，还需 `inj_pair2` 一类引理。

---

### `congruence`

**做什么**

等式的「全自动同余闭包」求解器：结合上下文中的 `=`、构造子单射/不相交、以及函数应用同余，尝试关闭目标。能同时覆盖许多本可用 `subst`+`rewrite`+`discriminate`+`f_equal` 拼出来的短证明。

**常见语法**

```coq
congruence.
congruence n.          (* 限制推理深度，少见 *)
intros; congruence.
intuition congruence.  (* 先做直觉逻辑化简再 congruence *)
```

**何时用 / 何时别用**

- **用**：一堆 Leibniz 等式绕来绕去；`f x = f y` 且已知 `x = y`；构造子冲突混在等式链里。
- **别用**：目标是 setoid `≈`（不是 `=`）；需要引理/范畴定律（用 `cat` / `rewrite`）；大型算术（用 `lia` / `ring`）。

**仓库示例**

`Lib/MapDecide.v`：

```coq
(* Lib/MapDecide.v *)
apply term_beq_sound in Heqb.
congruence.
```

`Theory/Coq/Map.v`：

```coq
transitivity (lookup k0 y); congruence.
```

`Theory/Coq/List/Proofs.v`：`induction …; simpl; congruence.`

`Instance/Presented/Three.v` / `Instance/Square.v`：`exfalso; intuition congruence`。

**易混点**

- `congruence` 只管 `=`，不管 `≈`。本库大量态射等式是 `≈`，那些场合用 `cat` / `rewrite` / `proper`。
- 失败时不会部分推进；要么关掉，要么原样留下——不要指望它「先帮你 rewrite 一下」。
- 与 `f_equal`：`f_equal` 是单步「往外加函数」；`congruence` 是多步闭环。

---

### `contradict` / `exfalso` / `absurd`

**做什么**

三者都通向「从矛盾证任意目标」，但切入点不同：

| 战术 | 作用 |
|------|------|
| `exfalso` | 把当前目标换成 `False`，然后你去证假 |
| `absurd P` | 生成两个子目标：`P` 与 `~P`（证完即得 `False`） |
| `contradict H` | 若 `H : ~P`，则目标换成 `P`；若 `H : P`，则目标换成 `~P`（翻转「与 H 矛盾」） |

**常见语法**

```coq
exfalso.                 (* goal := False *)
exfalso; apply H.
exfalso; discriminate.
absurd (n < 0).          (* 需分别证 n<0 与 ~(n<0) *)
contradict H.            (* 翻转与 H 的关系 *)
```

**何时用 / 何时别用**

- **用**：你已看出当前分支荒谬，但目标本身不是 `False`；或想先把目标收成假再调用 `discriminate` / `lia` / 专用引理。
- **别用**：已经有直接的 `discriminate` / `contradiction` 可关时，不必绕；本仓库里 **`exfalso` 很常见，`absurd` / `contradict` 几乎不出现在提交的 `.v` 里**（交互证明里仍可用）。

**仓库示例**

`Instance/Top/Hausdorff.v`：

```coq
injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
```

`Theory/Metacategory/ETAC.v`：

```coq
intros n Hn; exfalso; exact (PeanoNat.Nat.nlt_0_r n Hn).
```

`Instance/Fun/Closed.v`、`Structure/Complete/Freyd.v`、`Instance/Parallel.v` 等亦有独立的 `exfalso.` 行。

`absurd` / `contradict`：扫描未见战术用法（仅注释里出现英文 “absurd”）；小白若在 IDE 里需要「翻转否定假设」，可记 `contradict H`，但本库风格更偏向 `exfalso; exact …` 或 `intuition; discriminate`。

**易混点**

- `exfalso` 之后目标是 `False`，不是「任意命题」——你仍需证明假。
- `contradiction`（未单列但常一起学）：若上下文已有 `H : False` 或一对 `P`/`~P`，可直接关目标；与 `exfalso` 不同，它不改目标形态。
- 不要用 `exfalso` 逃避该用的构造——只有分支确实不可能时才合适。

---

### `intuition` / `firstorder`

**做什么**

- `intuition`：直觉主义命题逻辑的自动化（合取/析取/蕴含/否定/`True`/`False` 等），常把目标拆开并尝试 `auto`。
- `firstorder`：一阶逻辑自动化（带量词），比 `intuition` 更能处理 `exists`/`forall` 交织的目标。

本库在 `Lib/Tactics.v` 的 `equivalence` / `proper` 里**内嵌了 `intuition`**，所以很多 setoid 义务你看不到手写，却间接受益。

**常见语法**

```coq
intuition.
intuition auto.
intuition discriminate.
intuition congruence.
firstorder.
now firstorder.
firstorder eauto.
```

**何时用 / 何时别用**

- **用**：纯逻辑连接词堆叠；`↔` 的对称/传递义务；`option`/`list` 等价里「显然」的逻辑壳。
- **别用**：核心是范畴等式 `≈`、需要 `rewrite` 引理、或算术——先 `cat` / `lia`，不要把希望寄托在 `intuition` 上。`firstorder` 失败时可能很慢，大目标慎用。

**仓库示例**

`Theory/Isomorphism.v`：

```coq
(* Theory/Isomorphism.v — iso_equiv_equivalence *)
Next Obligation. now firstorder. Qed.
Next Obligation. now firstorder. Qed.
Next Obligation.
  firstorder;
  try solve [ now transitivity (to y0)
            | now transitivity (from y0) ].
Qed.
```

`Lib/Datatypes.v`：

```coq
Next Obligation. intuition; discriminate. Qed.
(* … *)
- firstorder.
```

`Lib/Tactics.v`（定义层，展示库如何调用）：

```coq
Ltac equivalence := constructor; repeat intro; simpl; try cat; intuition; …
Ltac proper := repeat intro; simpl; try cat; intuition.
```

**易混点**

- `intuition` 默认可能调用 `auto with *`，有时引入意外 hint（仓库里可见 `Local Set Warnings "-intuition-auto-with-star"`）。
- `firstorder` ≠ `eauto`：前者偏一阶逻辑搜索，后者偏带 evar 的 hint 应用。
- 证明项可能偏大；关键引理更宜手写清晰步骤，把 `intuition`/`firstorder` 留给义务收尾。

---

## 2. 自动化与求解器

### `auto` / `eauto` / `trivial` / `easy` / `now`

**做什么**

| 战术 | 一句话 |
|------|--------|
| `auto` | 用 hint 数据库做有界深度的 `apply` 搜索（默认 `core`） |
| `eauto` | 同 `auto`，但允许 evar（可「先占位再填」） |
| `trivial` | 极浅的自动（比 `auto` 弱，适合一眼能关的目标） |
| `easy` | `trivial` 的加强版：再试 `inversion`/`solve` 等简单套路 |
| `now tac` | 先跑 `tac`，再用 `easy` 风格收尾；关不掉就失败 |

**常见语法**

```coq
auto.
auto with category_laws.
auto with *.
eauto.
intuition eauto.
trivial.
easy.
now cat.
now rewrite Hg.
now apply id_unique_left.
Proof. auto. Qed.
```

**何时用 / 何时别用**

- **用**：收尾；`intros`/`split`/`destruct` 之后「剩下显然」；配合本库 `category_laws` / `categories` hint（见 `docs/AUTOMATION.md`）。
- **别用**：主线推理（应写出关键 `rewrite`/`apply`）；盲目 `auto with *` 可能慢且证明项不稳。本库更推荐 **`cat` / `cat_simpl`** 处理态射层目标。

**仓库示例**

`Theory/Category.v`：

```coq
Proof. auto. Qed.                 (* dom_id / cod_id *)
Proof. split; auto. Qed.
Proof. intros [H _]; now apply id_unique_left. Qed.
```

`Theory/Functor.v`：

```coq
now cat.
destruct p. now trivial.
```

`Lib/Datatypes.v`：`left; trivial.` / `right; trivial.`

`Structure/UniversalProperty/Universal/Arrow.v`：

```coq
rewrite (unique_property universal_arrow_universal); easy).
```

`Structure/UniversalProperty/Limit.v`：`Hint Extern 20 => easy : core.`

**易混点**

- `now tac` 失败 = 整步失败（不会留下 `tac` 的中间状态），适合「断言这步必须关完」。
- `auto` 默认不用你自己的引理，除非 `Hint` 进数据库，或写成 `auto using lem`。
- 本库义务默认 `Obligation Tactic := cat_simpl`（见下节自定义），很多 `Next Obligation` 无需手写 `auto`。

---

### `lia`

**做什么**

线性整数算术求解器（Linear Integer Arithmetic）：处理 `nat`/`Z` 上带 `+`、`-`、常数倍、比较的目标。来自 `Lia` 模块（`Require Import Lia.`）。

**常见语法**

```coq
lia.
simpl; lia.
pose proof (size_delete i' m); lia.
exfalso; lia.
```

**何时用 / 何时别用**

- **用**：大小/长度/索引不等式；`wf` 义务里证明测度下降；`n <= m`、`S n = S m → …` 等。
- **别用**：含乘法非线性（多数情况；那时试 `nia`）；环等式恒等（优先 `ring`）；范畴 `≈`（与算术无关）。

**仓库示例**

`Theory/Coq/Map.v`：

```coq
(* Theory/Coq/Map.v *)
Lemma size_delete `{EqDec k} i m : (size (delete i m) <= size m)%nat.
Proof.
  induction m; simpl; auto.
  destruct (eq_dec i k0) eqn:Heqe;
  auto; simpl; lia.
Qed.
(* … *)
pose proof (size_delete i' m); lia.
```

`Lib/MapDecide.v`：`rewrite …; simpl; lia.`

`Instance/InnerProduct/Galois.v`：`injection Hin; intros; lia.`

**易混点**

- 目标里若还有定义包装，先 `simpl`/`unfold`/`cbn`。
- `lia` 失败时看是否混入了非算术假设；可 `clear` 无关假设再试。
- 与 `omega`（旧）：现代 Coq/Rocq 用 `lia`，不要再学 `omega`。

---

### `ring`

**做什么**

环/半环上的代数恒等求解器：自动证明如 `a + b = b + a`、`a * (b + c) = a*b + a*c`、`(m * n * p = m * (n * p))%Z` 等（在已注册的 `ring` 结构上）。

**常见语法**

```coq
ring.
assert (H : (1 * n = n)%Z) by ring; exact H.
apply ut2_eq3; ring.
exists (k + l)%Z; ring.
```

**何时用 / 何时别用**

- **用**：`Z`、多项式、矩阵条目、Rng 实例里「纯代数展开即得」的等式。
- **别用**：不等式（用 `lia`）；含自定义函数且未告知 `ring`；范畴态射等式。

**仓库示例**

`Adjunction/Unitalization.v`：

```coq
- assert (H : (m * n * p = m * (n * p))%Z) by ring; exact H.
- assert (H : (1 * n = n)%Z) by ring; exact H.
- assert (H : (m * (n + p) = m * n + m * p)%Z) by ring; exact H.
```

`Instance/Rng/Quotient.v`：`exists (k + l)%Z; ring.`

`Instance/Rng/Algebras/Associative.v`：`apply ut2_eq3; ring.`

**易混点**

- `ring` 证等式，不证 `≤`/`≠`。
- 需要目标类型上有 `Ring`/`SemiRing` 实例；否则报错。
- `ring_simplify`（相关）：只化简不关目标，本任务不展开，需要时可查手册。

---

### `f_equal`

**做什么**

把目标 `f a = f b` 收成 `a = b`（对函数构造子 / 应用做同余）。多参数时可逐步剥：`f x y = f x' y'` → 先证 `x = x'` 再证 `y = y'`。

**常见语法**

```coq
f_equal.
f_equal; auto.
apply f_equal.
apply (f_equal fin_pred_option) in H.   (* 对假设用 *)
```

**何时用 / 何时别用**

- **用**：两边同一函数头；列表 `map` 后归纳；构造子外层已对齐。
- **别用**：两边函数不同；目标是 `≈`（要用 `Proper` / `rewrite`）；更复杂同余用 `congruence` 可能一次做完。

**仓库示例**

`Lib/Datatypes.v`：

```coq
(* Lib/Datatypes.v — map_inj *)
apply f_inj in H1; subst.
f_equal.
now apply IHxs.
```

`Instance/FinSet/Skeleton.v`（对假设使用）：

```coq
apply (f_equal fin_pred_option) in H.
simpl in H.
now injection H.
```

`Theory/Functor.v` 在运输（`transport`）引理里大量出现**函数** `f_equal`（标准库项），与战术同名——见易混点。

**易混点**

- 战术 `f_equal` vs 引理 `f_equal : ∀ f x y, x = y → f x = f y`：写法都是 `f_equal`，语境不同（战术位置 vs `apply (f_equal …)`）。
- 只处理 `=`，不处理 `≈`。
- 剥多层时可 `repeat f_equal`，但有时不如 `congruence` 干净。

---

### 本库自定义助手（`Lib/Tactics.v`，点到为止）

完整契约见 [`docs/AUTOMATION.md`](../AUTOMATION.md)。这里只列小白读本仓库时最常撞见的名字（**不要整文件背诵**）：

| 名称 | 作用（极简） | 典型出现 |
|------|----------------|----------|
| `cat` | `simplify` + `autorewrite with categories` + `auto with category_laws` + 尝试 `reflexivity` | `Theory/Functor.v`：`now cat.` |
| `cat_simpl` | 更强；也是全局 `Obligation Tactic` | 多数 `Program` 义务自动跑 |
| `equivalence` | 关 `Equivalence` 目标 | `Theory/Category.v` / `Functor.v` |
| `proper` | 关 `Proper` / `respectful` | `Theory/Isomorphism.v`：`proper.` |
| `construct` | `unshelve econstructor; simpl; intros` | `Proof. construct; cat. Qed.` |
| `simplify` | `cat` 内部的结构前奏（拆 `∧`/`*`/`↔` 等） | 一般不手写 |
| `inv H` | `inversion H; subst; try clear H` | `Lib/Datatypes.v`：`try inv H` |
| `spose F as X` | `pose proof` + `simpl` | 实例化 setoid 引理 |
| `sapply` / `srewrite` / `srewrite_r` | 先 `cbn` 再 `apply`/`rewrite` | `Theory/Category.v` 的 `rewrites` 提示 |
| `normal` | 复合链左结合规范化 | 定义在 `Functor/Bifunctor.v`，**不在** `Tactics.v` |
| `isomorphism` | 关 `_ ≅ _` | `Theory/Isomorphism.v` |

Hint 库：`categories`（rewrite）、`category_laws`（`auto`）、以及扩展后的 `core`。下游约定见 `docs/AUTOMATION.md`「推荐的下游约定」。

---

## 3. 查询与求值命令

> 下列多数是**交互命令**（IDE / `coqtop` 里敲），部分也会写进 `.v` 做编译期检查（本仓库 `Check` / `About` / `Eval` 较常见）。

### `Check`

**做什么**

显示一个项的类型（以及宇宙级别等信息）。用于确认「这个标识符/表达式到底是什么类型」，或在文件末尾做回归钉扎（nail down API）。

**常见语法**

```coq
Check id.
Check (@id C x).
Check (fun z : obj[C] => @GroupObject C CM z).
Check @Monoidal.
Fail Check (Top_Discrete ⊣ Top_Forget).   (* 期望失败时 *)
```

**何时用 / 何时别用**

- **用**：搞不清记号背后的类型；确认隐式参数；CI/文件尾部「类型仍是这样」的断言。
- **别用**：想看定义体（用 `Print`）；想搜索名字（用 `Search`/`Locate`）。

**仓库示例**

`Adjunction/Unitalization.v`、`Theory/Algebra/Group/Hom.v`、`Theory/Density.v`、`Instance/Rng/Free.v` 等文件末尾有大量 `Check …` 钉扎。

`Test/Probe*.v` 里几乎整页 `Check`（探针测试）；读理论时优先看 `Theory/` / `Adjunction/` 里较短的几行即可。

**易混点**

- `Check` 不证明任何东西，只打印类型。
- 记号未 `Open Scope` 时，`Check` 可能显示成丑陋的展开式——先打开正确 scope（见 `docs/NOTATION.md`）。

---

### `Print`

**做什么**

打印定义/归纳类型/模块的**完整体**（不只是类型）。

**常见语法**

```coq
Print nat.
Print Category.
Print Assumptions my_lemma.   (* 列出证明用到的公理 *)
```

**何时用 / 何时别用**

- **用**：想看 record 有哪些字段；核对不透明/`Qed` 后是否还能计算；查公理依赖（`Print Assumptions`）。
- **别用**：只关心类型时用 `Check` 更干净；巨型归纳打印刷屏。

**仓库示例**

提交的 `.v` 里直接写 `Print` 较少；`Instance/FinSet/Skeleton.v` 注释提到用 `Print Assumptions` 做公理审计。交互阅读 `Category` / `Functor` / `Isomorphism` 时，在 IDE 里对标识符 `Print` 最有用。

**易混点**

- `Print` vs `About`：`About` 给摘要（类型、参数、隐式、出处）；`Print` 给定义体。
- `Qed` 证明的引理对 `Print` 通常不透明（看不到证明项细节），这是刻意的。

---

### `Search`

**做什么**

按类型模式 / 名字子串搜索引理。小白最强的「库内谷歌」。

**常见语法**

```coq
Search (id ∘ _).
Search "fmap".
Search (?f ∘ id ≈ ?f).
Search bool : nat.           (* 多模式；具体版本语法略有差异 *)
```

**何时用 / 何时别用**

- **用**：记得结论形态但忘了引理名；探索 `categories` 里已有什么 rewrite。
- **别用**：已知全名时直接 `Check`/`Locate`；模式写太宽会淹没输出。

**仓库示例**

`.v` 源文件中几乎不提交 `Search`（交互命令）。读本库时建议在已 `Require Import Category.Theory.Category` 的会话里：

```coq
Search (id ∘ _).
Search (_ ∘ id ≈ _).
```

对照 `docs/AUTOMATION.md` 中 `categories` 数据库内容（`id_left`、`id_right`、`comp_assoc`、`fmap_id`…）。

**易混点**

- 不同 Coq/Rocq 版本 `Search` 语法略有变迁；以你本机 `Search` 帮助为准。
- 搜 `≈` 前要确保 setoid/范畴 scope 已开，否则模式可能匹配不到。

---

### `Locate`

**做什么**

查一个**记号或短名**到底解析到哪个完整路径 / 哪种 notation。

**常见语法**

```coq
Locate "∘".
Locate "≅".
Locate fmap.
Locate Category.
```

**何时用 / 何时别用**

- **用**：记号冲突、多个 `∘`、不确定 `≅` 来自哪；`docs/NOTATION.md` 对不上时现场确认。
- **别用**：已知模块路径时直接 `Check Module.path`。

**仓库示例**

源码中少见提交；与 `docs/NOTATION.md` 对照使用。例如打开 `homset_scope` / `morphism_scope` 后 `Locate "∘"`，应指向本库复合记号。

**易混点**

- `Locate "∘"`（带引号）查记号；`Locate compose` 查标识符。
- 同一记号可能有多条，看输出里的 scope / level。

---

### `About`

**做什么**

打印常量的「名片」：类型、隐式参数、可匹配性、定义出处等，比 `Check` 啰嗦、比 `Print` 短。

**常见语法**

```coq
About Dorroh.
About unitalization_adjunction.
About fmap.
```

**何时用 / 何时别用**

- **用**：快速了解引理要几个隐式参数、是否 `Program` 生成；读陌生 API 第一站。
- **别用**：需要定义体时用 `Print`；需要类型是否可判定时用 `Check` 即可。

**仓库示例**

`Adjunction/Unitalization.v`：

```coq
About Dorroh.
About unitalization_adjunction.
```

`Instance/Rg.v`：`About Rg_trivial.` / `About Rg_Zero.`

**易混点**

- `About` 对记号本身可能不如 `Locate` 直观——先 `Locate` 找到常量名，再 `About`。

---

### `Compute` / `Eval` / `cbv` / `lazy` / `compute`

**做什么**

对项做**化简/求值**并显示结果（或在定义里嵌入化简后的项）。

| 形式 | 角色 |
|------|------|
| `Compute t` | 交互：用默认策略算出 `t` 的值 |
| `Eval strat in t` | 交互/定义：用指定策略 `strat` 求值 |
| `cbv` | 战术/策略：call-by-value（可限制 `beta iota delta […]`） |
| `lazy` | 惰性策略 |
| `compute` | 战术：大致相当于强化简当前目标（常用 `cbv` 的别名风格） |

**常见语法**

```coq
Compute (1 + 1).
Eval cbn in (id ∘ f).
Eval cbv beta iota zeta delta [ liftM ] in
  λ x y, bind x (λ x, liftM (f x) y).

(* 作为战术 *)
cbv beta.
cbv beta iota delta [ foo bar ].
lazy.
compute.          (* 视版本/上下文 *)
```

**何时用 / 何时别用**

- **用**：看封闭项算到多少；在定义里**展开某几个常量**而保持其余不动（`delta [ … ]`）；证明前先观察目标形态。
- **别用**：对含公理/不透明 `Qed` 的项强行 `Compute` 往往停在原地；证明中大手 `compute` 可能把目标撑爆——本库更常用 `simpl` / `cbn` / `cat`。

**仓库示例**

`Theory/Coq/Monad.v`——在**定义**里用 `Eval cbv …` 展开 `liftM`，避免层层包装：

```coq
(* Theory/Coq/Monad.v *)
Definition liftM2 {x y z : Type@{d}} (f : x → y → z) : F x → F y → F z :=
  Eval cbv beta iota zeta delta [ liftM ] in
    λ x y, bind x (λ x, liftM (f x) y).
```

`Monad/Kleisli/Comparison.v`：

```coq
intros x y f; cbv beta; rewrite !id_cast_refl, id_left, id_right; simpl.
```

**易混点**

- `cbn` / `simpl`（常见化简战术）比完整 `cbv` 更温和，日常证明优先它们。
- `Eval … in` 出现在定义右侧时，是**编译期**求值，结果写进常量体。
- `lazy` 与 `cbv` 对同一项可能表现不同；出怪结果时换策略对比。
- 文件名 `Instance/Fun/Eval.v`、`Instance/Lambda/Eval.v` 里的 `Eval` 是**范畴定义名**，不是求值命令——别搜混。

---

### `Show`

**做什么**

在证明模式中，打印当前证明状态：剩余目标、局部上下文等。变体可显示某个目标、脚本、存在变量等。

**常见语法**

```coq
Show.                (* 当前目标与上下文 *)
Show 2.              (* 第 2 个目标 *)
Show Proof.          (* 当前证明项 *)
Show Script.         (* 部分版本 *)
Show Existentials.
```

**何时用 / 何时别用**

- **用**：IDE 焦点乱了；多目标时想看全局；调试 `Focus`/`All` 之后的状态。
- **别用**：写进库代码当注释替代——本仓库 **`.v` 中基本不提交 `Show`**（纯交互）。

**仓库示例**

无稳定的源码落点。推荐在证明 `Theory/Category.v` 里任选一条 `Corollary`，于 `Proof.` 后手动 `Show.`，对照 goal 窗口理解 `split`/`auto` 前后变化。

**易混点**

- `Show` 不改变证明状态。
- 有的 IDE（Proof General / VsCoq / Rocq LSP）已用面板替代 `Show`，但命令仍可用。
- `Show Proof` 在 `Qed` 前有用；`Defined` 的透明证明更易读。

---

## 附：与 Part A/B 的分工（合并时用）

- **Part A**（结构声明）：`Require`/`Import`、`Section`、`Context`、`Class`/`Record`/`Program`、`Notation`、`Hint`、`Obligation`…
- **Part B**（核心证明战术）：`intros`/`apply`/`rewrite`/`destruct`/`induction`/`assert`/`pose`/`specialize`/`reflexivity`/`symmetry`/`transitivity`…
- **Part C**（本文）：逻辑连接词与归纳等式、自动化求解器、查询求值；以及指向 `Lib/Tactics.v` 的库级包装。

读范畴证明时的经验顺序：

1. 目标是 `≈`？先想 `cat` / `rewrite` / `proper`（B + AUTOMATION）。
2. 目标是 `/\` `\/` `exists` `False`？用本文逻辑战术。
3. 目标是 `nat`/`Z` 算术？`lia` / `ring`。
4. 卡住不知有什么引理？`Search` / `Locate` / `About` / `Check`。

