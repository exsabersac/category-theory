# CLAUDE.md

本代码库是 Coq/Rocq 中范畴论的全面形式化。含 1177 个证明文件（`_CoqProject` 构建集——磁盘上有 1181 个 `.v` 文件，差额为 `doc/plan/books/probes/` 下三个未构建探测加上未注册的 `Structure/Limit/Preservation/Shapes.v`；此前 563/566 的数字早已过时，所述理由亦不完整）与超过 170,000 行，实现核心范畴概念，核心理论零公理——覆盖从范畴、函子、伴随到单子性、伴随函子定理、充实与高阶结构（双范畴、伪双重范畴）、Lawvere 理论、多范畴与 operad，以及初等 topos 理论的经典典范。

「核心理论零公理」比听上去更窄，docs/AXIOMS.md 是准确窄度的权威。两件独立事实成立。第一，库中任何地方仅有的 `Axiom`/`Parameter` 声明是 ZX-calculus 实例的三个 `Phase` 参数，全在 `Instance/ZX.v`。第二，`Print Assumptions` 对一份枚举的标题定义列表报告「Closed under the global context」，由 `make print-assumptions` 审计。第二点*不是*对库中每个定义的宣称——docs/AXIOMS.md 按术语如此说明——也未对 `Theory/`、`Structure/` 或 `Construction/` 做目录范围认证。具体实例层（`Instance/`、`Theory/Coq/`）确实使用 stdlib 公理，枚举于彼。另有许多高级旗舰定理是*参数化*证明的——作为抽象结构上的无公理条件句——仅部分由树内具体模型实例化；docs/INHABITATION.md 记录哪些。

**中文翻译说明（zh-CN）**：开篇与下方「命令 / 架构」要点已译；全文很长（约 45 KB），其余英文指导性章节本波次保留，后续可续译。

## 命令 (Commands)

### 构建库 (Building the Library)

```bash
# Build the entire library (default: Rocq 9.1)
make

# Build for specific version (if using Nix)
nix-shell -p coqPackages_9_1.coq --run make

# Build using Nix flake (the default package is category-theory_9_1)
nix build
# ...or select a version explicitly, e.g. nix build .#category-theory_8_20

# Clean build artifacts
make clean
make fullclean  # removes Makefile.coq as well

# Install library
make install

# Check for admitted proofs or TODOs
make todo

# Guard the preamble's file counts against _CoqProject and the tree
make claude-md-counts-check

# Guard docs/INDEX.md's five section headings (an Edit has eaten one twice)
make index-check
```

### 单文件开发 (Single File Development)

```bash
# Compile a single file
coqc -R . Category Theory/Category.v

# Interactive development (in coqide/vscoq)
# Ensure _CoqProject is loaded with: -R . Category
```

### 证明开发模式 (Proof Development Patterns)

本库在 `Lib/Tactics.v` 中使用自定义 tactic：
- `cat` - 范畴证明的标准化简
- `cat_simpl` - 更激进的化简，含 program obligation
- `proper` - 证明态射的尊重性
- `equivalence` - 证明等价关系

## 架构 (Architecture)

### 核心抽象层级 (Core Abstraction Hierarchy)

本库通过**基于 setoid 的态射**实现范畴论：态射形成等价类，而非使用严格相等。这一基本设计选择贯穿整个架构：

```
Category (homsets are setoids with ≈ equivalence)
    ↓
Functor (preserves equivalence, not just equality)
    ↓
Natural Transformation (naturality respects ≈)
    ↓
Adjunction/Monad/Kan Extension
```

### 宇宙多态策略 (Universe Polymorphism Strategy)

本库全程使用三个宇宙参数 `{o h p}`：
- `o` - 对象宇宙层级
- `h` - hom 集宇宙层级
- `p` - 证明/命题宇宙层级
- 约束：`h <= p` 保证态射证明可以引用态射

这使任意层级上的「范畴的范畴」成为可能，而不致宇宙不一致。

具体代数范畴是必须手写的例外。其对象记录携带 `PropEquiv`（`Lib/Setoid/Propositional.v`），即载体的 `≈` 在逻辑上是 `Prop`-值关系的性质——因为载体上的 `Prop`-值关系是载体大小的，而 `Type`-值关系高一个宇宙，伴随函子定理正依赖此算术。`Prop` 的排序随后给每个记录贡献 `Set+1`，会使建于其上的范畴多出第三个冗余宇宙，故 `CMon`、`Ab`、`Rig`、`Ring`、`Rg`、`Grp` 被**手工**钉到 `Category@{u p p}`，每个字段的实例写出，且记录的三个宇宙读作 `(辅助, 载体, 证明)` 而非 `(载体, 证明, 辅助)`。给三个槽不同层级的注解必须置换以匹配；全相等者如 `@{Set Set Set}` 不受影响。setoid 簇是反例：自 #450 起 `Instance/Variety/Free.v` 的 `SetoidOpAlgebra` 也携带 `PropEquiv`（字段 `soa_prop`），且**无需**手工钉住——`About` 测得 `SetoidAlgs` 保持七个宇宙与其 `Category@{u1 u2 u2}` 形状，仅多约束 `Set < u1`。为何需要这一切的权威陈述是 `Structure/Complete.v` 文首的大小注记；文档分歧以彼处为准。

### 对偶架构 (Duality Architecture)

**关键洞见**：对偶内建于定义，使 `C^op^op = C` 由 reflexivity 成立。

这要求核心定义中的对称定律：
- Category 中同时有 `comp_assoc` 与 `comp_assoc_sym`
- 自然变换中同时有 `naturality` 与 `naturality_sym`

好处：
- 余单子一行：`Definition Comonad := @Monad (C^op) (M^op)`
- 对偶证明常常自动
- 对偶概念无需代码重复

### 证明义务管理 (Proof Obligation Management)

本库广泛使用 Coq 的 Program 机制：
1. 定义用 `Program Instance` 推迟证明义务
2. `Obligation Tactic := cat_simpl` 自动化多数证明
3. 剩余义务用具体 tactic 证明
4. 从而把数学内容与证明细节分开

### 实例解析策略 (Instance Resolution Strategy)

范畴通过以下方式发现：
1. 概念的类型类（Category、Functor 等）
2. 条件实例用 `Existing Instance`
3. 带范畴提示的记号驱动推断
4. 推断失败时显式范畴参数

例：需要时用 `f ∘[C] g` 指定范畴 C。

## 关键文件与概念 (Key Files and Concepts)

本库 headline 开发的分项索引在 **docs/INDEX.md**：每个已落地开发一条 bullet，约 250 条，各说明交付了什么、强度如何（`eq_refl`、`≈`、相对 `StrictCat` 的 `Cat`）、测了什么及按何标准、以及**未**交付什么。直至 2026-09-09 这是本文件的 “Key Files and Concepts” 节，每条 bullet 未改。该日期前凡引用 CLAUDE.md Key Files 索引、其中 bullet/数字，或 CLAUDE.md 出现次数的材料，均指 docs/INDEX.md 中的条目或计数。

使用规则：
- 编辑文件前，在 docs/INDEX.md 中 grep 其 basename（有些 bullet 路径相对其节），若有 bullet 则先读：记录每项断言的强度与已遇陷阱（宇宙钉、`Qed`-不透明捐赠者、记号遮蔽、假通过探测等）。约三分之一 `.v` 有自己的 bullet，故缺席不是信号。
- 新工作在同类已在其下的标题下向 docs/INDEX.md **追加一条** bullet。索引节按主题而非按目录（`Structure/Topos.v` 在理论核心下），且 `Solver/`、`Tools/`、`Lib/`、`Test/` 在彼处无节。插入 bullet 的 `Edit` 曾两次吃掉后随标题，故前后检查 `grep -c '^- \*\*' docs/INDEX.md` 与 `grep -c '^## ' docs/INDEX.md`；`make index-check` 在五标题未按序全在时失败。仅当出现新目录或文件族时才改下方地图。
- bullet 中每个数字都是带标准的测量；无法从该句重测的数字不要写入。更正就地记为更正（「早先修订说 X；测得 Y」），从不静默改写。
- 引用文件与构造，从不引用行号（`File.v:N` 等）：它们会漂移；树已于 2026-09-17 清扫。点名所指定义、实例、字段、标志、记号或文首短文，读者可 grep。

下方地图——headline 开发所在；细节在 bullet。目录后跟星号表示其下全部文件；根文件后括号内 “+” glob 表示文件及其卫星。下列标题按目录分组地图，**不是**索引的节。`_CoqProject` 中每个文件都可从下方精确路径或 glob 到达。

### 理论核心 (`Theory/`、`Natural/`、`Functor/`、`Adjunction/`、`Monad/`、`Comonad/`)
- `Theory/Category.v`、`Theory/Functor.v`、`Theory/Natural/Transformation.v`（+ `Theory/Natural/Transformation/Arrows.v`）、`Natural/Transformation/*`、`Theory/Isomorphism.v`、`Theory/Morphisms.v`（+ `Theory/Morphisms/*`）：基于 setoid 的范畴与函子（Full/Faithful 闭包与反射）、分量与仅箭头呈现的自然变换、单/满演算及经 `C^op` 导出对偶的纪律。
- `Theory/Shapes.v`、`Theory/Diagram.v`（+ `Theory/Diagram/Examples.v`）、`Construction/PreorderReflection.v`：出自行走形状的函子、作为 quiver 同态且路径一般交换的图、普遍薄商。
- `Theory/Adjunction.v` 与 `Adjunction/*`：hom 集与单位/余单位伴随；共轭、mates 与伴随方块、带参数伴随、复合、RAPL/LAPC、加性、Paré 分裂判据、右侧伴随、由余单位决定、可表性、由单位与余单位的满与忠实、左伴随左逆、对角的伴随、GAFT 与 SAFT（解集 resizing 词汇在 `Adjunction/GAFT/Resize.v`；`Adjunction/SAFT/*` 含从良幂到 SAFT 子对象指标的桥等）、单位化、包络代数、余核对/等化子伴随。细节见 docs/INDEX.md 对应 bullet。
- `Instance/Adj.v`（+ `Instance/Adj/*`）、`Instance/Adjoints.v`：以共轭对为箭头的伴随范畴、两遗忘函子，以及范畴、伴随与共轭对的双范畴。
- `Theory/Monad.v`、`Monad/*`、`Comonad/*`：单子、强度、Kleisli 与 Eilenberg–Moore 分解及其极限、单子性（Beck）、两分解比较、Dubuc 提升、分次与交换单子、变换子、单子态射；对偶给出余单子及 co-Kleisli 与余代数 API。
- `Theory/Kan/Extension.v`、`Structure/Limit/Kan/Pointwise.v`：Kan 扩张（整体与局部）及逐点（余）极限公式。
- `Functor/Hom.v`、`Functor/Hom/Yoneda.v`（+ 卫星）、`Functor/Representable.v`（+ 卫星）等：Yoneda、可表性、hom 函子保持极限、转移引理等。
- `Theory/Universal/Element.v`、`Theory/Universal/Arrow.v`、`Theory/Density.v`、`Construction/Elements/Kan.v`：普遍元与普遍箭头、每个取值于集合的函子作为 representable 的余极限、Kan 余 Yoneda 形式。
- `Theory/Equivalence.v`、`Theory/Skeleton.v`、`Construction/Subcategory/Dense.v`：等价、骨骼、同构稠密满子范畴可反射。
- `Theory/Bicategory.v`、`Theory/TwoCategory.v`、`Theory/DoubleCategory.v` 及相关 Instance/Construction：双范畴、严格 2-范畴、伪双重范畴及 companions/conjoints。
- `Theory/Algebra/*`、`Theory/OGraph.v`、`Theory/EckmannHilton.v`、`Theory/Centre.v`：代数结构、O-图、Eckmann–Hilton、中心。
- `Theory/Metacategory.v`、`Theory/Lawvere.v`、`Theory/Multicategory.v` 及卫星：元范畴、Lawvere 理论、对称多范畴与 operad。
- `Theory/Concrete.v`、`Theory/Connected/Components.v`、`Theory/Size.v`、`Theory/Sieve.v`、`Theory/WeaklyInitial.v`：具体范畴、连通分量、大小词汇、筛、Freyd 初始对象构造。
- `Functor/Structure/*`、`Functor/Applicative.v`、`Functor/Strong.v` 等：函子结构层（幺半、笛卡尔、applicative、强函子等），支撑 `Theory/Coq/*`。

### 结构 (`Structure/`)
- 终/初/零对象、笛卡尔与余笛卡尔、闭、BiCCC、普遍性质。
- 极限/余极限及其保持、反射、创造；拉回、推出、等化子、余等化子。
- 幺半、辫、对称、闭幺半、星自治；预幺半与 Freyd 范畴。
- 加性脊柱：Ab 充实 → 双积 → 核 → 阿贝尔范畴。
- 正交分解、正则范畴；topos、子对象分类子、良幂、层。
- （余）端、双自然、双函子、Day 卷积。

### 构造 (`Construction/`)
- 对偶、积、余积、逗号、切片、箭头范畴、柱。
- 自由范畴/群胚/幺半、PROP、Karoubi、商、Cayley、提升。
- 子范畴、反射、局部化；Grothendieck、展示、纤维化；F-（余）代数、Lambek、Adámek；充实范畴；跨/共跨与装饰共跨。

### 具体实例 (`Instance/`)
- 集合与类型：`Sets`、`Coq`、`FinSet`、幂集、离散/非离散等。
- 代数：群、阿贝尔群、模、环、域、向量空间等。
- 序：预序、偏序、完备半格等。
- 拓扑与度量：`Top`、`Met` 及大量卫星（见 docs/INDEX.md / docs/AXIOMS.md）。
- 范畴的范畴与函子范畴：`Cat`、`StrictCat`、`Fun`、锥范畴。
- 其它：关系、命题、λ 演算、品种、ZX（唯一含 `Parameter` 的文件）等。

### 应用编程与工具 (`Theory/Coq/`、`Solver/`、`Tools/`、`Lib/`、`Test/`)
- `Theory/Coq/*`：把纯理论与实用 Coq 编程桥接。
- `Solver/*`：范畴等式的反射求解器。
- `Tools/Abstraction.v`、`Tools/Represented.v`：把 Coq 函数编译到笛卡尔闭组合子等。
- `Lib.v` 与 `Lib/*`：基础（setoid、`≈`、tactic、标志）。
- `Test/*`：`Fail` 探测与回归测试。

## 关键设计模式 (Critical Design Patterns)

### 优先等价而非相等 (Equivalence Over Equality)
态射上绝不要用 `=`，永远用 `≈`：
```coq
(* 错误 *)
Lemma foo : f ∘ id = f.

(* 正确 *)
Lemma foo : f ∘ id ≈ f.
```

### Proper 态射
所有运算必须尊重等价：
```coq
Program Instance Foo_Proper {C : Category} :
  Proper (equiv ==> equiv ==> equiv) (@foo C).
```

### 记号优先级
- `~>` 态射（level 90）
- `∘` 复合（level 40，左结合）
- `⟶` 范畴之间的函子
- `⟹` 自然变换

### 证明自动化
标准证明模式：
```coq
Proof.
  intros.
  cat.          (* 尝试化简 + 重写 *)
  proper.       (* 若证明 Proper *)
  equivalence.  (* 若证明 Equivalence *)
Qed.
```

## 常见开发任务 (Common Development Tasks)

### 添加新范畴实例
1. 定义对象与态射
2. 定义态射上的等价关系（setoid）
3. 证明它构成范畴（id、compose、定律）
4. 放入 Instance/ 目录
5. 加入 _CoqProject

### 证明函子性
1. 定义对象映射 F_obj
2. 定义态射映射 F_map
3. 证明 F_map 尊重等价
4. 证明 F 保持 id 与复合
5. 用 `Program Instance` 管理义务

### 建立伴随
1. 定义函子 F : C ⟶ D 与 G : D ⟶ C
2. 定义单位 η : Id ⟹ G ○ F
3. 定义余单位 ε : F ○ G ⟹ Id
4. 证明三角恒等式
5. 或使用 hom 集伴随定义

## 参考与学习 (References and Learning)

处理具体概念时参考：
- **nLab**：https://ncatlab.org/nlab/show/[concept_name]
- **README.md**：详细记号指南（「记号」节）
- **docs/AXIOMS.md**：公理审计
- **docs/INHABITATION.md**：哪些标题结果有树内具体见证
- **docs/INDEX.md**：分项开发索引
- **文件内背景短文**：多数旗舰概念文件在定义性文首之外还有历史/用途短文；接触陌生文件时先读该块。

## 版本 (Versioning)

默认版本：Rocq 9.1（flake.nix 中的 `default` 包）
支持：Coq 8.19–8.20，Rocq 9.0–9.1
部分内容需要 Equations（版本与 Coq 匹配）

## 测试个别定理 (Testing Individual Theorems)

测试特定构造：
```bash
# 提取所需文件
coqdep -R . Category Theory/MyConstruction.v | grep -v "^#"

# 先编译依赖
make Theory/Category.vo Theory/Functor.vo

# 再编译你的文件
coqc -R . Category Theory/MyConstruction.v
```

**中文翻译说明（zh-CN）**：本文已尽量全文译为简体中文；地图条目中的路径与标识符保持英文。更细的交付测量见 docs/INDEX.md。
