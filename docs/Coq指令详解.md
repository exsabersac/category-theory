# Coq 指令详解（category-theory）

面向 **Coq 小白**：按本仓库（`category-theory`）真实出现的 vernacular / 战术做扫描说明，每条固定五段——**做什么 / 常见语法 / 何时用·何时别用 / 仓库示例 / 易混点**。示例优先取自 `Theory/Category.v`、`Theory/Functor.v`、`Lib/*.v`、`Structure/*.v` 等较短可读片段。

- **分支**：`docs/coq-commands-guide`（从 `zh-CN` 分出，**不**并回 `zh-CN`；本文档不修改任何 `.v`）。
- **相关**：[`AUTOMATION.md`](AUTOMATION.md)（库自定义 tactic / hint DB）、[`NOTATION.md`](NOTATION.md)（记号）。
- **草稿溯源**：合并自 [`_drafts/part-A-vernac.md`](_drafts/part-A-vernac.md)、[`_drafts/part-B-tactics-core.md`](_drafts/part-B-tactics-core.md)、[`_drafts/part-C-logic-auto.md`](_drafts/part-C-logic-auto.md)。

## 阅读顺序

1. **Part A · Vernacular（结构声明）**：`Require` / `Class` / `Instance` / `Program` … ——先知道文件怎么搭起来。
2. **Part B · 核心战术**：`intros` / `rewrite` / `apply` / `destruct` … ——Proof 里最常用的手脚。
3. **Part C · 逻辑、自动化与查询**：`split` / `auto` / `Search` / `Check` … ——逻辑连接词、收尾自动化与查库。

本库同态相等几乎一律是 setoid `≈`（不是裸 `=`）；读 Part B 前先看该篇开头的「相等 ≈ setoid」说明。

---

# Part A：Vernacular（结构声明类）

## 0. 先分清：Class + Context（类型类风格）vs 普通 Record

本仓库几乎所有「范畴结构」都用 **`Class` + `Instance`/`Program Instance`**，再配合 **`Section`/`Context`** 把「当前范畴 `C`」等参数变成局部假设，而不是写成一个没有实例搜索的纯 `Record`。

`Theory/Category.v` 里已有【字段展开】注释（约 L72–L126），核心对照：

| 概念 | 做什么 | 本库用法 |
|------|--------|----------|
| `Inductive` | 可多构造子的数据类型 | 列表/语法树等（`Lib/MapDecide.v` 的 `term`） |
| `Record` | 单构造子 + 命名字段/投影 | 普通数据捆（`Lib/MapDecide.v` 的 `environment`） |
| `Class` | 在 Record 上再加 **类型类搜索** | `Category`、`Functor`、`Setoid`、`Terminal`… |
| `Instance` | 填某个 Class 的实现 | `hom_preorder`、`Functor_Setoid`… |
| `Context` | 在 Section 内声明隐式/显式参数 | `Context {C : Category}` |

阅读 `Category` 建议顺序（摘自字段展开注释）：

`obj → hom/homset → id/compose → Proper → 四条律`

`Structure/Terminal.v` 是「Class 包在 Section+Context 里」的典型短例：先 `Context {C : Category}`，再在该假设下声明 `Class Terminal`。

---

## 1. 装库与作用域

### `Require` / `Import` / `From … Require Export`

**做什么**

- `Require`：把已编译模块装进当前文件的依赖图；**默认不把名字引进当前命名空间**（多数名字仍要写长路径，或再 `Import`）。
- `Import`：把已 Require 的模块的短名（定义、记法、Hint 等，按导出规则）引进当前作用域。
- `Export`：像 Import，但**再导出给依赖本文件的下游**——下游 `Require Import 本文件` 时也会看到这些名字。
- `From X Require …`：从逻辑路径前缀 `X` 装模块（标准库常用 `From Coq Require …`）。

**常见语法**

```coq
Require Import Category.Lib.
Require Import Category.Theory.Category.
From Coq Require Export Program.
Require Export Category.Lib.Foundation.
Import ListNotations.
```

**何时用 / 何时别用**

- **用 `Require Import`**：本文件要直接写短名（几乎每个 `.v` 文件头）。
- **用 `Require Export`**：本文件是「门面」库（如 `Lib/Setoid.v` 导出 `Foundation`），让用户只 Require 你即可。
- **用 `From Coq Require Export Program`**：本库大量 `Program`/`Obligation`，在 `Lib/Foundation.v` 统一导出。
- **别**在业务文件里无环 `Require`；**别**滥用 `Export` 把整棵标准库再导出一遍（污染命名空间）。

**仓库示例**

```coq
(* Theory/Category.v *)
Require Import Category.Lib.

(* Theory/Functor.v *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Equations.Prop.Logic.

(* Lib/Foundation.v *)
From Coq Require Export Program.
From Coq Require Export CMorphisms.

(* Lib/Setoid.v *)
Require Export Category.Lib.Foundation.
```

**易混点**

- `Require` ≠ `Import`：只 Require 有时仍要写 `Module.Name`。
- `Import` ≠ `Export`：Import 只影响本文件；Export 影响下游。
- 逻辑路径 `Category.Theory.Category` 对应物理文件 `Theory/Category.v`（由 `_CoqProject`/`dune` 配置），不是任意文件夹名。

---

### `Open Scope`（及相关：`Declare` / `Delimit` / `Bind` / `Close Scope`）

**做什么**

- 记法（`Notation`）挂在 **scope** 上；`Open Scope foo_scope` 让该 scope 的记法在解析时优先可用。
- `Declare Scope`：登记一个新 scope 名。
- `Delimit Scope s with key`：允许写 `t%key` 强制进该 scope。
- `Bind Scope s with T`：类型为 `T` 的子项自动倾向 scope `s`。
- `Close Scope`：关掉某个已打开的 scope（本库关掉默认 `nat_scope`，避免数字记法抢优先级）。

**常见语法**

```coq
Declare Scope category_scope.
Delimit Scope category_scope with category.
Bind Scope category_scope with Category.
Open Scope category_scope.
Close Scope nat_scope.
```

**何时用 / 何时别用**

- **用**：引入 `~>`、`∘`、`≈`、`⟶` 等范畴记法前后，必须 Open 对应 scope。
- **别**：在不需要记法的纯计算文件里盲目 Open 一堆 scope（解析歧义难查）。

**仓库示例**

```coq
(* Lib/Foundation.v *)
Declare Scope category_theory_scope.
Delimit Scope category_theory_scope with category_theory.
Open Scope category_theory_scope.
Close Scope nat_scope.

(* Theory/Category.v *)
Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope morphism_scope.

(* Theory/Functor.v *)
Open Scope functor_type_scope.
Open Scope functor_scope.
```

**易混点**

- `Open Scope` 只影响**记法解析**，不装库。
- `x%category` 这种后缀来自 `Delimit Scope … with category`，与 `Open` 互补。
- `Reserved Infix`（见 `Category.v` 文件头）只占优先级，真正定义仍靠后面的 `Notation`。

---

## 2. 模块与 Section

### `Module` / `End`

**做什么**

把定义装进命名空间（可参数化），用 `End Name` 关闭。参数化模块像「函子模块」：给进其他 Module 类型，生成一套实现。

**常见语法**

```coq
Module Compat.
  Module Fake.
    (* … *)
  End Fake.
End Compat.

Module FMapExt (E : DecidableType) (M : WSfun E).
  Module P := WProperties_fun E M.
  (* … *)
End FMapExt.
```

**何时用 / 何时别用**

- **用**：隔离兼容层（`Lib/Tactics.v` 的 `Compat`）、封装 FMap 扩展（`Lib/FMapExt.v`）。
- **别**：把每个小 Lemma 都包成 Module（过重）；日常定理用 `Section` 通常更轻。

**仓库示例**

```coq
(* Lib/Tactics.v *)
Module Compat.
  Module Fake.
    Notation internal_eq_rew_r_dep := ltac:(fail "should not happen") (only parsing).
  End Fake.
  Module FromEqdepFactsIfExists.
    Import Fake.
    Import EqdepFacts.
    Notation eq_rew_r_dep := internal_eq_rew_r_dep.
  End FromEqdepFactsIfExists.
End Compat.

(* Lib/FMapExt.v *)
Module FMapExt (E : DecidableType) (M : WSfun E).
  Module P := WProperties_fun E M.
  Module F := P.F.
  (* … *)
End FMapExt.
```

**易混点**

- `Module M := …` 是**别名/应用**，不是新开可写模块体。
- `Section` 的变量在 `End` 后变成全称量化；`Module` 的名字则保留限定路径 `M.name`。

---

### `Section` / `End`

**做什么**

打开一段局部声明区：其中的 `Variable`/`Hypothesis`/`Context` 在 `End` 后自动泛化到定理/定义的前缀参数。

**常见语法**

```coq
Section Category.
Context {C : Category}.
Corollary dom_id {x : C} : dom (@id C x) = x.
Proof. auto. Qed.
End Category.
```

**何时用 / 何时别用**

- **用**：一长串引理共享同一 `C : Category`（`Theory/Category.v`、`Structure/Terminal.v`、`Theory/Functor.v` 的 `AFunctor`/`StrictEq`）。
- **别**：只有一条定义时硬套 Section（增加跳转成本）。

**仓库示例**

```coq
(* Theory/Category.v *)
Section Category.
Context {C : Category}.
Corollary id_unique_left {x : C} (u : x ~> x) :
  (∀ (y : C) (f : x ~> y), f ∘ u ≈ f) → u ≈ id.
Proof. intro H; rewrite <- (id_left u); apply H. Qed.
End Category.

(* Structure/Terminal.v *)
Section Terminal.
Context {C : Category}.
Class Terminal := {
  terminal_obj : C;
  one {x} : x ~> terminal_obj;
  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
}.
End Terminal.
```

**易混点**

- Section 名只是标签，不产生 `SectionName.foo` 路径（和 Module 不同）。
- `End` 必须与最近的 `Section`/`Module` 配对；嵌套时名字要匹配。

---

### `Context`

**做什么**

在 Section（或某些交互式目标）里声明一组参数/假设，可带 `{隐式}`、`` `(全称模式) ``、`[一般化]` 等绑定器语法；比反复写 `Variable` 更紧凑，且常与类型类一起用。

**常见语法**

```coq
Context {C : Category}.
Context {C D : Category}.
Context `{@Terminal C}.
```

**何时用 / 何时别用**

- **用**：类型类风格文件的标准开头（本库几乎处处如此）。
- **别**：在 Section 外滥用（语义与 Section 内不完全相同，新手易懵）。

**仓库示例**

```coq
(* Theory/Functor.v *)
Section AFunctor.
Context {C D : Category}.
Class AFunctor (F : C → D) : Type := { (* … *) }.
End AFunctor.

(* Structure/Terminal.v *)
Context {C : Category}.
```

**易混点**

- `Context {C : Category}`：`C` 对下游定义默认**隐式**（由类型推断）。
- `Context (C : Category)`：显式参数。
- 与 `Variable` 相近，但 `Context` 更常写类型类/`Setoid` 的反引号绑定器。

---

### `Variable` / `Hypothesis`

**做什么**

- `Variable`：在 Section 内声明一个（或若干）**类型参数/数据参数**。
- `Hypothesis`：声明一条**命题假设**（本质也是 Section 变量，只是命名意图是「假设」）。

`End` 后二者都会变成定理语句前的 `∀`。

**常见语法**

```coq
Variable A : Type.
Variable leA : A → A → Prop.
Hypothesis flip_involutive : ∀ (i j : A) (x : B i j), (* … *).
```

**何时用 / 何时别用**

- **用**：Section 内参数较多、或证明依赖额外公理/性质（`Lib/TList.v`、`Lib/NETList.v`、`Lib/Datatypes.v`）。
- **别**：可用 `Context {…}` 一次写清时仍拆成很多 `Variable`（风格不统一）。

**仓库示例**

```coq
(* Lib/Datatypes.v *)
Section Symmetric_Product2.
Variable A : Type.
Variable leA : A → A → Prop.
Inductive symprod2 : A * A → A * A → Prop := (* … *).
End Symmetric_Product2.

(* Lib/TList.v — Section TListProofsRev *)
Hypothesis flip_involutive : ∀ (i j : A) (x : B i j), (* … *).

(* Lib/FMapExt.v — Section for_all *)
Variable elt : Type.
Variable P : M.key → elt → bool.
Variable P_Proper : Proper (E.eq ==> eq ==> eq) P.
```

**易混点**

- `Hypothesis` 不会自动变成「公理」；只是 Section 假设，离开 Section 就成前提。
- 与文件顶层的 `Axiom`/`Parameter` 不同：后者是全局不透明假设，本库几乎不用。

---

## 3. 定义与数据类型

### `Definition`

**做什么**

给一个项（函数、值、类型表达式、证明项）起名。可透明（默认可 `unfold`），也可用证明模式填写。

**常见语法**

```coq
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].

Definition Build_Category' {obj} hom {homset} id compose
  {compose_respects} {id_left id_right comp_assoc} := {| … |}.
```

**何时用 / 何时别用**

- **用**：命名辅助构造子、缩写、非递归函数、打包 Record/Class 字段。
- **别**：需要结构递归时用 `Fixpoint`；需要多构造子类型时用 `Inductive`。

**仓库示例**

```coq
(* Theory/Category.v *)
Definition Build_Category'
           {obj} hom {homset} id compose
           {compose_respects}
           {id_left id_right comp_assoc} :=
  {| obj := obj; hom := hom; (* … *)
     comp_assoc_sym :=
       fun _ _ _ _ _ _ _ => symmetry (@comp_assoc _ _ _ _ _ _ _); |}.

(* Theory/Functor.v *)
Definition FAlgebra `(F : C ⟶ C) (a : C) := F a ~> a.

(* Structure/Terminal.v *)
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].
```

**易混点**

- `Definition` 体可以是证明脚本后再 `Defined`/`Qed`（见下文 Example）。
- `{| … |}` 是 Record/Class 构造语法，常与 `Definition`/`Program Definition` 连用。

---

### `Fixpoint`

**做什么**

定义**结构递归**函数；Coq 会检查终止性（通常按某归纳参数递减）。

**常见语法**

```coq
Fixpoint list_equiv `{Setoid A} (xs ys : list A) : Type :=
  match xs, ys with
  | nil, nil => True
  | x :: xs, y :: ys => x ≈ y ∧ list_equiv xs ys
  | _, _ => False
  end.
```

**何时用 / 何时别用**

- **用**：列表/依赖列表/语法树上的递归（`Lib/Datatypes.v`、`Lib/TList.v`、`Lib/MapDecide.v`）。
- **别**：非递归用 `Definition`；证明递归命题也可用 `Fixpoint`，但多数人更爱 `induction` 战术。

**仓库示例**

```coq
(* Lib/Datatypes.v *)
Fixpoint list_equiv `{Setoid A} (xs ys : list A) : Type := (* … *).

(* Lib/TList.v *)
Fixpoint tlist_length {i j} (xs : tlist B i j) : nat := (* … *).
Fixpoint tlist_concat {i j} (xs : tlist (tlist B) i j) : tlist B i j := (* … *).

(* Lib/MapDecide.v 还可 Program Fixpoint … {measure …} *)
```

**易混点**

- 终止性失败时不要硬写「假递归」；可用 `Program Fixpoint` + `measure`（见 `MapDecide.v`）或 `Equations`。
- `Fixpoint` 默认透明；证明想隐藏细节时用 `Qed` 结束的引理，而不是把证明写进 Fixpoint。

---

### `Inductive`

**做什么**

声明归纳类型（可多个构造子），同时生成归纳/递归原理。

**常见语法**

```coq
Inductive poly_unit@{u} : Type@{u} := ttt.

Inductive term : Set :=
  | Var   : positive → term
  | Value : N → term.
```

**何时用 / 何时别用**

- **用**：语法、树、有限枚举、依赖路径类型（`tlist'`/`netlist`）。
- **别**：只想捆字段、单构造子时优先 `Record`/`Class`（字段投影更友好）。

**仓库示例**

```coq
(* Lib/Setoid.v *)
Inductive poly_unit@{u} : Type@{u} := ttt.

(* Lib/MapDecide.v *)
Inductive term : Set :=
  | Var   : positive → term
  | Value : N → term.

(* Lib/TList.v *)
Inductive tlist' {A : Type} {B : A → A → Type} (k : A) : A -> Type := (* … *).
```

**易混点**

- `Class`/`Record` 在内核上也是归纳类型，但多了投影与（Class）实例搜索。
- 宇宙注解 `@{u}` 在本库很常见（`Set Universe Polymorphism`）。

---

### `Record`

**做什么**

单构造子归纳类型的语法糖：命名字段、自动投影、可用 `{| field := … |}` 构造。

**常见语法**

```coq
Record environment : Set := {
  vars : positive → N
}.
```

**何时用 / 何时别用**

- **用**：纯数据记录、不想参与类型类搜索时（`Lib/MapDecide.v`；`Functor/Bifunctor/Partial.v` 的 `RawLaws`）。
- **别**：需要自动找实例 / 当「结构字典」时用 `Class`（本库主流）。

**仓库示例**

```coq
(* Lib/MapDecide.v *)
Record environment : Set := {
  vars : positive → N
}.
```

**易混点**

- `Class` ≈ `Record` + 类型类机制；字段展开注释写得很清楚（`Theory/Category.v` L82–L87）。
- `Set Primitive Projections`（Foundation）让投影更「定义性」，影响证明中的简化。

---

## 4. 类型类：`Class` / `Instance` / `Existing Instance`

### `Class`

**做什么**

声明类型类：一组字段（数据 + 定律）。后续可用 `Instance` 注册实现；类型检查时 Coq 会搜索实例来填 `` `{Class} `` / `Class` 类型的隐式参数。

**常见语法**

```coq
Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};
  hom : obj → obj → uhom where "a ~> b" := (hom a b);
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);
  id {x} : x ~> x;
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);
  compose_respects {x y z} : Proper … (@compose x y z);
  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;
  (* … *)
}.
```

**何时用 / 何时别用**

- **用**：范畴、函子、Setoid、Terminal… 一切「可被搜索的结构」。
- **别**：完全不需要搜索的一次性数据包（用 `Record`）。

**仓库示例**

```coq
(* Theory/Category.v — 完整 Class Category，见 L128–L158 *)
(* Theory/Functor.v *)
Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} := {
  fobj : C → D;
  fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y;
  fmap_respects : ∀ x y, Proper … (@fmap x y);
  fmap_id {x : C} : fmap (@id C x) ≈ id;
  fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.

(* Lib/Setoid.v *)
Class Setoid A := {
  equiv : crelation A;
  setoid_equiv : Equivalence equiv
}.
```

**易混点**

- 定律也是字段：必须提供证明，且参与搜索（见 Category 字段展开 L75–L80）。
- `Class` 参数本身也可以是 `{C : Category}`：依赖已有实例。

---

### `Instance`

**做什么**

注册某个 `Class` 的实现。常配合 `Program Instance`：数据字段先填，证明字段变成 `Obligation`。

**常见语法**

```coq
Program Instance Functor_Setoid {C D : Category} : Setoid (C ⟶ D) := {
  equiv := (* … *)
}.
Next Obligation. (* 证明 Equivalence *) Qed.

Instance fobj_respects `(F : C ⟶ D) : (* … *).
```

**何时用 / 何时别用**

- **用**：为 `Setoid`/`Proper`/`Functor`/`PreOrder` 等提供全局或局部实例。
- **别**：一次性证明却建成全局 Instance（污染搜索，导致慢/歧义）。

**仓库示例**

```coq
(* Theory/Category.v *)
#[export]
Program Instance hom_preorder {C : Category} : PreOrder (@hom C) := {
  PreOrder_Reflexive  := fun _ => id;
  PreOrder_Transitive := fun _ _ _ f g => g ∘ f
}.

(* Theory/Functor.v *)
Program Instance Compose_respects {C D E : Category} :
  Proper … (@Compose C D E).
Next Obligation. (* … *) Qed.

(* Lib/Datatypes.v *)
#[global]
Program Instance list_setoid `{Setoid A} : Setoid (list A) := {
  equiv := list_equiv
}.
```

**易混点**

- `Program Instance` 与裸 `Instance`：前者把未填字段变成义务；本库大量使用前者。
- `#[export]` / `#[global]`：控制实例是否导出/全局可见（见 Local/Global 一节）。

---

### `Existing Instance`

**做什么**

某个项**已经是**某 Class 的实例（例如 Class 的字段本身是 `Setoid`/`Proper`），用本命令把它**登记进搜索数据库**，否则类型类解析找不到它。

**常见语法**

```coq
#[export] Existing Instance homset.
#[export] Existing Instance compose_respects.
#[export] Existing Instance setoid_equiv.
#[export] Existing Instance fmap_respects.
```

**何时用 / 何时别用**

- **用**：Class 字段里嵌了子 Class / `Proper`，需要下游自动用（本库模式极多）。
- **别**：对普通 Lemma 乱标 Existing Instance（类型不对会报错或行为怪异）。

**仓库示例**

```coq
(* Theory/Category.v *)
#[export] Existing Instance homset.
#[export] Existing Instance compose_respects.

(* Lib/Setoid.v *)
#[export] Existing Instance setoid_equiv.

(* Theory/Functor.v *)
#[export] Existing Instance fmap_respects.
```

**易混点**

- `Instance`：新建一项并注册；`Existing Instance`：已有项只注册。
- 漏写时典型症状：`Unable to satisfy the following constraints: Setoid ?A` / `Proper …`。

---

## 5. 定理外壳与证明结束方式

### `Theorem` / `Lemma` / `Example` / `Corollary`

**做什么**

四者在内核上几乎一样：都是命名一个类型为命题（或任意类型）的项，通常进入证明模式。差别主要是**文档意图**：

| 关键字 | 常见意图 |
|--------|----------|
| `Theorem` | 重要结果 |
| `Lemma` | 辅助引理 |
| `Corollary` | 直接推论 |
| `Example` | 用法演示 / 可计算实例 |

**常见语法**

```coq
Lemma fun_equiv_id_right {A B} (F : A ⟶ B) : F ◯ Id ≈ F.
Proof. construct; cat. Qed.

Corollary dom_id {x : C} : dom (@id C x) = x.
Proof. auto. Qed.

Example Build_Category'_Coq : Category.
Proof. (* … *) Defined.

Theorem Faithful_hom_action_injective : Faithful T → hom_action_injective.
Proof. (* … *) Qed.
```

**何时用 / 何时别用**

- **用**：按数学行文挑选关键字即可；本库 Corollary 极多（短性质），Lemma/Theorem 在 Functor 与 Hom 相关文件中常见。
- **别**：纠结「必须用 Theorem 才重要」——工具链不区分。

**仓库示例**

```coq
(* Theory/Functor.v *)
Lemma fun_equiv_id_left {A B} (F : A ⟶ B) : Id ◯ F ≈ F.
Proof. construct; cat. Qed.

Corollary fobj_Compose `(F : D ⟶ E) `(G : C ⟶ D) {x} :
  fobj[F ◯ G] x = fobj[F] (fobj[G] x).
Proof. reflexivity. Defined.

(* Theory/Category.v *)
Example Build_Category'_Coq : Category.
Proof. (* … *) Defined.

(* Functor/Hom/Induced.v *)
Theorem Faithful_hom_action_injective : Faithful T → hom_action_injective.
Proof. intros F a b f g H; exact (fmap_inj f g H). Qed.
```

**易混点**

- `Definition` 也可以陈述命题；用 Theorem/Lemma 只是习惯与检索友好。
- `Example` 常 `Defined`，方便后面计算/打印。

---

### `Proof` / `Qed` / `Defined` / `Admitted` / `Abort`

**做什么**

- `Proof.`：显式进入证明模式（可省略，但本库常用）。
- `Qed.`：保存证明并**不透明**（默认不可 `unfold` 该定理）。
- `Defined.`：保存证明并**透明**（可展开、可计算）。
- `Admitted.`：接受当前目标为公理（**跳过证明**）——仅草稿/暂缓。
- `Abort.`：放弃当前证明，**不产生**常量。

**常见语法**

```coq
Lemma foo : P.
Proof.
  (* tactics *)
Qed.

Example bar : T.
Proof.
  (* … *)
Defined.
```

**何时用 / 何时别用**

- **`Qed`**：普通数学证明（默认）。
- **`Defined`**：后面要计算、或作为 `Program`/`refine` 构造的一部分（如 `Build_Category'_Coq`、部分 `Corollary`）。
- **`Admitted`**：临时占位；**合并前应清掉**。
- **`Abort`**：交互试错；不要留在正式文件里。

**仓库示例**

```coq
(* Theory/Category.v — 透明例 *)
Example Build_Category'_Coq : Category.
Proof. (* … *) Defined.

(* Theory/Category.v — 不透明推论 *)
Corollary dom_id {x : C} : dom (@id C x) = x.
Proof. auto. Qed.

(* Theory/Functor.v — Defined 的短等式 *)
Corollary fobj_Compose … : …
Proof. reflexivity. Defined.
```

（本草稿扫描的优先文件中，正式路径很少长期留 `Admitted`/`Abort`；二者仍是标准 vernac，阅读 Coq 报错/教程时会遇到。）

**易混点**

- `Qed` 后不能依赖其证明体做计算；需要计算就 `Defined`。
- `Program` 的 `Next Obligation. … Qed.` 里，用 `Qed`/`Defined` 同样影响该义务的透明度。

---

## 6. 记法与参数声明

### `Notation`（及 `Infix` / `Reserved Infix`）

**做什么**

自定义语法糖，可挂到某个 scope，并设置优先级/结合性。

**常见语法**

```coq
Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : type_scope.

Infix "<$>" := fmap (at level 29, left associativity, only parsing) : morphism_scope.

Reserved Infix "~>" (at level 90, right associativity).
```

**何时用 / 何时别用**

- **用**：`~>`、`∘`、`≈`、`⟶`、`one[x]` 等提高可读性。
- **别**：无限制覆盖标准记法（本库用 `Local Set Warnings "-notation-overridden"` 有时是不得已）。

**仓库示例**

```coq
(* Theory/Category.v *)
Notation "x ~> y" := (@hom _%category x%object y%object) (* … *).
Notation "f ∘ g" := (* … *).

(* Lib/Setoid.v *)
Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

(* Theory/Functor.v *)
Notation "C ⟶ D" := (@Functor C%category D%category) (* … *).
```

**易混点**

- `only parsing`：只能读入，不用于打印。
- 记法里的 `%category` 依赖 `Delimit Scope`。
- Class 字段旁的 `where "a ~> b" := …` 是**局部**记法，与顶层 `Notation` 不同。

---

### `Arguments`

**做什么**

声明常量参数的**隐式/显式**状态，以及简化（`/`）时如何展开；也可绑定 scope（`%_category` 等）。

**常见语法**

```coq
Arguments fmap
  {C%_category D%_category Functor%_functor x%_object y%_object} f%_morphism.

Arguments Morphism_equality {_ _} _ _ /.
Arguments id_left {_%_category _%_object _%_object} _%_morphism.
```

**何时用 / 何时别用**

- **用**：压缩冗长宇宙/范畴参数；让 `simpl` 按 `/` 标记展开。
- **别**：把必要参数全隐式化导致推断失败。

**仓库示例**

```coq
(* Theory/Category.v *)
Arguments dom {_%_category _%_object _%_object} _%_morphism.
Arguments comp_assoc {_%_category _%_object _%_object _%_object _%_object}
  _%_morphism _%_morphism _%_morphism.

(* Lib/Foundation.v *)
Arguments Basics.compose {_ _ _} _ _ /.
```

**易混点**

- `{x}` 在类型里写隐式；`Arguments` 可事后改。
- `_` 在 Arguments 里表示「保持该位名称但按标记隐式」。
- `%_category` 形式是较新的 scope 标记写法（与 `%category` 相关）。

---

## 7. 可见性与选项：`Local` / `Global` / `Set` / `Unset`

### `Local` / `Global`（及属性 `#[export]`）

**做什么**

- `Local`：随后声明仅本模块/文件内有效（例如 `Local Set Warnings …`）。
- `Global`：强制全局（在 Section 内有时需要，避免 End 后丢失）。
- `#[export]`：导出给 Import 本文件的下游（实例、Hint 常用）。

**常见语法**

```coq
Local Set Warnings "-notation-overridden".
#[global] Program Instance list_setoid … 
#[export] Hint Rewrite @id_left : categories.
#[export] Existing Instance homset.
```

**何时用 / 何时别用**

- **`Local Set Warnings`**：只在本文件压警告。
- **`#[export] Instance/Hint`**：库代码默认导出。
- **`#[global] Instance`**：在 Section 外/需要明确全局时（`Lib/Datatypes.v`）。

**仓库示例**

```coq
(* Lib/Setoid.v *)
Local Set Warnings "-notation-overridden".

(* Lib/Datatypes.v *)
#[global]
Program Instance cons_respects {A} `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@cons A).

(* Theory/Category.v *)
#[export] Hint Rewrite @id_left : categories.
```

**易混点**

- Section 内的 `Instance` 默认行为与顶层不完全相同；拿不准就显式 `#[export]`/`#[global]`。
- `Local` 修饰 `Set` 与修饰 `Definition` 都成立，含义是「作用域局部」。

---

### `Set` / `Unset`

**做什么**

开关全局（或 Local）选项：宇宙多态、原始投影、Obligation 透明度、警告等。

**常见语法**

```coq
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Local Set Warnings "-notation-overridden".
```

**何时用 / 何时别用**

- **用**：每个核心 Lib 文件头几乎都有这三句（与本库 setoid/范畴编码配套）。
- **别**：在业务证明中途乱 `Set`/`Unset`（影响后续全部解释）。

**仓库示例**

```coq
(* Lib/Foundation.v / Lib/Setoid.v / Lib/Tactics.v *)
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
```

**易混点**

- `Unset Transparent Obligations`：Program 生成的义务证明默认**不透明**——符合数学库习惯。
- `Set Universe Polymorphism`：`Category@{o h p}` 这类宇宙参数才好用。

---

## 8. Program 义务机制（本库重点）

### `Program` / `Obligation` / `Next Obligation`

**做什么**

`Program Definition` / `Program Instance` / `Program Fixpoint` 允许你先写「带洞」的定义：能推断的字段自动填，剩下的证明责任变成 **Obligation**。然后：

- `Next Obligation.`：按顺序证明下一个义务；
- `Obligation n.`：点名第 n 个；
- 义务内用普通战术，以 `Qed`/`Defined` 结束。

**常见语法**

```coq
Program Definition terminal_unique {C : Category} (T1 T2 : @Terminal C) :
  @terminal_obj C T1 ≅ @terminal_obj C T2 := {|
  to   := @one C T2 (@terminal_obj C T1);
  from := @one C T1 (@terminal_obj C T2)
|}.
Next Obligation. apply (@one_unique C T2). Qed.
Next Obligation. apply (@one_unique C T1). Qed.

Program Instance funext_Setoid … := {| equiv := λ f g, ∀ x, f x ≈ g x |}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry; now apply X.
  - now rewrite X, X0.
Qed.
```

**何时用 / 何时别用**

- **用**：构造 `Category`/`Functor`/`Setoid`/`≅` 时——本库**默认风格**；`Lib/Foundation.v` 因此 `Require Export Program`。
- **别**：义务过多又无结构时，改用手写 `refine`/`unshelve` 可能更清晰；但新人应先熟悉 Program。

**仓库示例**

```coq
(* Theory/Functor.v *)
Program Definition Id {C : Category} : C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.

Program Definition Compose {C D E : Category}
  (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj[F] (fobj[G] x);
  fmap := fun _ _ f => fmap[F] (fmap[G] f)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. intros; rewrite !fmap_comp; reflexivity. Qed.

(* Structure/Terminal.v *)
Program Definition terminal_unique … := {| … |}.
Next Obligation. apply (@one_unique C T2). Qed.

(* Lib/FMapExt.v 亦见 Obligation 1. … 形式 *)
```

**易混点**

- `Program` 不是战术，是**vernacular 修饰符**。
- 义务顺序随字段/依赖变化；加字段后 `Next Obligation` 可能对不上，改用 `Obligation n` 或重新 Generate。
- 与 `Equations` 插件不同：本文件头有时 `Require Import Equations…`，那是另一套工具。

---

## 9. 自定义战术与 Hint

### `Ltac`

**做什么**

用 Ltac 语言定义可复用的战术宏（本 Part 只讲**声明**；具体子战术见 Part B）。

**常见语法**

```coq
Ltac comp_left :=
  try rewrite <- !comp_assoc;
  apply compose_respects; [reflexivity|].

Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).
```

**何时用 / 何时别用**

- **用**：重复出现的「结合律挪位置」「造 Functor」等套路（`Theory/Category.v`、`Theory/Functor.v`、`Lib/Tactics*.v`）。
- **别**：把一次性证明塞进巨型 Ltac（难维护、难读错误）。

**仓库示例**

```coq
(* Theory/Category.v *)
Ltac comp_left :=
  try rewrite <- !comp_assoc;
  apply compose_respects; [reflexivity|].
Ltac comp_right :=
  try rewrite !comp_assoc;
  apply compose_respects; [|reflexivity].

(* Theory/Functor.v *)
Ltac constructive := (* … *).
Ltac functor := unshelve (refine {| fobj := _; fmap := _ |}; simpl; intros).
```

**易混点**

- `Ltac` 是动态的，类型错误常延迟到运行时。
- `Tactic Notation`（见 `Foundation.v` 的 `given`）可自定义战术语法糖。

---

### `Hint`

**做什么**

向提示数据库注册：构造子、展开、重写、Extern 战术等，供 `auto`/`eauto`/`autorewrite`/`typeclasses eauto` 使用。本库大量使用自定义库 `cat` 与 `categories`。

**常见语法**

```coq
#[export] Hint Unfold Basics.compose : core.
#[export] Hint Rewrite @id_left : categories.
#[export] Hint Rewrite <- @comp_assoc : categories.
#[export] Hint Constructors Equivalence : core.
#[export] Hint Extern 1 (@equiv _ _ _ _) => reflexivity : cat.
#[export] Hint Immediate id : cat.
```

**何时用 / 何时别用**

- **用**：稳定、可逆的简化/重写（`id_left`/`id_right`）；结构化 Extern（`Lib/Tactics2.v`）。
- **别**：高代价 Extern 无条件扔进 `core`（拖慢全局 `auto`）。

**仓库示例**

```coq
(* Theory/Category.v *)
#[export] Hint Rewrite @id_left : categories.
#[export] Hint Rewrite @id_right : categories.

(* Lib/Foundation.v *)
#[export] Hint Unfold Basics.compose : core.

(* Lib/Tactics.v *)
#[export] Hint Constructors Equivalence : core.
#[export] Hint Unfold Reflexive : core.

(* Lib/Tactics2.v *)
Hint Extern 1 (@hom _ _ _) => compose_reduce : cat.
#[export] Hint Rewrite <- @comp_assoc : categories.
```

**易混点**

- `Hint Rewrite` 默认方向是左→右；反向写 `<-`。
- 数据库名：`core`、`cat`、`categories` 不同；`autorewrite with categories` 只看后者。
- 成本数字（`Extern 1` vs `Extern 40`）影响尝试顺序。

---

## 10. 强制转换与关系声明

### `Coercion`

**做什么**

声明一条**隐式强制转换**：需要类型 `B` 却给了 `A` 时，自动插入 `f : A → B`。本库用来把 `Category` 当成对象类型、`Functor` 当成对象函数。

**常见语法**

```coq
Coercion obj : Category >-> Sortclass.
Coercion fobj : Functor >-> Funclass.
Coercion setoid_equiv : Setoid >-> Equivalence.
Coercion FromAFunctor : AFunctor >-> Functor.
```

**何时用 / 何时别用**

- **用**：`x : C` 实为 `x : obj C`；`F x` 实为 `fobj F x`——大幅缩短陈述。
- **别**：链式 Coercion 过长（推断与打印变黑魔法）。

**仓库示例**

```coq
(* Theory/Category.v *)
Coercion obj : Category >-> Sortclass.

(* Theory/Functor.v *)
Coercion fobj : Functor >-> Funclass.
Coercion FromAFunctor : AFunctor >-> Functor.

(* Lib/Setoid.v *)
Coercion setoid_equiv : Setoid >-> Equivalence.
```

**易混点**

- `>-> Sortclass` / `Funclass` 是强制转换的**目标类**，不是普通类型名。
- Coercion 不改变内核项的真实类型，只影响读写与推断。

---

### `Proper` / `Equivalence`（作为实例目标）

**做什么**

二者来自标准库关系理论，本库通过 **`Instance`/`Program Instance`** 声明：

- `Equivalence R`：`R` 自反、对称、传递（Setoid 的心脏）。
- `Proper (R1 ==> R2 ==> …) f`：函数 `f` 尊重这些关系——**setoid rewriting** 的许可证。

它们不是独立的「定义命令」，但作为 **Instance 的目标类型** 在本库极高频，必须会认。

**常见语法**

```coq
Program Instance list_equivalence `{Setoid A} : Equivalence list_equiv.
Next Obligation. (* Reflexive *) Qed.
Next Obligation. (* Symmetric *) Qed.
Next Obligation. (* Transitive *) Qed.

Program Instance cons_respects {A} `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@cons A).

(* Class 字段里直接要求 Proper *)
compose_respects : Proper (equiv ==> equiv ==> equiv) (@compose x y z);
fmap_respects : Proper (equiv ==> equiv) (@fmap x y);
```

**何时用 / 何时别用**

- **用**：任何要在 `≈` 下 `rewrite` 的函数/运算；Category 的 `compose`、Functor 的 `fmap`、list 的 `cons`/`app`…
- **别**：只在 `=`（定义相等）世界里工作时尚可省略；本库几乎总在 setoid 世界。

**仓库示例**

```coq
(* Theory/Category.v 字段 *)
compose_respects {x y z} :
  Proper@{h p} (respectful@{h p h p h p} equiv
                  (respectful@{h p h p h p} equiv equiv))
    (@compose x y z);

(* Lib/Datatypes.v *)
#[global]
Program Instance list_equivalence `{Setoid A} : Equivalence list_equiv.
#[global]
Program Instance app_respects {A} `{Setoid A} :
  Proper (equiv ==> equiv ==> equiv) (@app A).

(* Theory/Functor.v *)
Global Instance proper_transport … : Proper … .
```

**易混点**

- `Equivalence` 是 Class；`Setoid` 包装了 `equiv` + `Equivalence` 实例（再 `Existing Instance setoid_equiv` / `Coercion`）。
- `Proper (equiv ==> equiv) f` 读作：若 `x ≈ y` 则 `f x ≈ f y`。
- 漏 `Proper` 实例时：`rewrite` 报 setoid 无法重写，而不是「等式不成立」。

---

## 11. 本库文件头常见「三件套」（速记）

几乎每个理论文件开头形如：

```coq
Require Import Category.Lib.
(* 或更多 Require *)
Generalizable All Variables.
Set Primitive Projections.          (* 常在 Lib 层已 Set *)
Set Universe Polymorphism.
Unset Transparent Obligations.
```

- `Generalizable All Variables`：允许 `` `{A} `` / `` `(f : x ~> y) `` 等绑定器自动推广变量（配合类型类风格）。
- 后三句选项见上文 `Set`/`Unset`。

---

## 12. 阅读路线（小白）

1. `Lib/Foundation.v`：Program 导出、记法 scope、`Hint Unfold`、`Arguments`。
2. `Lib/Setoid.v`：`Class Setoid`、`Existing Instance`、`Coercion`、`Program Instance`。
3. `Theory/Category.v`：字段展开注释 + `Class Category` + Section/Context + Example + Ltac。
4. `Theory/Functor.v`：`Program Definition Id/Compose` + `Next Obligation`。
5. `Structure/Terminal.v`：短 Class + Program 证同构唯一性。

---

*（Part A 完。战术级指令见 Part B；自动化与逻辑连接词战术见 Part C。）*

---

# Part B：核心战术

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

---

# Part C：逻辑战术 · 自动化 · 查询/求值

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

> **去重说明**：战术糖 `now tac`（≈ `tac; easy`）的专节见 **Part B · `now`**；本节只讲自动化族本身，对 `now` 仅作对照。

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
