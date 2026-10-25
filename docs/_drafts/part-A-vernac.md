# Part A：Vernacular（结构声明类）指令详解

> 草稿：只覆盖 **vernacular / 结构声明**（装库、模块、定义、证明外壳、记法、类型类、Program 等）。
> 战术脚本（`intros`/`rewrite`/`apply`…）见后续 Part B。
>
> 仓库：`category-theory`，分支：`docs/coq-commands-guide`。
> 示例优先取自 `Theory/Category.v`、`Theory/Functor.v`、`Lib/*.v`、`Structure/*.v`。
> **未修改任何 `.v` 文件。**

---

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
