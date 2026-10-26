Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Coq.
Require Import Category.Instance.AST.
Require Import Category.Tools.Represented.

Generalizable All Variables.

(** * Compiling Coq functions to cartesian-closed combinators / * 将 Coq 函数编译为笛卡尔闭合组合子 *)

(*
nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   Conal Elliott, “Compiling to Categories”, Proc. ACM Program. Lang. 1, ICFP
   (2017), 27:1–27:27. http://conal.net/papers/compiling-to-categories/

   By the Curry–Howard–Lambek correspondence the simply-typed lambda calculus is
   the internal language of cartesian closed categories: types are objects,
   pairing is the product, the function type is the exponential [z^y], lambda
   abstraction is [curry], and application is [eval]. A closed term of type
   [a → b] therefore denotes a morphism [repr a ~> repr b] in the free CCC
   ([AST]), and Elliott's “compiling to categories” is exactly this translation
   read as a program transformation.

   This file makes the translation's *correctness* explicit. Via [Repr] (see
   Tools/Represented) each Coq type [a] is represented by an object [repr a] and
   each value [x : a] by a global element [convert x : 1 ~> repr a]. A lambda
   term [lam : a → b] is correctly compiled to a combinator [ccc] when [convert]
   intertwines them — when applying [lam] then representing the result agrees
   with representing the argument then applying [ccc]:

       lam >==> ccc  :=  ∀ x, convert (lam x) ≈ ccc ∘ convert x

   i.e. [convert] is a homomorphism from the function [lam] to the arrow [ccc].
   The lemmas below are the per-construct compilation rules of [Compiling to
   Categories]: [ccc_id] (variable), [ccc_terminal] (unit introduction),
   [ccc_curry] (abstraction), and [ccc_apply]/[ccc_apply_pair] (application),
   each proving that the categorical combinator it names refines the source
   lambda. Composing these rules over the structure of a term compiles the whole
   term while preserving meaning.

--------
nLab：https://ncatlab.org/nlab/show/cartesian+closed+category
维基百科：https://en.wikipedia.org/wiki/Cartesian_closed_category

Conal Elliott，《编译到范畴》，见 ACM 程序设计语言会议论文集 1，ICFP（2017），27:1–27:27。http://conal.net/papers/compiling-to-categories/

根据 Curry–Howard–Lambek 对应关系，简单类型 λ 演算是笛卡尔闭范畴的内部语言：类型是对象，配对是积，函数类型是指数 [z^y]，λ 抽象是 [curry]，应用是 [eval]。因此，类型为 [a → b] 的闭项表示自由 CCC ([AST]) 中的一个态射 [repr a ~> repr b]，而 Elliott 的“编译到范畴”正是将这一定义作为程序转换的翻译。

此文件明确了翻译的*正确性*。通过 [Repr]（参见 工具/表示），每个 Coq 类型 [a] 由一个对象 [repr a] 表示，每个值 [x : a] 由一个全局元素 [convert x : 1 ~> repr a] 表示。当 [convert] 交织它们时，一个 lambda 项 [lam : a → b] 被正确编译为组合子 [ccc] —— 当应用 [lam] 后，再表示结果，与先表示参数再应用 [ccc] 是一致的：

lam >==> ccc  :=  ∀ x, convert (lam x) ≈ ccc ∘ convert x

即 [convert] 是从函数 [lam] 到箭头 [ccc] 的同态映射。以下引理是《编译到范畴》的每个结构的编译规则：[ccc_id]（变量）、[ccc_terminal]（单位引入）、[ccc_curry]（抽象）以及 [ccc_apply]/[ccc_apply_pair]（应用），每一个都证明其命名的范畴组合子细化了源 lambda。将这些规则在一个项的结构上组合，就可以在保持意义的同时编译整个项。
*)

Section Abstraction.

(*
The correctness relation for compiling a unary function [lam : a → b] to a
   combinator [ccc : repr a ~> repr b]: [convert] carries [lam] to [ccc].

--------
将一元函数 [lam : a → b] 编译为组合子 [ccc : repr a ~> repr b] 的正确性关系：[convert] 将 [lam] 转换为 [ccc]。
*)
Definition rel `{Repr a} `{Repr b}
           (lam : a → b) (ccc : repr a ~{AST}~> repr b) : Type :=
  ∀ x : a, convert (lam x) ≈ ccc ∘ convert x.

(*
The curried, binary variant: a function [lam : a → b → c] is compiled to an
   arrow into the exponential [repr c ^ repr b], and correctness is checked
   after [uncurry] against the represented pair [convert (x, y)].

--------
柯里化的二元变体：函数 [lam : a → b → c] 被编译为箭头进入指数 [repr c ^ repr b]，并在 [uncurry] 之后针对表示的对 [convert (x, y)] 检查正确性。
*)
Definition rel2 `{Repr a} `{Repr b} `{Repr c}
           (lam : a → b → c) (ccc : repr a ~{AST}~> repr c ^ repr b) : Type :=
  ∀ (x : a) (y : b), convert (lam x y) ≈ uncurry ccc ∘ convert (x, y).

Infix ">==>" := rel (at level 99) : category_scope.
Infix ">===>" := rel2 (at level 99) : category_scope.

(* Variable rule: the identity lambda [λx, x] compiles to the identity arrow. / 变量规则：身份 lambda [λx, x] 编译为身份箭头。 *)
Corollary ccc_id : ∀ `{Repr a}, (λ x : a, x) >==> id.
Proof. unfold rel; intros; cat. Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

(*
Pairing of global elements is the represented pair: this is the [convert] of
   [prod_Repr] (see Tools/Represented) holding definitionally.

--------
全局元素的配对是表示的对：这是 [convert] 的 [prod_Repr]（见工具/表示）按照定义保持的。
*)
Corollary convert_fork `{Repr a} `{Repr b} (x : a) (y : b) :
  convert x △ convert y ≈ convert (x, y).
Proof. reflexivity. Qed.

(*
Application rule: when [U] compiles to a curried arrow [U'] and [V] to [V'],
   the application [λx, U x (V x)] compiles to [eval ∘ U' △ V'] — feed the paired
   results of [U'] and [V'] to evaluation, exactly Elliott's [apply].

--------
应用规则：当 [U] 编译为一个柯里化箭头 [U'] 并且 [V] 编译为 [V'] 时，应用 [λx, U x (V x)] 编译为 [eval ∘ U' △ V']——将 [U'] 和 [V'] 的成对结果输入到求值中，完全按照 Elliott 的 [apply]。
*)
Theorem ccc_apply :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a → b → c) (U' : repr a ~{AST}~> repr c ^ repr b)
    (V : a → b) (V' : repr a ~{AST}~> repr b),
  U >===> U' ->
  V >==> V' ->
    (λ x, U x (V x)) >==> eval ∘ U' △ V'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrites.
  rewrite <- eval_first.
  comp_left.
  unfold first.
  rewrite <- fork_comp.
  rewrite <- comp_assoc.
  rewrite <- convert_fork; cat.
Qed.

(*
Application rule with an uncurried callee [U : a * b → c]: the argument is
   paired with the input via [id △ V'] before applying [U'].

--------
带有未柯里化被调用函数 [U : a * b → c] 的应用规则：在应用 [U'] 之前，参数通过 [id △ V'] 与输入配对。
*)
Theorem ccc_apply_pair :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b → c) (U' : repr a × repr b ~{AST}~> repr c)
    (V : a → b) (V' : repr a ~{AST}~> repr b),
  U >==> U' ->
  V >==> V' ->
    (λ x, U (x, V x)) >==> U' ∘ id △ V'.
Proof.
  unfold rel; intros ??????? U' V; subst; intros.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite id_left.
  rewrites.
  rewrite convert_fork.
  reflexivity.
Qed.

(*
Abstraction rule: an inner lambda [λy, U (x, y)] compiles by currying the
   uncurried combinator [U'], so [λx, λy, U (x, y)] compiles to [curry U'].

--------
抽象规则：一个内部 lambda [λy, U (x, y)] 通过对未柯里化的组合子 [U'] 进行柯里化来编译，因此 [λx, λy, U (x, y)] 编译成 [curry U']。
*)
Theorem ccc_curry :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b → c) (U' : repr a × repr b ~> repr c),
    U >==> U' ->
      (λ x, λ y, U (x, y)) >===> curry U'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite uncurry_curry.
  apply X.
Qed.

(*
Unit-introduction rule: the constant [tt] map compiles to the unique arrow
   [one] into the terminal object, by [one_unique].

--------
单元介绍规则：常量 [tt] 映射编译为唯一箭头 [one] 到终端对象，由 [one_unique] 完成。
*)
Theorem ccc_terminal : ∀ `{Repr a},
  (λ _ : a, tt) >==> one.
Proof.
  unfold rel; simpl; intros; cat.
  apply one_unique.
Qed.

(*
Logical bookkeeping: a non-dependent hypothesis [a] commutes past a universal
   quantifier in both directions (the curry/uncurry of implications).

--------
逻辑记账：一个非依赖假设 [a] 在两个方向上与全称量词对换（蕴含的柯里化/去柯里化）。
*)
Lemma distribute_forall : ∀ a {X} P, (a → ∀ (x : X), P x) → (∀ x, a → P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Lemma forall_distribute : ∀ a {X} P, (∀ x, a → P x) → (a → ∀ (x : X), P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

End Abstraction.

(*
A cartesian category equipped with a distinguished “numbers” object and an
   addition arrow on it — the minimal structure needed to compile arithmetic
   expressions. [Coq_Numerical] below realises it with [nat] and [Nat.add], and
   any model interpreting [AST] into such a category gives meaning to numeric
   programs.

--------
一个笛卡尔范畴，配备了一个特殊的“数字”对象及其上的加法箭头——编译算术表达式所需的最小结构。下面的 [Coq_Numerical] 使用 [nat] 和 [Nat.add] 实现了它，任何将 [AST] 解释为这样的范畴的模型，都为数值程序赋予了意义。
*)
Class Numerical (C : Category) `{@Cartesian C} := {
  numerical_obj : obj;
  add : numerical_obj × numerical_obj ~> numerical_obj
}.

Section NumericalFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Numerical C _}.
Context `{@Cartesian D}.
Context `{@Numerical D _}.
Context `{@CartesianFunctor _ _ F _ _}.

(*
A (cartesian) functor preserving the numerical structure: it identifies the
   source and target number objects ([map_num]) and carries source addition to
   target addition coherently with the product comparison [prod_out]. This lets
   addition be transported along [F], so [fmap add] is computed in the target.

--------
保持数值结构的（笛卡尔）函子：它识别源和目标的数对象（[map_num]），并将源加法一致地映射到目标加法，与乘积比较 [prod_out] 一致。这使得加法可以沿着 [F] 传递，因此 [fmap add] 可以在目标中计算。
*)
Class NumericalFunctor := {
  map_num : numerical_obj ≅ F numerical_obj;

  fmap_add :
    fmap add ≈ map_num ∘ @add D _ _ ∘ split (map_num⁻¹) (map_num⁻¹)
                       ∘ @prod_out _ _ F _ _ _ numerical_obj numerical_obj
}.

End NumericalFunctor.

#[export]
Instance Coq_Numerical : @Numerical Coq Coq_Cartesian := {
  numerical_obj := nat;
  add := Datatypes.uncurry Nat.add
}.

Section Example.

Infix ">==>" := rel (at level 99) : category_scope.

(*
Theorem ccc_arity2 :
  ∀ (a b c : Type)
    (f : a → b) (f' : F a ~> F b)
    (g : a → b) (g' : F a ~> F b)
    (p : b → b → c) (p' : F b ~> F c ^ F b),
  f >==> f' ->
  g >==> g' ->
  p >==> exp_in ∘ p' ->
  (λ x : a, p (f x) (g x)) >==> uncurry p' ∘ f' △ g'.
Proof.
Abort.

Theorem ccc_plus :
  ∀ (f : nat → nat) (f' : F nat ~> F nat)
    (g : nat → nat) (g' : F nat ~> F nat),
  f >==> f' ->
  g >==> g' ->
  (λ x : nat, (f x + g x)%nat)
    >==> map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹) ∘ f' △ g'.
Proof.
  intros.
  pose proof (ccc_arity2 nat nat nat f f' g g' Nat.add
                         (curry (map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹)))
                         X X0).
  simpl in X1.
  unfold rel in *; repeat intros.
  rewrite uncurry_curry in X1.
  rewrites; [reflexivity|]; clear X1.
  pose proof (@fmap_add Coq _ _ _ _ _ _ _ _) as HA.
  simpl in HA.
  assert (Nat.add = prod_uncurry (λ p : nat * nat, (fst p + snd p)%nat)) by auto.
  rewrites.
Abort.

--------
定理 ccc_arity2 ：
  对于所有 (a b c : 类型)
    (f : a → b) (f' : F a ~> F b)
    (g : a → b) (g' : F a ~> F b)
    (p : b → b → c) (p' : F b ~> F c ^ F b)，
  如果 f >==> f' ，
  g >==> g' ，
  p >==> exp_in ∘ p' ，
  则 (λ x : a, p (f x) (g x)) >==> uncurry p' ∘ f' △ g'。
证明。
放弃。

定理 ccc_plus ：
  对于所有的 (f : nat → nat) (f' : F nat ~> F nat)
    (g : nat → nat) (g' : F nat ~> F nat)，
  如果 f >==> f' 且
  g >==> g'，则有
  (λ x : nat, (f x + g x)%nat)
    >==> map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹) ∘ f' △ g'。
证明。
  引入假设。
  使用定理 (ccc_arity2 nat nat nat f f' g g' Nat.add
                         (curry (map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹)))
                         X X0) 得到证明。
  在 X1 中化简。
  展开 rel 在所有地方；重复引入。
  在 X1 中使用 uncurry_curry 重写。
  重写；使用 [reflexivity|]；清理 X1。
  使用 (@fmap_add Coq _ _ _ _ _ _ _ _) 得到 HA。
  在 HA 中化简。
  声明 (Nat.add = prod_uncurry (λ p : nat * nat, (fst p + snd p)%nat)) 并自动证明。
  重写。
放弃。
*)

(* f : A -->[Setoid] R / f : A -->[Setoid] R *)
(* g : A -->[Setoid] R / g : A -->[Setoid] R *)
(* + : R * R -->[Setoid] R *)
(* ============== *)
(* lambda x. f x + g x  : A -->[Setoid] R / lambda x. f x + g x  : A -->[Setoid] R *)

(* Definition generic_add := fmap Nat.add. / 定义 generic_add := fmap Nat.add。 *)

End Example.

(* Eval simpl in @generic_add. / 在 @generic_add 中进行简单评估。 *)
