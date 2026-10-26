Require Import Category.Lib.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(* * * Derived operators: the clone of a signature / * * 派生运算符：签名的克隆 *)

(*
 nLab:      https://ncatlab.org/nlab/show/clone
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
 Wikipedia: https://en.wikipedia.org/wiki/Clone_(algebra)

 Mac Lane §V.6, book p. 124 (PDF p. 133), the definition of a DERIVED
 OPERATOR.  The derived operators of a type close the given operations
 under composition and substitution, and Mac Lane's point is that the
 action of the clone on any algebra is already determined by the action
 of the basic operations: every action of Ω extends uniquely to an
 action of Λ.

 ** What the tree had, measured

 Nothing arity-graded with a substitution action.  Instance/Comp.v's
 [Tree] is a term over a WHOLE variable type, not an operator of a
 specific arity, and names no composition or substitution operation.
 Construction/PROP/Term.v's [Term] is arity-graded and closes under
 composition, tensor and braids, but NOT under substitution along an
 arbitrary function between finite arities — braids are bijections, and
 Mac Lane's substitution duplicates and deletes variables.

 ** The index type costs nothing

 [Fin.t] is already in scope everywhere: Lib/Setoid.v requires
 Coq.Vectors.Fin and defines [Fin_Setoid], and every file in
 _CoqProject requires Category.Lib.  So grading on [Fin.t n] and
 substituting along an ARBITRARY [Fin.t m → Fin.t n] adds no [Require].
 Instance/FinSet.v is built on exactly this shape, which is to say
 the tree's own [FinSet] already IS “arbitrary maps between finite
 arities”.

 ** Substitution is the free-algebra universal property, not a new
 recursion

 [clone_subst] is [induced_map] at the free algebra on the target
 arity.  That makes HALF of the issue's phrase “recovering
 [induced_hom] / [from_free_unique] as the free-algebra instance”
 literally true rather than a remark: substitution IS the induced
 homomorphism's underlying map, and renaming is substitution by
 variables.  The other half is NOT delivered and an audit was right to
 say so — [from_free_unique] is not recovered here at all.  Its
 analogue is [action_extends_to_clone] below, which is a different
 statement (uniqueness of an ACTION extending the basic operations, in
 setoid form) rather than that constant re-derived.

 ** The unique-extension theorem, in two forms, and why

 The theorem is shipped TWICE, and the difference is the whole point of
 the file's discipline.

 [action_extends_to_clone] — the name the issue's Verification block
 checks — is stated against a [SetoidAction]: a carrier with a setoid,
 operations, and an argumentwise-congruence field [sact_op_respects].
 It is CLOSED UNDER THE GLOBAL CONTEXT.

 [action_extends_to_clone_leibniz] is the same theorem with [=] for `≈`
 and no congruence field, and it reports
 [functional_extensionality_dep].  It cannot avoid it: the inductive
 step compares [op A o (fun j => F (args j) env)] with
 [op A o (fun j => clone_act (args j) env)], two argument bundles that
 the induction hypothesis makes pointwise equal and that are not
 convertible.  That is the identical wall as Instance/Comp.v's
 [from_free_unique], whose own marker comment already names the
 cure.

 Nothing is smuggled by the setoid form.  [sact_op_respects] is
 precisely what [functional_extensionality] supplies for [eq_Setoid], so
 the setoid statement is strictly more general and strictly weaker in
 assumptions — which is why it, and not the Leibniz shadow, carries the
 headline name.  Only the axiom-free constants are gated;
 docs/AXIOMS.md records the two that are not.

 ** Not delivered

 No setoid on [Tree] itself — the cure Instance/Comp.v proposes.
 AN EARLIER REVISION OF THIS PARAGRAPH GAVE A REASON THAT IS WRONG, and
 it is corrected here rather than quietly dropped.  It said such a
 congruence “risks pulling in [Eqdep]/[JMeq_eq]”, because transitivity
 would have to invert [tree_equiv (node o k) (node o' k')] and so want
 injectivity of [existT] on an [operation S] with no decidable
 equality.  Measured: there is no such risk.  Making symmetry and
 transitivity CONSTRUCTORS of the inductive rather than theorems means
 no inversion is ever performed, and reflexivity is then derived by
 plain induction on the tree; the whole thing is Closed under the
 global context.  (It must be [Type]-valued rather than [Prop]-valued,
 since [Setoid]'s [equiv] is a crelation.)  CORRECTION (#450): that
 parenthesis is wrong.  Instance/Variety/Free.v's [tree_equiv], a
 congruence of exactly the kind described, is [Prop]-valued since #450
 ([About tree_equiv] ends in [→ Prop]), and a [crelation] field accepts a
 [Prop]-valued relation by cumulativity; Free.v's CORRECTION (#450)
 under “The congruence on terms is axiom-free” gives the account.

 The honest reason it is absent is simply that this file does not need
 it: what the clone's unique-extension theorem needs is a setoid on the
 TARGET of an action, which is what [SetoidAction] supplies, and the
 congruence generated by [E] on terms belongs to the free-algebra
 construction rather than here.

 THAT CONSTRUCTION HAS SINCE LANDED, which settles the correction above
 rather than leaving it as an argument: Instance/Variety/Free.v's
 [tree_equiv] is exactly the congruence this block declined, it takes
 symmetry and transitivity as constructors precisely as described, and
 it is Closed under the global context — as is everything built on it
 up to [Free_Variety_adjunction].  No clone as a CATEGORY and so
 no Lawvere theory — see the closing comment of Instance/Variety.v. 

 --------
 nLab：       https://ncatlab.org/nlab/show/clone
 nLab：       https://ncatlab.org/nlab/show/Lawvere+theory
 维基百科：  https://en.wikipedia.org/wiki/Clone_(algebra)

 Mac Lane §V.6，书本第124页（PDF第133页），DERIVED OPERATOR 的定义。某类型的导出算子在组合和替换下封闭给定的操作，而 Mac Lane 的观点是，克隆在任何代数上的作用已经由基本操作的作用决定：Ω 的每个作用都唯一地扩展为 Λ 的作用。

 ** 树上有什么，被测量没有对替代操作进行算子元数分级。Instance/Comp.v 中的 [Tree] 是一个整体变量类型上的项，而不是特定算子元数的运算符，也不表示任何组合或替代操作。Construction/PROP/Term.v 中的 [Term] 进行了算子元数分级，并在组合、张量和编织下闭合，但不在沿有限元数之间的任意函数进行的替代下闭合——编织是双射，而 Mac Lane 的替代会复制和删除变量。

 ** 索引类型不耗费任何成本[Fin.t] 已经在任何地方都有作用域：Lib/Setoid.v 需要 Coq.Vectors.Fin 并定义了 [Fin_Setoid]，并且 _CoqProject 中的每个文件都需要 Category.Lib。因此，对 [Fin.t n] 进行评分并沿着任意 [Fin.t m → Fin.t n] 进行替换不会增加任何 [Require]。Instance/FinSet.v 就是基于这种结构构建的，也就是说树本身的 [FinSet] 已经是“有限元类型之间的任意映射”。

 **替换是自由代数的泛性质，而不是一种新的递归[clone_subst] 在目标运算元上的自由代数中是 [induced_map]。 这使得问题短语的一半“恢复 [induced_hom] / [from_free_unique] 作为自由代数实例”字面上是真的，而不是一个评论：替换确实是诱导同态的底层映射，而重命名是通过变量进行替换。另一半没有实现，审计指出此点是正确的——[from_free_unique] 在这里根本没有恢复。它的对应物是下面的 [action_extends_to_clone]，它是一个不同的陈述（扩展基本运算的 ACTION 的唯一性，以集合体形式表示），而不是重新推导该常数。

 ** 唯一扩展定理，两种形式，以及原因

 该定理被发表了两次，而其中的区别正是文件规范的关键所在。[action_extends_to_clone] —— 此名称由该问题的验证块检查 —— 是针对 [SetoidAction]：具有集合类型、操作和逐参数同余字段 [sact_op_respects] 的载体而声明的。它在全局上下文下是封闭的。

 [action_extends_to_clone_leibniz] 是相同定理，对于 `≈` 使用 [=]，但没有同余字段，并且它报告 [functional_extensionality_dep]。它无法避免：归纳步骤将 [op A o (fun j => F (args j) env)] 与 [op A o (fun j => clone_act (args j) env)] 进行比较，这两个参数集合在归纳假设下逐点相等，但不可转换。这与 Instance/Comp.v 中的 [from_free_unique] 完全相同，其自身的标记注释已经命名了解决方法。没有任何东西是由集合形式走私的。[sact_op_respects] 正是 [functional_extensionality] 为 [eq_Setoid] 提供的，因此集合声明在假设上严格更一般且严格更弱——这就是为什么它，而不是莱布尼茨影子，拥有主要名称的原因。只有无公理的常量是受限制的；docs/AXIOMS.md 记录了两个不受限制的常量。

 ** 未交付在 [Tree] 本身上没有设定——Instance/Comp.v 提出的解决方法。这个段落的早期版本给出了一个错误的原因，这里进行了更正，而不是悄悄删除。它说这种等价关系“有可能牵扯到 [Eqdep] / [JMeq_eq]”，因为传递性将不得不反转 [tree_equiv (node o k) (node o' k')]，因此需要 [existT] 在一个没有可判定相等性的 [operation S] 上的单射性。经过衡量：不存在这种风险。将对称性和传递性作为归纳类型的构造子而不是定理意味着永远不会执行反转，然后通过对树的普通归纳推导自反性；整个过程在全局上下文下是封闭的。（它必须是 [Type] 值，而不是 [Prop] 值，因为 [Setoid] 的 [equiv] 是一个 crelation。）更正（#450）：那个括号是错误的。Instance/Variety/Free.v 的 [tree_equiv]，一个完全符合所描述类型的同余，自 #450（[About tree_equiv] 以 [→ Prop] 结尾）以来是 [Prop] 值，并且 [crelation] 域通过累积性接受一个 [Prop] 值的关系；Free.v 的“术语上的同余无需公理”下的更正（#450）给出了说明。

 它缺失的真实原因只是因为这个文件不需要它：克隆的唯一扩展定理所需要的是作用目标上的一个集合，这是 [SetoidAction] 提供的，而由 [E] 在术语上生成的同余属于自由代数构造而不是这里。该构造自那时以来已经发布，它解决了上述修正，而不是将其作为一个论点保留：Instance/Variety/Free.v 的 [tree_equiv] 正是这个模块拒绝的同余，它以精确描述的方式将对称性和传递性作为构造子，并且在全局上下文下是封闭的——正如基于它构建的所有内容直到 [Free_Variety_adjunction] 一样。没有作为范畴的克隆，因此没有 Lawvere 理论——参见 Instance/Variety.v 的结束评论。
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Clone.

Context (S : UA.OpSignature).

(* * ** The arity-graded derived operators / * ** 按元数分级的派生运算符 *)

Definition DerivedOperators (n : nat) : Type := UA.Tree S (Fin.t n).

Definition clone_var {n} (i : Fin.t n) : DerivedOperators n :=
  UA.generator S (Fin.t n) i.

Definition clone_op {n} (o : UA.operation S)
  (args : UA.arity o → DerivedOperators n) : DerivedOperators n :=
  UA.node S (Fin.t n) o args.

(* * ** Closure under substitution, along an ARBITRARY map of arities [clone_subst] is Instance/Comp.v's [induced_map] at the free algebra on [Fin.t n]; [clone_rename] is substitution by variables, and it is where “arbitrary function between finite arities” — duplication and deletion included, not merely a braid — enters. / * ** 在替换下的封闭性，沿着任意的元数映射 [clone_subst] 是 Instance/Comp.v 中的 [induced_map] 在 [Fin.t n] 自由代数上的实例；[clone_rename] 是变量的替换，并且它是“有限元数之间的任意函数” — 包括复制和删除，而不仅仅是编排 — 的应用场所。 *)

Definition clone_subst {m n} (s : Fin.t m → DerivedOperators n)
  : DerivedOperators m → DerivedOperators n :=
  UA.induced_map S (Fin.t m) (UA.Free S (Fin.t n)) s.

Definition clone_rename {m n} (phi : Fin.t m → Fin.t n)
  : DerivedOperators m → DerivedOperators n :=
  clone_subst (fun i => clone_var (phi i)).

(* * ** Actions, up to a setoid on the target / * ** 动作，取决于目标上的集合关系 *)

Record SetoidAction := {
  sact_carrier : Type;
  sact_setoid  : Setoid sact_carrier;
  sact_op      : ∀ o : UA.operation S,
                  (UA.arity o → sact_carrier) → sact_carrier;

  (* the congruence field that replaces functional extensionality / 替代函数外延性的同余场 *)
  sact_op_respects : ∀ (o : UA.operation S) (k1 k2 : UA.arity o → sact_carrier),
    (∀ j, @equiv _ sact_setoid (k1 j) (k2 j)) →
    @equiv _ sact_setoid (sact_op o k1) (sact_op o k2)
}.

(*
 A [#[local]] notation, and it SHADOWS Theory/Category.v's
 [x ≈[ C ] y] for morphism equivalence in a named category, for the
 remainder of this section.  That is harmless here — this file never
 compares morphisms of a category — and the [#[local]] keeps it out of
 every other file, but it is worth knowing before copying the idiom
 somewhere that does. 

 --------
 [#[local]] 符号，它在本节的其余部分中表示命名范畴中态射的等价性，对应 Theory/Category.v 的 [x ≈[ C ]y]。这里无害——这个文件从不比较一个范畴的态射——而 [#[local]] 将它排除在其他文件之外，但在将这个惯用法复制到其他地方之前值得了解。
*)
#[local] Notation "x ≈[ A ] y" := (@equiv _ (sact_setoid A) x y)
  (at level 79, only parsing).

(* Every [SetoidAction] has an underlying [OpAlgebra]: the setoid and its congruence field are extra structure, not a weakening. / 每一个 [SetoidAction] 都有一个潜在的 [OpAlgebra]：集合论和其同余场是额外的结构，而不是一种弱化。 *)
Definition sact_alg (A : SetoidAction) : UA.OpAlgebra S :=
  {| UA.carrier := sact_carrier A ; UA.op := sact_op A |}.

Fixpoint clone_act {n} (A : SetoidAction) (t : DerivedOperators n)
  (env : Fin.t n → sact_carrier A) : sact_carrier A :=
  match t with
  | UA.generator _ _ i    => env i
  | UA.node _ _ o args => sact_op A o (fun j => clone_act A (args j) env)
  end.

(*
 Both computation rules hold definitionally; [reflexivity] is not
 hiding a rewrite. 

 --------
 两个计算规则在定义上都是成立的；[reflexivity] 并没有隐藏重写。
*)

Lemma clone_act_var {n} (A : SetoidAction) (i : Fin.t n)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_var i) env ≈[A] env i.
Proof. reflexivity. Qed.

Lemma clone_act_op {n} (A : SetoidAction) (o : UA.operation S)
  (args : UA.arity o → DerivedOperators n)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_op o args) env
    ≈[A] sact_op A o (fun j => clone_act A (args j) env).
Proof. reflexivity. Qed.

(*
   * ** Mac Lane's theorem: the action of Ω determines the action of Λ

   Any operator [F] that acts like the variables on variables and like
   the basic operations on nodes agrees with [clone_act] everywhere.
   AXIOM-FREE: the inductive step closes with [sact_op_respects] where the
   Leibniz form below must close with functional extensionality. 

   --------
   * ** 麦克莱恩定理：Ω 的作用决定 Λ 的作用

   任何像变量作用于变量一样作用的运算符 [F]，以及像基本运算作用于节点一样作用的运算符，都在任何地方与 [clone_act] 一致。
   无公理：归纳步骤在 [sact_op_respects] 处结束，其中下面的莱布尼茨形式必须通过函数外延性闭合。
*)

Theorem action_extends_to_clone (A : SetoidAction)
  (F : ∀ n, DerivedOperators n → (Fin.t n → sact_carrier A) → sact_carrier A)
  (Hvar : ∀ n (i : Fin.t n) env, F n (clone_var i) env ≈[A] env i)
  (Hop : ∀ n (o : UA.operation S) (args : UA.arity o → DerivedOperators n) env,
           F n (clone_op o args) env
             ≈[A] sact_op A o (fun j => F n (args j) env)) :
  ∀ n (t : DerivedOperators n) env, F n t env ≈[A] clone_act A t env.
Proof.
  intros n t.
  induction t as [i | o args IH]; intro env.
  - apply Hvar.
  - rewrite (Hop n o args env).
    apply sact_op_respects.
    intro j.
    apply IH.
Qed.

(* * ** The substitution and renaming laws for the action / * ** 行动的替代和重新命名法律 *)

Lemma clone_act_subst {m n} (A : SetoidAction)
  (s : Fin.t m → DerivedOperators n) (t : DerivedOperators m)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_subst s t) env
    ≈[A] clone_act A t (fun i => clone_act A (s i) env).
Proof.
  induction t as [i | o args IH]; simpl.
  - reflexivity.
  - apply sact_op_respects.
    intro j.
    apply IH.
Qed.

Lemma clone_act_rename {m n} (A : SetoidAction)
  (phi : Fin.t m → Fin.t n) (t : DerivedOperators m)
  (env : Fin.t n → sact_carrier A) :
  clone_act A (clone_rename phi t) env
    ≈[A] clone_act A t (fun i => env (phi i)).
Proof. apply clone_act_subst. Qed.

End Clone.

Arguments clone_var {_ _} _.
Arguments clone_op {_ _} _ _.
Arguments clone_subst {_ _ _} _ _.
Arguments clone_rename {_ _ _} _ _.
Arguments sact_carrier {_} _.
Arguments sact_op {_} _ _ _.
Arguments clone_act {_ _} _ _ _.

(*
   * ** The Leibniz shadows, and their cost

   Shipped so the comparison is available in the tree rather than only in
   this header, and named so that no one mistakes them for the headline
   statements.  BOTH REPORT [functional_extensionality_dep]; neither is
   gated. 

   --------
   * ** 莱布尼茨影子，以及它们的成本

   已发货，以便比较可以在树中使用，而不仅仅是在
   这个标题中，并且命名以免有人将它们误认为是头条
   声明。两者都报告 [functional_extensionality_dep]；都没有
   设置门控。
*)

Section CloneLeibniz.

Context (S : UA.OpSignature).

(* An action with no setoid: Leibniz [=] throughout. / 一个没有集合的动作：莱布尼茨 [=] 贯穿始终。 *)
Definition leibniz_action (A : UA.OpAlgebra S) : SetoidAction S :=
  {| sact_carrier := UA.carrier A
   ; sact_setoid  := eq_Setoid (UA.carrier A)
   ; sact_op      := UA.op A
   ; sact_op_respects := fun o k1 k2 H =>
       f_equal (UA.op A o) (functional_extensionality_dep k1 k2 H)
  |}.

Theorem action_extends_to_clone_leibniz (A : UA.OpAlgebra S)
  (F : ∀ n, DerivedOperators S n → (Fin.t n → UA.carrier A) → UA.carrier A)
  (Hvar : ∀ n (i : Fin.t n) env, F n (clone_var i) env = env i)
  (Hop : ∀ n (o : UA.operation S) (args : UA.arity o → DerivedOperators S n) env,
           F n (clone_op o args) env
             = UA.op A o (fun j => F n (args j) env)) :
  ∀ n (t : DerivedOperators S n) env,
    F n t env = clone_act (leibniz_action A) t env.
Proof.
  exact (action_extends_to_clone S (leibniz_action A) F Hvar Hop).
Qed.

Lemma clone_act_subst_leibniz {m n} (A : UA.OpAlgebra S)
  (s : Fin.t m → DerivedOperators S n) (t : DerivedOperators S m)
  (env : Fin.t n → UA.carrier A) :
  clone_act (leibniz_action A) (clone_subst s t) env
    = clone_act (leibniz_action A) t
        (fun i => clone_act (leibniz_action A) (s i) env).
Proof. exact (clone_act_subst S (leibniz_action A) s t env). Qed.

End CloneLeibniz.
