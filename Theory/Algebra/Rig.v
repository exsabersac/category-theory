Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Preadditive.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(**
* Rigs: rings without negatives

    Fong and Spivak, “Seven Sketches in Compositionality”, §5.3.1:
    Definition 5.36 with its footnotes [7sketches:5.3.1:def5.36], the
    naturals (Example 5.37 [7sketches:5.3.1:example5.37]), the booleans
    (Example 5.38 [7sketches:5.3.1:example5.38]), and rings as rigs with
    negatives (Example 5.42 [7sketches:5.3.1:example5.42]); §6.2.1
    Exercise 6.7 [7sketches:6.2.1:ex6.7], the rig homomorphisms, their
    category, and its initial object.
    nLab: https://ncatlab.org/nlab/show/rig
    Wikipedia: https://en.wikipedia.org/wiki/Semiring

    A rig (or semiring) is a “ring without negatives”: a commutative
    monoid (0, +), a monoid (1, ·) — multiplication deliberately NOT
    assumed commutative, per Definition 5.36 — with · distributing over +
    on both sides and 0 annihilating on both sides.  The mnemonic of
    Example 5.42: a riNg without Negatives.

    NAMING.  Following the set-level algebra precedent of Instance/CMon.v
    ([CMonObject]/[CMonHom]/[CMon]), the carrier-level structure is
    [RigObject], its homomorphisms [RigHom], and the category [Rig]; the
    underlying carrier is a setoid and every law is stated with [≈].

    THE ONE-OBJECT READING.  The library has carried the rig axioms all
    along, one categorical level up: [Structure/Preadditive.v]'s
    commutative-monoid enrichment specializes, on a ONE-OBJECT category,
    to exactly the four clauses of Definition 5.36 — the additive clause
    is [padd_assoc]/[padd_comm]/[padd_zero_left], the multiplicative
    monoid is the category structure itself, distributivity is
    [compose_padd_left]/[compose_padd_right], and annihilation is
    [compose_pzero_left]/[compose_pzero_right].  This file makes the
    specialization a theorem in both directions: [DeloopRig] equips the
    one-object category delooping a rig's multiplicative monoid
    (Construction/Deloop.v's construction, with composition as
    multiplication) with a [Preadditive] instance, and [EndRig] reads a
    rig off the endomorphism hom of ANY object of any LOCALLY
    PROPOSITIONAL preadditive category — an earlier revision of this
    sentence said “ANY preadditive category”, and the strength-change
    paragraph below records why it no longer can.  The rig-side round
    trip is definitional on every DATA
    field (zero, add, one, mul — the four [eq_refl] acceptance tests) and
    is packaged as the identity-carrier isomorphism [EndRig_DeloopRig] in
    [Rig]; unlike Deloop.v's proof-free [hom_monoid_Deloop] the full
    record equality is not definitional, because [RigObject] carries its
    laws as fields and the delooping's laws are opaque proof terms.  The
    category-side composite has no equational form for the same reason as
    in Deloop.v — [DeloopRig (EndRig P c)] is
    one-object while the ambient category need not be — and the honest
    statement (the full subcategory on {c}, preadditively) is deferred
    exactly as Deloop.v defers its §I.3 dictionary.  The three artifacts
    are packaged as [rig_iff_one_object_preadditive].

    A RECORDED STRENGTH CHANGE, ON THE CONVERSE HALF OF THAT BRIDGE.
    An earlier revision of this file stated the one-object reading
    unconditionally: “rigs are one-object preadditive categories”,
    with [EndRig] applicable to any [Preadditive C].  Since the PR
    “algebraic carriers are sets” (2026-09-17) a [RigObject] carries
    [rig_prop], a [PropEquiv] for its carrier setoid, and [EndRig]'s
    carrier IS the ambient's hom-setoid [c ~> c]; an arbitrary category
    supplies no [Prop] mirror of its `≈` — in [Cat] an [F ≈ G] IS a
    family of isomorphisms, so there is none (Lib/Setoid/
    Propositional.v, Instance/Sets/Propositional.v's header).
    So [EndRig] and, through it, [rig_iff_one_object_preadditive]'s
    second and third components now take
    [{LP : LocallyPropositional C}] (declared at
    Instance/Sets/Propositional.v).  Those two constants are the
    only ones in this file whose statement changed; [DeloopRig],
    [DeloopRig_Preadditive] and the rig side of the bridge are as they
    were, and so is every instance and the initiality argument.

    The hypothesis sits exactly at the PASSAGE from an internal
    structure to a concrete algebraic record, not in the internal
    algebra: [Preadditive] is untouched and keeps the ambient `≈`,
    which is the SCOPE paragraph of Structure/Complete.v's size note
    (item 4) read at this file.  Being a class, it is discharged by
    resolution wherever an instance is in scope, and every use in this
    file and downstream of it has one: at a delooping by
    [DeloopRig_LocallyPropositional] below — which is why the four
    [eq_refl] round-trip [Example]s and [EndRig_DeloopRig] are
    unchanged — and at [Ab], [RMod R] and [CMon] by
    [Ab_LocallyPropositional] (Instance/Ab.v),
    [RMod_LocallyPropositional] (Instance/Mod.v) and
    [CMon_LocallyPropositional] (Instance/CMon.v).

    INSTANCES.  [Nat_Rig] assembles the stdlib arithmetic lemmas into the
    rig of Example 5.37; [Bool_Rig] is Example 5.38's (false, ∨, true, ∧),
    proved by case analysis; both are axiom-free.  [RingObject] extends
    [RigObject] with additive inverses (mirroring how
    Structure/Additive.v extends Structure/Preadditive.v), with the
    forgetful functor [Ring_Forget_Rig]; the concrete witness is the
    integers [Int_Ring] over stdlib [Z] — axiom-free, unlike the ℝ
    witness the source suggests, whose stdlib axioms the library's
    zero-axiom discipline prefers to avoid (docs/AXIOMS.md).  Ring
    homomorphisms need no extra clause: preservation of negation is a
    THEOREM ([RigHom_neg]), by uniqueness of additive inverses.

    THE INITIAL OBJECT (Exercise 6.7).  The naturals are initial in
    [Rig]: the unique homomorphism out of [Nat_Rig] sends n to the n-fold
    sum of 1 ([rig_iter]), and any homomorphism agrees with it by
    induction ([Rig_Initial]).

    FORGETTING.  [Rig_Forget_CMon] projects the additive commutative
    monoid (a functor to Instance/CMon.v's [CMon]); [Rig_Forget_Mon]
    packages the multiplicative monoid as an internal monoid in
    (Sets, ∏) and lands in Theory/Algebra/Monoid/Hom.v's [Mon Sets].
    Their composites with the respective forgetfuls to [Sets] agree on
    the carrier, definitionally.

    The reconciliation with [Monad/Graded.v]'s [AndGrade] (the
    multiplicative half of [Bool_Rig]) and with the categorified rig
    structure of skeletal [FinSet] (whose coproduct and product act on
    objects exactly as [Nat_Rig]'s operations) live in the companion file
    Theory/Algebra/Rig/Connections.v, keeping this file's imports to the
    algebra spine.

--------
* 装备：没有底片的环

Fong 和 Spivak，“组合性的七个草图”，§5.3.1：
 定义 5.36 及其脚注 [7sketches:5.3.1:def5.36]，
 自然数（示例 5.37 [7sketches:5.3.1:example5.37]），布尔值
 （示例 5.38 [7sketches:5.3.1:example5.38]），并将环作为装备
 底片（示例 5.42 [7sketches:5.3.1:example5.42]）； §6.2.1
 练习 6.7 [7sketches:6.2.1:ex6.7]，装备同态，它们的
 范畴及其初始对象。 
nLab：https://ncatlab.org/nlab/show/rig
 维基百科：https://en.wikipedia.org/wiki/Semiring

钻机（或半环）是“没有负数的环”：可交换
 幺半群 (0, +)、幺半群 (1, ·) — 故意进行 NOT 乘法
 假设可交换，根据定义 5.36 — 其中 · 分布于 +
 双方均0歼灭。 的助记符
 例 5.42：没有底片的环。

命名。 遵循 Instance/CMon.v 的集合级代数先例
 （[CMonObject]/[CMonHom]/[CMon]），电信级结构为
 [RigObject]、其同态 [RigHom] 以及范畴 [Rig]； 的
 底层载体是 setoid，每条定律都用 [≈] 规定。

单一目标阅读。 图书馆已经承载了所有的装备公理
 沿着，一级分类：[Structure/Preadditive.v]
 交换幺半群丰富专门针对一个对象范畴，
 正好符合定义 5.36 的四个子句——附加子句
 是 [padd_assoc]/[padd_comm]/[padd_zero_left]，乘法
 幺半群是范畴结构本身，分布性是
 [compose_padd_left]/[compose_padd_right]，湮灭是
 [compose_pzero_left]/[compose_pzero_right]。
该文件使
 双向专业化定理：[DeloopRig] 配备
 单对象范畴解环装备的乘法幺半群
 （Construction/Deloop.v 的构造，其组成为
 乘法）与 [Preadditive] 实例，并且 [EndRig] 读取
 摆脱任何本地任何对象的内同态 hom
 PROPOSITIONAL preadditive 范畴 - 对此的早期修订
 句子说“任何预加性范畴”，并且强度变化
 下面的段落记录了为什么它不再可以。
钻机侧回合
 行程对每个数据都有定义
 字段（零、加、一、乘 — 四个 [eq_refl] 验收测试）和
 被封装为恒等载体同构 [EndRig_DeloopRig]
 [Rig]； 与 Deloop.v 的无证明 [hom_monoid_Deloop] 不同，完整的
 记录相等不是定义性的，因为 [RigObject] 带有它的
 作为场的定律和解环定律是不透明的证明术语。 的
 范畴侧复合没有等式形式，原因与
 在 Deloop.v — [DeloopRig (EndRig P c)] 中
 单一对象，而环境范畴不需要 - 并且诚实
 语句（{c} 上的完整子范畴，预先添加）被推迟
 正如 Deloop.v 推迟其 §I.3 字典一样。 三件神器
 封装为 [rig_iff_one_object_preadditive]。

这座桥的另一半有记录的力量变化。 
该文件的早期版本规定了单对象读取
 无条件地：“装备是单对象预加法范畴”，
 [EndRig] 适用于任何 [Preadditive C]。 自从公关
 “代数载体是集合”（2026-09-17）[RigObject] 携带
 [rig_prop]、[PropEquiv] 及其载体 setoid 和 [EndRig]
 载体是环境的hom-setoid [c ~> c]； 任意范畴
 不提供 `≈` 的 [Prop] 镜像 — 在 [Cat] 中，[F ≈ G] 是
 同构族，所以没有（Lib/Setoid/
 Propositional.v，Instance/Sets/Propositional.v 的标头）。 
因此 [EndRig] 以及通过它 [rig_iff_one_object_preadditive]
 现在需要第二个和第三个组件
 [{LP : LocallyPropositional C}]（声明于
 实例/集合/命题.v)。 这两个常数是
 仅此文件中的语句发生更改的； [DeloopRig]，
 [DeloopRig_Preadditive] 和桥的钻机侧是一样的
 是，每个实例和初始参数也是如此。

该假设恰好位于来自内部的通道
 结构为具体的代数记录，而不是在内部
 代数：[Preadditive] 未受影响并保持环境 `≈`，
 这是 Structure/Complete.v 大小注释的 SCOPE 段落
 （第 4 项）读取此文件。 作为一个类，它是由
 解决实例在范围内的任何地方，以及此中的每次使用
 文件及其下游有一个：在 delooping 处
 下面的 [DeloopRig_LocallyPropositional] — 这就是为什么这四个
 [eq_refl] 往返 [Example] 和 [EndRig_DeloopRig] 是
 不变 — 在 [Ab]、[RMod R] 和 [CMon] 中
 [Ab_LocallyPropositional]（实例/Ab.v），
 [RMod_LocallyPropositional]（实例/Mod.v）和
 [CMon_LocallyPropositional]（实例/CMon.v）。

实例。 [Nat_Rig] 将 stdlib 算术引理组装成
 实施例5.37的装备； [Bool_Rig] 是示例 5.38 的（假、∨、真、∧），
 通过案例分析证明； 两者都是无公理的。 [RingObject] 扩展
 [RigObject] 具有加性逆（反映如何
 Structure/Additive.v 扩展 Structure/Preadditive.v)，其中
 健忘函子 [Ring_Forget_Rig]； 具体见证者是
 整数 [Int_Ring] 优于 stdlib [Z] — 无公理，与 ℝ 不同
 见证来源表明，其 stdlib 公理是图书馆的
 零公理纪律倾向于避免（docs/AXIOMS.md）。 戒指
 同态不需要额外的子句：否定的保留是
 定理 ([RigHom_neg])，通过加法逆的唯一性。

初始目标（练习 6.7）。 自然物最初是在
 [Rig]：[Nat_Rig] 中独特的同态将 n 发送到 n 倍
 1 ([rig_iter]) 的总和，并且任何同态都与它一致
 感应 ([Rig_Initial])。

忘记。 [Rig_Forget_CMon] 投影加法交换
 monoid（Instance/CMon.v 的 [CMon] 的函子）； 保护70X
 将乘法幺半群封装为内部幺半群
 （集合，∏）并登陆 Theory/Algebra/Monoid/Hom.v 的 [Mon Sets]。 
他们的复合材料与 [Sets] 各自的遗忘一致
 从定义上讲，承运人。

与 [Monad/Graded.v] 的 [AndGrade] 的协调（
 [Bool_Rig] 的乘法一半）和分类装备
 骨架 [FinSet] 的结构（其联积和积作用于
 与 [Nat_Rig] 的操作完全相同的对象）存在于配套文件中
 Theory/Algebra/Rig/Connections.v，将此文件的导入保留到
 代数脊柱。
*)

(** ** Rigs over a setoid carrier / ** 在集合载体上的环 *)

(*
Definition 5.36, clause for clause.  Multiplication is NOT commutative:
   clause (b) is a bare monoid.

--------
定义 5.36，逐条条款。乘法不是交换的：条款 (b) 是一个裸幺半群。
*)
Record RigObject := {
  rig_setoid :> SetoidObject;

  rig_zero : carrier rig_setoid;
  rig_add  : carrier rig_setoid → carrier rig_setoid → carrier rig_setoid;
  rig_one  : carrier rig_setoid;
  rig_mul  : carrier rig_setoid → carrier rig_setoid → carrier rig_setoid;

  rig_add_respects : Proper (equiv ==> equiv ==> equiv) rig_add;
  rig_mul_respects : Proper (equiv ==> equiv ==> equiv) rig_mul;

  (* (a) (0, +) is a commutative monoid / (a) (0, +) 是交换幺半群 *)
  rig_add_assoc : ∀ a b c,
    rig_add (rig_add a b) c ≈ rig_add a (rig_add b c);
  rig_add_comm : ∀ a b, rig_add a b ≈ rig_add b a;
  rig_add_zero_l : ∀ a, rig_add rig_zero a ≈ a;

  (* (b) (1, ·) is a monoid — not assumed commutative / (b) (1, ·) 是一个幺半群——不假定为交换的 *)
  rig_mul_assoc : ∀ a b c,
    rig_mul (rig_mul a b) c ≈ rig_mul a (rig_mul b c);
  rig_mul_one_l : ∀ a, rig_mul rig_one a ≈ a;
  rig_mul_one_r : ∀ a, rig_mul a rig_one ≈ a;

  (* (c) · distributes over + on both sides / (c) · 在两边对 + 分配 *)
  rig_distr_l : ∀ a b c,
    rig_mul a (rig_add b c) ≈ rig_add (rig_mul a b) (rig_mul a c);
  rig_distr_r : ∀ a b c,
    rig_mul (rig_add a b) c ≈ rig_add (rig_mul a c) (rig_mul b c);

  (* (d) 0 annihilates on both sides / (d) 0 在两边均被消去 *)
  rig_mul_zero_l : ∀ a, rig_mul rig_zero a ≈ rig_zero;
  rig_mul_zero_r : ∀ a, rig_mul a rig_zero ≈ rig_zero;

  (*
The carrier is a SET: its `≈` is logically equivalent to a [Prop]-valued
     relation (Lib/Setoid/Propositional.v).  This field is not part of
     Definition 5.36; it is the same standing commitment [CMonObject] makes,
     and it is forced HERE rather than left to the rig's additive half because
     [rig_cmon] below builds a [CMonObject] whose carrier setoid IS
     [rig_setoid].  Last field, for the [Program] obligation-ordering reason
     given at Instance/CMon.v's [CMonObject].

--------
载体是一个集合：它的 `≈` 在逻辑上等价于一个 [Prop] 值的关系（Lib/Setoid/Propositional.v）。这个字段不是定义 5.36 的一部分；它与 [CMonObject] 所做的承诺相同，并且它在此处被强制，而不是留给该装置的加法部分，因为下面的 [rig_cmon] 构建了一个其载体集合是 [rig_setoid] 的 [CMonObject]。最后一个字段，出于 Instance/CMon.v 中 [CMonObject] 给出的 [Program] 义务排序原因。
*)
  rig_prop : PropEquiv (is_setoid rig_setoid)
}.

#[export] Existing Instance rig_add_respects.
#[export] Existing Instance rig_mul_respects.
#[export] Existing Instance rig_prop.

(* The right additive unit law follows by commutativity, as in CMon. / 正加法单位律由交换律得到，就像在CMon中一样。 *)
Corollary rig_add_zero_r (R : RigObject) (a : carrier (rig_setoid R)) :
  rig_add R a (rig_zero R) ≈ a.
Proof.
  rewrite rig_add_comm.
  apply rig_add_zero_l.
Qed.

(* The additive half of a rig, as a commutative monoid object. / 作为交换幺半群对象的装置的加性半部分。 *)
Definition rig_cmon (R : RigObject) : CMonObject := {|
  cmon_setoid := rig_setoid R;
  cmon_zero := rig_zero R;
  cmon_plus := rig_add R;
  cmon_plus_respects := rig_add_respects R;
  cmon_plus_assoc := rig_add_assoc R;
  cmon_plus_comm := rig_add_comm R;
  cmon_plus_zero_l := rig_add_zero_l R;
  cmon_prop := rig_prop R
|}.

(** ** Rig homomorphisms and the category Rig / ** 幂环同态与幂环范畴 *)

(* Exercise 6.7 part 1: a rig homomorphism preserves 0, +, 1 and ·. / 练习 6.7 第 1 部分：rig 同态保持 0、+、1 和 ·。 *)
Record RigHom (R S : RigObject) := {
  rig_map :> SetoidMorphism (rig_setoid R) (rig_setoid S);

  rig_map_zero : rig_map (rig_zero R) ≈ rig_zero S;
  rig_map_add : ∀ a b,
    rig_map (rig_add R a b) ≈ rig_add S (rig_map a) (rig_map b);
  rig_map_one : rig_map (rig_one R) ≈ rig_one S;
  rig_map_mul : ∀ a b,
    rig_map (rig_mul R a b) ≈ rig_mul S (rig_map a) (rig_map b)
}.

Arguments rig_map {R S} _.
Arguments rig_map_zero {R S} _.
Arguments rig_map_add {R S} _ _ _.
Arguments rig_map_one {R S} _.
Arguments rig_map_mul {R S} _ _ _.

#[local] Obligation Tactic := idtac.

(* Homomorphisms are compared by their underlying maps, pointwise. / 同态通过它们的底层映射按点比较。 *)
#[export]
Program Instance RigHom_Setoid {R S : RigObject} : Setoid (RigHom R S) := {|
  equiv := fun f g => ∀ a, rig_map f a ≈ rig_map g a
|}.
Next Obligation.
  intros R S.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (rig_map g a); [ apply Hfg | apply Hgh ].
Qed.

Program Definition rig_hom_id {R : RigObject} : RigHom R R := {|
  rig_map := setoid_morphism_id
|}.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.

Program Definition rig_hom_compose {R S T : RigObject}
  (f : RigHom S T) (g : RigHom R S) : RigHom R T := {|
  rig_map := setoid_morphism_compose (rig_map f) (rig_map g)
|}.
Next Obligation.
  intros R S T f g; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_zero g)).
  apply rig_map_zero.
Qed.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_add g a b)).
  apply rig_map_add.
Qed.
Next Obligation.
  intros R S T f g; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_one g)).
  apply rig_map_one.
Qed.
Next Obligation.
  intros R S T f g a b; simpl.
  rewrite (proper_morphism (rig_map f) _ _ (rig_map_mul g a b)).
  apply rig_map_mul.
Qed.

Lemma rig_hom_compose_respects {R S T : RigObject} :
  Proper (equiv ==> equiv ==> equiv) (@rig_hom_compose R S T).
Proof.
  intros f1 f2 Hf g1 g2 Hg a; simpl.
  rewrite (Hf (rig_map g1 a)).
  apply (proper_morphism (rig_map f2)), Hg.
Qed.

(* The category of rigs and rig homomorphisms. / 环和环同态的范畴。 *)
(*
The universes are pinned by hand, for the reason recorded at
   Instance/CMon.v's [CMon]: with [rig_prop] a field the record's sort carries
   a [Set+1], the elaborator stops identifying the record's own sort variable
   with the category's object universe, and [Rig] would acquire a third,
   redundant universe -- refusing the `Rig@{uo uh}` annotations of
   Instance/Rng/Free.v for arity.  Measured after the change,
   [Rig@{u p} : Category@{u p p}] with the one new constraint [Set < u].

--------
宇宙是手动固定的，原因记录在 Instance/CMon.v 的 [CMon]：当 [rig_prop] 是一个字段时，记录的类型携带一个 [Set+1]，展开器停止将记录自身的类型变量与范畴的对象宇宙识别起来，并且 [Rig] 会获得第三个多余的宇宙——拒绝 Instance/Rng/Free.v 的 `Rig@{uo uh}` 注释以表示元数。修改后测量，[Rig@{u p} : Category@{u p p}] 带有一个新的约束 [Set < u]。
*)
Program Definition Rig@{u p} : Category@{u p p} := {|
  obj     := RigObject@{p p p};
  hom     := RigHom@{p};
  homset  := @RigHom_Setoid@{p};
  id      := @rig_hom_id@{p};
  compose := @rig_hom_compose@{u p};

  compose_respects := @rig_hom_compose_respects@{u p}
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** ** The forgetful functors / ** 忘记函子 *)

(* To commutative monoids: keep the additive half. / 对于交换幺半群：保留加法部分。 *)
Program Definition Rig_Forget_CMon : Rig ⟶ CMon := {|
  fobj := rig_cmon;
  fmap := fun R S f => {|
    cmon_map := rig_map f;
    cmon_map_zero := rig_map_zero f;
    cmon_map_plus := rig_map_add f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(*
The multiplicative half, as an internal monoid in (Sets, ∏): the
   multiplication uncurried over the product setoid, the unit selected
   from the terminal setoid.

--------
乘法半群，作为 (Sets, ∏) 中的内部幺半群：乘法在积集合上非柯里化，单位从终对象集合中选择。
*)
Program Definition rig_mult_monoid (R : RigObject) :
  @Monoid Sets Sets_Product_Monoidal (rig_setoid R) := {|
  mu := {| morphism := fun p => rig_mul R (fst p) (snd p) |};
  eta := {| morphism := fun _ => rig_one R |}
|}.
Next Obligation.
  intros R p q [Hp Hq]; simpl.
  now rewrite Hp, Hq.
Qed.
Next Obligation.
  intros R [[a b] c]; simpl.
  apply rig_mul_assoc.
Qed.
Next Obligation.
  intros R [u a]; simpl.
  apply rig_mul_one_l.
Qed.
Next Obligation.
  intros R [a u]; simpl.
  apply rig_mul_one_r.
Qed.

(* To internal monoids in Sets: keep the multiplicative half. / 到集合中的内部幺半群：保留乘法部分。 *)
Program Definition Rig_Forget_Mon : Rig ⟶ @Mon Sets Sets_Product_Monoidal := {|
  fobj := fun R => (rig_setoid R : obj[Sets]; rig_mult_monoid R);
  fmap := fun R S f => (rig_map f; _)
|}.
Next Obligation.
  intros R S f.
  unshelve econstructor.
  - intro p; simpl.
    apply rig_map_mul.
  - intro u; simpl.
    apply rig_map_one.
Qed.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(** ** The one-object Preadditive bridge / ** 单对象前加性桥 *)

(*
Delooping the multiplicative monoid, with composition as
   multiplication — Construction/Deloop.v's construction, inlined so this
   file stays on the algebra spine (Deloop's [MonObject] carries only one
   operation; a rig needs both).

--------
对乘法幺半群去环化，组合作为乘法 —— Construction/Deloop.v 的构造，内联以便此文件保持在代数脊上（Deloop 的 [MonObject] 只包含一个操作；一个环需要两个）。
*)
Program Definition DeloopRig (R : RigObject) : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => carrier (rig_setoid R);
  homset  := fun _ _ => is_setoid (rig_setoid R);
  id      := fun _ => rig_one R;
  compose := fun _ _ _ f g => rig_mul R f g;

  compose_respects := fun _ _ _ => rig_mul_respects R
|}.
Next Obligation. intros R x y f; simpl; apply rig_mul_one_l. Qed.
Next Obligation. intros R x y f; simpl; apply rig_mul_one_r. Qed.
Next Obligation.
  intros R x y z w f g h; simpl; symmetry; apply rig_mul_assoc.
Qed.
Next Obligation.
  intros R x y z w f g h; simpl; apply rig_mul_assoc.
Qed.

(*
[DeloopRig R]'s hom-setoid IS the rig's own carrier setoid, so the
   delooping is locally propositional as soon as the rig is -- which, since
   the PR “algebraic carriers are sets” (2026-09-17), every rig is.  This is
   what lets [EndRig] below be applied back to a delooping in the round-trip
   examples.

--------
[DeloopRig R] 的 hom-集合同构体就是环的自身载体同构体，因此一旦环是局部命题的，其去循环也是局部命题的——自从 PR“代数载体是集合”（2026-09-17）以来，每个环都是如此。这就是让下面的 [EndRig] 可以在循环示例中应用回去的原因。
*)
#[export] Instance DeloopRig_LocallyPropositional (R : RigObject) :
  LocallyPropositional (DeloopRig R).
Proof.
  constructor.
  intros x y.
  exact (rig_prop R).
Defined.

(*
The additive structure of the rig is a Preadditive enrichment of its
   delooping: the four clauses of Definition 5.36 are exactly the
   Preadditive fields on one object.

--------
该刚体的加法结构是其去环化的预加法增强：定义 5.36 的四个条款恰好是一个对象上的预加法域。
*)
Program Definition DeloopRig_Preadditive (R : RigObject) :
  Preadditive (DeloopRig R) := {|
  padd := fun _ _ => rig_add R;
  pzero := fun _ _ => rig_zero R
|}.
Next Obligation. intros R x y f g h; apply rig_add_assoc. Qed.
Next Obligation. intros R x y f g; apply rig_add_comm. Qed.
Next Obligation. intros R x y f; apply rig_add_zero_l. Qed.
Next Obligation. intros R x y z h f g; apply rig_distr_l. Qed.
Next Obligation. intros R x y z f g h; apply rig_distr_r. Qed.
Next Obligation. intros R x y z f; apply rig_mul_zero_l. Qed.
Next Obligation. intros R x y z f; apply rig_mul_zero_r. Qed.

(*
Conversely, the endomorphism hom of ANY object of ANY preadditive
   category is a rig: addition is the enrichment, multiplication is
   composition.  This is the honest converse — it does not need the
   category to have one object.

   It DOES need one thing it did not need before the PR “algebraic carriers
   are sets” (2026-09-17): the ambient category must be LOCALLY PROPOSITIONAL
   (Instance/Sets/Propositional.v), since the rig's carrier setoid IS
   [C]'s hom-setoid and [rig_prop] has to be supplied from it.  The hypothesis
   is a class, so it is discharged by instance resolution wherever an instance
   is in scope -- at a delooping by [DeloopRig_LocallyPropositional] above, at
   [Ab] and [RMod R] by the instances in Instance/Ab.v and Instance/Mod.v.

--------
相反，任意预加性范畴中任意对象的自同态构成一个幺半环：加法是丰富结构，乘法是复合。这是真正的逆命题——它不需要该范畴只有一个对象。

它确实需要在 PR “代数承载是集合” (2026-09-17) 中之前不需要的一件事：环境范畴必须是局部命题性的 (Instance/Sets/Propositional.v)，因为该幺半环的承载集合是 [C] 的同态集合，而 [rig_prop] 必须从中提供。该假设是一个类，因此一旦实例在作用域中，通过实例解析就可以被解决——在上文通过 [DeloopRig_LocallyPropositional] 的去环，在 Instance/Ab.v 和 Instance/Mod.v 中通过 [Ab] 和 [RMod R] 的实例。
*)
Program Definition EndRig {C : Category} {LP : LocallyPropositional C}
  (P : Preadditive C) (c : C) :
  RigObject := {|
  rig_setoid := {| carrier := c ~> c; is_setoid := @homset C c c |};
  rig_zero := pzero;
  rig_add := padd;
  rig_one := id;
  rig_mul := fun f g => f ∘ g;

  rig_add_respects := @padd_respects C P c c;
  rig_mul_respects := @compose_respects C c c c;

  rig_add_assoc := @padd_assoc C P c c;
  rig_add_comm := @padd_comm C P c c;
  rig_add_zero_l := @padd_zero_left C P c c;

  rig_distr_l := @compose_padd_left C P c c c;
  rig_distr_r := fun a b c0 => @compose_padd_right C P c c c a b c0;

  rig_mul_zero_l := fun f => @compose_pzero_left C P c c c f;
  rig_mul_zero_r := fun f => @compose_pzero_right C P c c c f;

  rig_prop := locally_prop c c
|}.
Next Obligation. intros C LP P c f g h; simpl; symmetry; apply comp_assoc. Qed.
Next Obligation. intros C LP P c f; simpl; apply id_left. Qed.
Next Obligation. intros C LP P c f; simpl; apply id_right. Qed.

(*
The rig-side round trip, on the data: all four operations agree on
   the nose.

--------
钻机端往返实验，在数据上：四个操作都在鼻部一致。
*)
Example EndRig_DeloopRig_zero (R : RigObject) :
  rig_zero (EndRig (DeloopRig_Preadditive R) ttt) = rig_zero R := eq_refl.
Example EndRig_DeloopRig_add (R : RigObject) :
  rig_add (EndRig (DeloopRig_Preadditive R) ttt) = rig_add R := eq_refl.
Example EndRig_DeloopRig_one (R : RigObject) :
  rig_one (EndRig (DeloopRig_Preadditive R) ttt) = rig_one R := eq_refl.
Example EndRig_DeloopRig_mul (R : RigObject) :
  rig_mul (EndRig (DeloopRig_Preadditive R) ttt) = rig_mul R := eq_refl.

(*
Packaged as an isomorphism in [Rig]: both directions are the identity
   on the carrier.  (The full record equality is blocked only by the
   proof-carrying law fields — see the header.)

--------
在 [Rig] 中被打包为同构：两个方向在载体上都是恒等的。（完整的记录相等仅被携带证明的法律字段阻止——参见头部。）
*)
Program Definition EndRig_DeloopRig (R : RigObject) :
  EndRig (DeloopRig_Preadditive R) ttt ≅[Rig] R := {|
  to := {| rig_map := setoid_morphism_id |};
  from := {| rig_map := setoid_morphism_id |}
|}.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R; simpl; reflexivity. Qed.
Next Obligation. intros R a b; simpl; reflexivity. Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.

(*
The bridge, packaged: a rig deloops to a one-object preadditive
   category, any object of a LOCALLY PROPOSITIONAL preadditive category
   has an endomorphism rig, and the round trip on the rig side is the
   identity-carrier isomorphism, definitional on the data.  (The
   category-side composite has no equational form — see the header.)

   AN EARLIER REVISION read the middle clause as “any object of a
   preadditive category”.  Since the PR “algebraic carriers are sets”
   (2026-09-17) this triple's measured type carries the hypothesis on
   its second and third components,

     … * (∀ C, LocallyPropositional C → Preadditive C → obj → RigObject)
         * …

   because a [RigObject] carries [rig_prop]; see [EndRig] above and the
   strength-change paragraph of the header for why, and for what
   discharges it.  The first component [DeloopRig_Preadditive] is
   unchanged.

--------
桥梁，封装：一个装置去环到一个单对象的预加性范畴，任何局部命题性预加性范畴的对象都具有一个自同态环装置，并且环装置上的往返是定义在数据上的恒等载体同构。（范畴侧的复合没有方程形式——见标题。）

早期的修订将中间从句读作“任何预加性范畴的对象”。自从 PR “代数载体是集合”（2026-09-17）以来，这个三元组的测量类型在其第二和第三分量上携带了假设，

    … * (∀ C, LocallyPropositional C → Preadditive C → obj → RigObject)
        * …

因为 [RigObject] 携带 [rig_prop]；参见上文的 [EndRig] 以及标题中的强度变化段落，了解原因以及它用于什么目的。第一个分量 [DeloopRig_Preadditive] 保持不变。
*)
Definition rig_iff_one_object_preadditive :=
  (@DeloopRig_Preadditive, @EndRig, @EndRig_DeloopRig).

(** ** The naturals (Example 5.37) / ** 自然数（示例 5.37） *)

Definition nat_setoid_object : SetoidObject := {|
  carrier := nat;
  is_setoid := {| equiv := @eq nat; setoid_equiv := eq_equivalence |}
|}.

Program Definition Nat_Rig : RigObject := {|
  rig_setoid := nat_setoid_object;
  rig_zero := 0%nat;
  rig_add := Nat.add;
  rig_one := 1%nat;
  rig_mul := Nat.mul;

  (*
[nat_setoid_object]'s `≈` IS [eq], which is already a [Prop]; the two
     implications are the identity.  The relation has to be NAMED -- an
     ascription [(x ≈ y : Prop)] is refused, see Lib/Setoid/Propositional.v.

--------
[nat_setoid_object] 的 `≈` 是 [eq]，这已经是一个 [Prop]；这两个含义是相同的。该关系必须被命名——拒绝使用归属 [(x ≈ y : Prop)]，参见 Lib/Setoid/Propositional.v。
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid nat_setoid_object) (@eq nat)
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. intros a b c; simpl; now rewrite Nat.add_assoc. Qed.
Next Obligation. intros a b; simpl; apply Nat.add_comm. Qed.
Next Obligation. intros a; simpl; reflexivity. Qed.
Next Obligation. intros a b c; simpl; now rewrite Nat.mul_assoc. Qed.
Next Obligation. intros a; simpl; apply Nat.mul_1_l. Qed.
Next Obligation. intros a; simpl; apply Nat.mul_1_r. Qed.
Next Obligation. intros a b c; simpl; apply Nat.mul_add_distr_l. Qed.
Next Obligation. intros a b c; simpl; apply Nat.mul_add_distr_r. Qed.
Next Obligation. intros a; simpl; reflexivity. Qed.
Next Obligation. intros a; simpl; apply Nat.mul_0_r. Qed.

(** ** The booleans (Example 5.38) / ** 布尔值（示例 5.38） *)

Definition bool_setoid_object : SetoidObject := {|
  carrier := bool;
  is_setoid := {| equiv := @eq bool; setoid_equiv := eq_equivalence |}
|}.

Program Definition Bool_Rig : RigObject := {|
  rig_setoid := bool_setoid_object;
  rig_zero := false;
  rig_add := orb;
  rig_one := true;
  rig_mul := andb;

  rig_prop := @PropEquiv_of_relation _ (is_setoid bool_setoid_object) (@eq bool)
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.

(** ** Rings: rigs with negatives (Example 5.42) / ** 环：带负数的环（示例 5.42） *)

(*
A ring is a rig with additive inverses — mirroring how
   Structure/Additive.v extends Structure/Preadditive.v with [pneg].

--------
环是具有加法逆元的环——这反映了 Structure/Additive.v 如何通过 [pneg] 扩展 Structure/Preadditive.v。
*)
Record RingObject := {
  ring_rig :> RigObject;

  ring_neg : carrier (rig_setoid ring_rig) → carrier (rig_setoid ring_rig);
  ring_neg_respects : Proper (equiv ==> equiv) ring_neg;
  ring_neg_l : ∀ a,
    rig_add ring_rig (ring_neg a) a ≈ rig_zero ring_rig
}.

#[export] Existing Instance ring_neg_respects.

(*
Ring homomorphisms are just rig homomorphisms: preservation of
   negation is a theorem, by uniqueness of additive inverses.

--------
环同态只是幺半环同态：负元的保持是一个定理，由加法逆元的唯一性得到。
*)
Lemma RigHom_neg (R S : RingObject) (f : RigHom R S)
  (a : carrier (rig_setoid R)) :
  rig_map f (ring_neg R a) ≈ ring_neg S (rig_map f a).
Proof.
  (*
f(-a) = f(-a) + 0 = f(-a) + (f a + -f a) = (f(-a) + f a) + -f a
           = f(-a + a) + -f a = f 0 + -f a = -f a

--------
f(-a) = f(-a) + 0 = f(-a) + (f a + -f a) = (f(-a) + f a) + -f a
 = f(-a + a) + -f a = f 0 + -f a = -f a
*)
  rewrite <- (rig_add_zero_r S (rig_map f (ring_neg R a))).
  rewrite <- (ring_neg_l S (rig_map f a)).
  rewrite (rig_add_comm S (ring_neg S (rig_map f a)) (rig_map f a)).
  rewrite <- rig_add_assoc.
  rewrite <- rig_map_add.
  rewrite (proper_morphism (rig_map f) _ _ (ring_neg_l R a)).
  rewrite rig_map_zero.
  now rewrite rig_add_zero_l.
Qed.

(*
The category of rings, and the forgetful functor to rigs: full on the
   nose, since the homomorphisms coincide.

--------
环的范畴，以及对 rigs 的遗忘函子：满
   鼻子，因为同态一致。
*)
(* Pinned for the same reason as [Rig] above. / 出于与上面 [Rig] 相同的原因而被置顶。 *)
Program Definition Ring@{u p} : Category@{u p p} := {|
  obj     := RingObject@{p p p};
  hom     := fun R S => RigHom@{p} R S;
  homset  := fun R S => @RigHom_Setoid@{p} R S;
  id      := fun R => @rig_hom_id@{p} R;
  compose := fun _ _ _ f g => rig_hom_compose@{u p} f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects@{u p} _ _ _
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

Program Definition Ring_Forget_Rig : Ring ⟶ Rig := {|
  fobj := fun R => ring_rig R;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(** ** The integers: an axiom-free ring witness / ** 整数：一个无公理环的见证 *)

(*
The equality is Type-ascribed (the Ipt_equiv/R_equiv precedent of
   Instance/Top/Interval.v and Instance/Top/Presheaf.v) so the setoid's
   proof level floats instead of being pinned at the level of Prop-valued
   [eq] — pinning it would force every abelian group sharing an [AbHom]
   with ℤ down to Set, which is exactly the tensor-unit situation of
   Instance/Ab/Monoidal.v.

--------
该等式是类型赋予的（Instance/Top/Interval.v 和 Instance/Top/Presheaf.v 中 Ipt_equiv/R_equiv 的先例），因此该集合体的证明级别是浮动的，而不是固定在 Prop 值的 [eq] 级别 —— 如果固定它，将迫使每个与 ℤ 共享 [AbHom] 的阿贝尔群降到 Set，这是 Instance/Ab/Monoidal.v 中张量单位的情况。
*)
Definition Z_eqT (x y : Z) : Type := x = y.

Lemma Z_eqT_Equivalence : Equivalence Z_eqT.
Proof.
  constructor; unfold Z_eqT.
  - intro x; reflexivity.
  - intros x y H; now symmetry.
  - intros x y z H1 H2; now transitivity y.
Qed.

Definition Z_setoid_object : SetoidObject := {|
  carrier := Z;
  is_setoid := {| equiv := Z_eqT; setoid_equiv := Z_eqT_Equivalence |}
|}.

Lemma Z_add_respectful : ∀ a b : Z, Z_eqT a b →
  ∀ c d : Z, Z_eqT c d → Z_eqT (Z.add a c) (Z.add b d).
Proof.
  intros a b Hab c d Hcd; unfold Z_eqT in *; now subst.
Qed.

Lemma Z_mul_respectful : ∀ a b : Z, Z_eqT a b →
  ∀ c d : Z, Z_eqT c d → Z_eqT (Z.mul a c) (Z.mul b d).
Proof.
  intros a b Hab c d Hcd; unfold Z_eqT in *; now subst.
Qed.

Lemma Z_opp_respectful : ∀ a b : Z, Z_eqT a b → Z_eqT (Z.opp a) (Z.opp b).
Proof.
  intros a b Hab; unfold Z_eqT in *; now subst.
Qed.

(*
Plain definitions with explicit proof terms: the stdlib equalities land
   in the Type-ascribed [Z_eqT] by conversion, and the explicit universe
   binders keep the setoid's levels parameters rather than letting
   minimization collapse them to Set — which would drag every abelian
   group sharing a hom with ℤ down with it (the tensor-unit situation of
   Instance/Ab/Monoidal.v).

--------
带有明确证明项的简单定义：标准库中的等式通过转换落在类型指定的 [Z_eqT] 中，而显式的宇宙绑定器保持了集合同构的层级参数，而不是让最小化将它们折叠到 Set —— 否则会把与 ℤ 有同态的每一个阿贝尔群一起拉下去（Instance/Ab/Monoidal.v 的张量单元情况）。
*)
(*
The universe instance is written [RigObject@{q o p}], not [@{o p q}]:
   since the PR “algebraic carriers are sets” (2026-09-17) the record's
   AUXILIARY level -- the one bounding the [PropEquiv] field's own sort, which
   carries the [Set+1] -- is the FIRST argument rather than the third, so the
   named universes keep their roles by being permuted rather than renamed.
   [o] is still the carrier, [p] the proof level and [q] the level the
   record's sort is read at.

--------
宇宙实例写作 [RigObject@{q o p}]，而不是 [@{o p q}]：自从 PR “代数载体是集合”（2026-09-17）后，记录的 AUXILIARY 级别——用于限定 [PropEquiv] 字段自身类型的级别，该字段承载 [Set+1]——是第一个参数而不是第三个参数，因此命名宇宙通过排列而不是重命名来保持它们的角色。[o] 仍然是载体，[p] 是证明级别，[q] 是读取记录类型的级别。
*)
Definition Int_Rig@{o p q | o <= q, p <= q +} : RigObject@{q o p} := {|
  rig_setoid := Z_setoid_object@{o p};
  rig_zero := 0%Z;
  rig_add := Z.add;
  rig_one := 1%Z;
  rig_mul := Z.mul;
  rig_add_respects := Z_add_respectful;
  rig_mul_respects := Z_mul_respectful;
  rig_add_assoc := fun a b c => eq_sym (Z.add_assoc a b c);
  rig_add_comm := Z.add_comm;
  rig_add_zero_l := Z.add_0_l;
  rig_mul_assoc := fun a b c => eq_sym (Z.mul_assoc a b c);
  rig_mul_one_l := Z.mul_1_l;
  rig_mul_one_r := Z.mul_1_r;
  rig_distr_l := Z.mul_add_distr_l;
  rig_distr_r := Z.mul_add_distr_r;
  rig_mul_zero_l := Z.mul_0_l;
  rig_mul_zero_r := Z.mul_0_r;

  (*
[Z_eqT] is [eq] under a [Type] ascription, so the [Prop] mirror is [eq]
     itself and the two implications are the identity by conversion.  The
     ascription is what keeps the setoid's proof level a parameter (see the
     comment above [Z_eqT]); it does not make the relation proof-relevant.

--------
[Z_eqT] 是在 [Type] 指定下的 [eq]，因此 [Prop] 镜像是 [eq] 自身，并且这两个蕴含通过转换是恒等的。指定是保持集合同构的证明级别为参数的原因（参见上面 [Z_eqT] 的注释）；它并不使关系具有证明相关性。
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid Z_setoid_object@{o p}) (@eq Z)
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition Int_Ring@{o p q | o <= q, p <= q +} : RingObject@{q o p} := {|
  ring_rig := Int_Rig@{o p q};
  ring_neg := Z.opp;
  ring_neg_respects := Z_opp_respectful;
  ring_neg_l := Z.add_opp_diag_l
|}.

(** ** The naturals are initial (Exercise 6.7, part 2) / ** 自然数是初始的（练习 6.7，第2部分） *)

(* The n-fold sum of 1. / 1 的 n 倍和。 *)
Fixpoint rig_iter (R : RigObject) (n : nat) : carrier (rig_setoid R) :=
  match n with
  | O => rig_zero R
  | S k => rig_add R (rig_one R) (rig_iter R k)
  end.

Lemma rig_iter_add (R : RigObject) (a b : nat) :
  rig_iter R (a + b) ≈ rig_add R (rig_iter R a) (rig_iter R b).
Proof.
  induction a; simpl.
  - now rewrite rig_add_zero_l.
  - now rewrite IHa, rig_add_assoc.
Qed.

Lemma rig_iter_mul (R : RigObject) (a b : nat) :
  rig_iter R (a * b) ≈ rig_mul R (rig_iter R a) (rig_iter R b).
Proof.
  induction a; simpl.
  - now rewrite rig_mul_zero_l.
  - rewrite rig_iter_add, IHa.
    rewrite rig_distr_r.
    now rewrite rig_mul_one_l.
Qed.

Program Definition rig_from_nat (R : RigObject) : RigHom Nat_Rig R := {|
  rig_map := {| morphism := rig_iter R |}
|}.
Next Obligation. intros R; proper. Qed.
Next Obligation. intros R a b; apply rig_iter_add. Qed.
Next Obligation.
  intros R; simpl.
  now rewrite rig_add_zero_r.
Qed.
Next Obligation. intros R a b; apply rig_iter_mul. Qed.

Lemma rig_from_nat_unique (R : RigObject) (h : RigHom Nat_Rig R) (n : nat) :
  rig_map h n ≈ rig_iter R n.
Proof.
  induction n; simpl.
  - apply (rig_map_zero h).
  - change (S n) with (1 + n)%nat.
    rewrite (rig_map_add h 1%nat n).
    rewrite IHn.
    apply rig_add_respects; [| reflexivity ].
    (* h 1 ≈ 1: the multiplicative unit clause / h 1 ≈ 1：乘法单位子句 *)
    apply (rig_map_one h).
Qed.

#[export] Program Instance Rig_Initial : @Initial Rig := {
  terminal_obj := Nat_Rig;
  one := rig_from_nat
}.
Next Obligation.
  intros R f g n; simpl.
  rewrite (rig_from_nat_unique R f n).
  now rewrite (rig_from_nat_unique R g n).
Qed.

(** ** Acceptance tests / ** 验收测试 *)

(* The four clauses at work on the concrete instances, computationally. / 四个条款在具体实例上运作，计算上。 *)
Example nat_rig_distr :
  rig_mul Nat_Rig 2%nat (rig_add Nat_Rig 3%nat 4%nat) = 14%nat
  := eq_refl.
Example bool_rig_annihilation :
  rig_mul Bool_Rig (rig_zero Bool_Rig) true = false := eq_refl.
Example int_ring_neg : rig_add Int_Rig (ring_neg Int_Ring 7%Z) 7%Z = 0%Z
  := eq_refl.

(* The initial homomorphism computes: 3 goes to 1 + (1 + (1 + 0)). / 初始同态计算：3 映射到 1 + (1 + (1 + 0))。 *)
Example rig_iter_nat_3 :
  rig_map (rig_from_nat Nat_Rig) 3%nat = 3%nat := eq_refl.

(*
The forgetful functors agree with the projections on the nose, and
   their composites with the forgetfuls to [Sets] return the carrier
   setoid definitionally — the header's claim, machine-checked.

--------
遗忘函子与投影在本质上完全一致，并且它们与到 [Sets] 的遗忘函子的复合在定义上返回载体集合——标题的声明，经过机器验证。
*)
Example rig_forget_cmon_carrier (R : RigObject) :
  cmon_setoid (Rig_Forget_CMon R) = rig_setoid R := eq_refl.
Example rig_forget_cmon_sets (R : RigObject) :
  CMon_Forget (Rig_Forget_CMon R) = rig_setoid R := eq_refl.
Example rig_forget_mon_sets (R : RigObject) :
  Mon_Forget (Rig_Forget_Mon R) = rig_setoid R := eq_refl.
