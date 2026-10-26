Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(* * * The category of algebras of a variety / * * 一类代数的范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/variety+of+algebras
 nLab:      https://ncatlab.org/nlab/show/algebraic+theory
 Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)

 Mac Lane §V.6, book p. 124 (PDF p. 133); Awodey §9.8, printed p. 256
 (PDF p. 265).

 The algebras of a given type that satisfy a set of identities — groups,
 rings, abelian groups, lattices — together with their operation-preserving
 maps form a category, the VARIETY or equational class of that
 presentation.  Mac Lane needs it as the setting for the free-algebra
 adjunction; Awodey defines the theory, its algebras and the forgetful
 functor to sets as the setting for the free-algebra theorem.

 ** What was missing, measured

 Instance/Comp.v has the whole syntactic apparatus and stops one step
 short of the category.  [OpSignature], [OpAlgebra] and
 [AlgHom] give operations, interpretations and homomorphisms;
 [EqSignature] gives laws with their naturality conditions; and
 [Algebra S E] is the TYPE of algebras satisfying them.  But
 [Algs] is the category of algebras of an OPERATION signature —
 the equations are dropped — and [Group := Algebra GroupOp GroupEq]
 is a type, not a category.  So ⟨Ω,E⟩-Alg was nowhere formed, and
 Instance/Roster.v records exactly that gap in prose: “there is no
 category of Groups there … the variety is recorded here as the type it
 is”.  This file forms it.

 ** How, and why this way

 [Variety] is the FULL SUBCATEGORY of [Algs] cut out by satisfaction of
 the laws, built with Construction/Subcategory.v's [Sub] in exactly the
 shape Theory/Lawvere/Model.v uses for [Models_sub]: an [sobj] that
 selects, an [shom] that retains every morphism ([True]), and closure
 proofs that are therefore [I].

 Two alternatives were considered and lose.  A fresh [Category] record
 over a sigma type would duplicate [Alg_id], [Alg_comp], [AlgHom_Setoid]
 and the four laws that [Sub] supplies for nothing; it would give up
 [Incl] and [Incl_Faithful]; and it would make fullness something to
 prove rather than the one-liner [fun _ _ _ _ _ => I].  The “[Models_sub]
 analogue” is not a third option — [Models] IS [Sub] of a subcategory, so
 that suggestion and this construction are the same one.

 The record presentation is not lost: [Variety_pack] and [Variety_unpack]
 are mutually inverse ON THE NOSE against Instance/Comp.v's
 [Algebra S E], each round trip an eta-expansion discharged by case
 analysis — the [Model_pack]/[Model_unpack] idiom of
 Theory/Lawvere/Model.v.

 Setoid discipline is inherited, not rebuilt: [Sub]'s hom-setoid is
 definitionally `≈` of first projections
 (Construction/Subcategory.v), so morphisms of [Variety] are compared
 with `≈`, and that `≈` is [Algs]' [AlgHom_Setoid], i.e. pointwise
 Leibniz [=] on carriers.  That is a property of the DONOR, which
 docs/INDEX.md's Instance/Ab.v bullet already flags, not a choice made
 here.

 ** The axiom boundary, and what it is actually a boundary of

 [Variety] and its twelve satellites are closed under the global
 context.  [GroupVariety] IS NOT: it reports
 [functional_extensionality_dep], inherited from Instance/Comp.v's
 [GroupEq], which is [Defined] with [functional_extensionality].
 The mechanism is [EqSignature]'s [lhs_natural] and
 [rhs_natural], which ask for a LEIBNIZ equation between
 two [arity o → B] argument bundles that are only pointwise equal.

 AN EARLIER REVISION OF THIS HEADER, OF THE COMMIT MESSAGE AND OF THE
 docs/INDEX.md BULLET DIAGNOSED THIS AS A FACT ABOUT EQUATION DEPTH —
 depth 1 free, depth ≥ 2 not.  THAT IS FALSE, and it is refuted by
 construction rather than by argument: [InvInvEq] below is the law
 inv (inv x) = x, DEPTH 2, over the very same [GroupOp], and it is
 Closed under the global context.

 The real criterion is the SHAPE OF EACH ARGUMENT BUNDLE, not the depth
 of the term.  A naturality field is conversion-provable exactly when
 every bundle the equation builds is either a REINDEXING [args ∘ φ] or
 a CONSTANT bundle: in the first case the field IS [op_commute] at that
 bundle, in the second [f_equal] against the constant-bundle former
 discharges it.  What defeats conversion is a bundle that MIXES a
 compound subterm with an [args] leaf, as every group axiom's [mul]
 node does — [mul' one' (args Only)] builds
 [fun i => match i with Fst => one' | Snd => args Only end], which is
 neither shape.  Two further measurements pin this down: associativity
 ALONE over [GroupOp], mentioning no nullary operation, still needs the
 axiom; and the SAME law at the EMPTY arity needs it when the bundle is
 spelled as a literal empty match and is CLOSED when the identical
 bundle is spelled as a reindexing of [args].  So the empty arity is
 not the root of anything — it is dodgeable — and
 Test/ProbeVariety440.v's n1 pins one conversion refusal, no more.

 What survives, and is the honest claim: no [EqSignature GroupOp]
 CAPTURING THE GROUP LAWS can be axiom-free by this route, because
 every group axiom has a [mul] node of the mixed shape.  That is a
 statement about the routes tried and the criterion above, NOT a proof
 of impossibility; and it needs the qualifier, since
 [eq := Empty_set] gives an axiom-free [EqSignature GroupOp] that
 captures nothing.

 Both sides are exhibited below rather than asserted: [CommMagmaVariety]
 (a depth-1 law, reindexing bundles) and [InvInvVariety] (a DEPTH-2 law,
 constant bundles) are both closed, and the second is the sharper
 exhibit because it is over [GroupOp] itself.

 Consequently [GroupVariety] and [GroupVariety_Bool] are deliberately
 NOT in the [make print-assumptions] gate — gating them would make the
 axiom audit report a stdlib axiom — and docs/AXIOMS.md carries them
 instead, with this reason.  Everything else in this file is gated,
 including the four [Variety_Forget] [Program] obligations and the two
 constructors, which are invisible to a [.glob] head census and were
 missed by a first count that claimed this file had no obligations.

 ** Not delivered

 No bridge to Theory/Lawvere/Model.v beyond a stated connection: see
 [variety_lawvere_connection] at the end of this file, which is a
 comment and not a theorem, and the follow-on issue it names.  No
 [GroupVariety ≅[Cat] Grp]: Instance/Variety/GroupComparison.v ships a fully
 faithful comparison functor instead and states why the isomorphism is
 not available.  No quotient of [Tree] by an equational congruence.  No
 removal of Instance/Comp.v's two commented-out instances, which is
 an edit to that file and is surfaced rather than made. 

 --------
 nLab:       https://ncatlab.org/nlab/show/variety+of+algebras 
 nLab:       https://ncatlab.org/nlab/show/algebraic+theory 
 Wikipedia:  https://en.wikipedia.org/wiki/Variety_(universal_algebra) 

 Mac Lane §V.6, 书籍第124页 (PDF第133页); Awodey §9.8, 印刷本第256页 (PDF第265页)。

 满足一组恒等式的给定类型的代数——群、环、阿贝尔群、格——连同它们保持运算的映射，构成一个范畴，即该表达式的品类或方程类。Mac Lane 需要它作为自由代数伴随的环境；Awodey 将理论、其代数及到集合的遗忘函子定义为自由代数定理的环境。

 ** 缺失的部分，用于测量Instance/Comp.v 拥有完整的句法结构，并且只差一步就可以形成范畴。[OpSignature]、[OpAlgebra] 和 [AlgHom] 提供操作、解释和同态；[EqSignature] 给出定律及其自然性条件；[Algebra S E] 是满足这些定律的代数的类型。但是 [Algs] 是一个操作签名代数的范畴——方程被省略——而 [Group := Algebra GroupOp GroupEq] 是一个类型，而不是范畴。因此 ⟨Ω,E⟩-Alg 并未形成，Instance/Roster.v 正是在文字中记录了这一空白：“这里没有群的范畴……这里作为它本身的类型记录了该簇”。这个文件形成了它。

 ** 如何，以及为什么以这种方式[Variety] 是通过满足定律而从 [Algs] 中剪切出的完整子类别，由 Construction/Subcategory.v 的 [Sub] 构建，形状与 Theory/Lawvere/Model.v 用于 [Models_sub] 的完全一致：一个选择的 [sobj]，一个保留每个态射（[True]）的 [shom]，以及因此是 [I] 的闭合证明。

 曾考虑过两种替代方案，但都失败了。在 sigma 类型上创建一个新的 [Category] 记录会重复 [Alg_id]、[Alg_comp]、[AlgHom_Setoid] 以及 [Sub] 提供的四条律法，而这些是多余的；它会放弃 [Incl] 和 [Incl_Faithful]；并且会使“完全性”变成需要证明的内容，而不是只需一行的 [fun _ _ _ _ _ => I]。所谓的“[Models_sub] 类似物”并不是第三种选择——[Models] 是子类别的 [Sub]，因此这个建议和这个构造是同一件事。记录表示并未丢失：[Variety_pack] 和 [Variety_unpack] 在 Instance/Comp.v 的 [Algebra S E] 上是完全互逆的，每一次往返都是由 case 分析完成的 eta 扩展——也就是 Theory/Lawvere/Model.v 中的 [Model_pack] / [Model_unpack] 习语。

 集合等价规律是继承而非重建的：[Sub] 的同态集合在定义上是首次投射的 `≈`（Construction/Subcategory.v），因此 [Variety] 的态射与 `≈` 进行比较，而 `≈` 则是 [Algs] 的 [AlgHom_Setoid]，即承载对象上的逐点 Leibniz [=]。这是 DONOR 的属性，docs/INDEX.md 中的 Instance/Ab.v 条目已经标记，而不是这里所做的选择。

 ** 公理边界，以及它实际上是哪种边界[Variety] 及其十二个卫星在全局上下文下是封闭的。[GroupVariety] 不是：它报告 [functional_extensionality_dep]，它继承自 Instance/Comp.v 的 [GroupEq]，这个 [GroupEq] 是 [Defined] 与 [functional_extensionality] 的组合。机制是 [EqSignature] 的 [lhs_natural] 和 [rhs_natural]，它们要求两个仅在点值上相等的 [arity o → B] 参数束之间存在一个莱布尼茨方程。

 这个头文件、提交信息以及 docs/INDEX.md 的早期版本将其诊断为关于方程深度的事实——深度 1 免费，深度 ≥ 2 不免费。那是错误的，并且它是通过构造而非论证反驳的：下面的 [InvInvEq] 是律 inv(inv x) = x，深度 2，作用于完全相同的 [GroupOp]，并且它在全局上下文下是封闭的。真正的标准是每个参数束的形状，而不是术语的深度。当且仅当方程构建的每个束都是重新索引 [args ∘ φ] 或常量束时，自然性域才是可转化证明的：在第一种情况下，该域在该束处是 [op_commute]，在第二种情况下，对常量束先前解除的 [f_equal]。阻碍转化的是将复合子项与 [args] 叶子混合的束，就像每个群公理的 [mul] 节点所做的那样——[mul' one' (args Only)] 构建 [fun i => match i with Fst => one' | Snd => args Only end]，它两者都不是该形状。还有两个进一步的测量确定了这一点：仅在 [GroupOp] 上的结合性，在没有提到零元运算的情况下，仍然需要公理；而在空元运算下的相同定律，当捆绑被写作字面上的空匹配时需要它，而当相同的捆绑被写作 [args] 的重索引时则是封闭的。因此，空元运算并不是任何事物的根源——它是可回避的——Test/ProbeVariety440.v 的 n1 固定了一个转换拒绝，没有更多。什么能存活，并且是诚实的说法：没有  [EqSignature GroupOp] 
 捕获群法则可以通过这条路线做到无公理性，因为每个群公理都有一个  [mul]  混合形状的节点。这是关于尝试过的路线和上述标准的陈述，而不是不可能性的证明；并且它需要限定词，因为  [eq := Empty_set]  给出了一个无公理的  [EqSignature GroupOp]  ，但它并没有捕获任何内容。

 下面展示了双方，而不是断言：  [CommMagmaVariety]  （一个深度为1的法则，重新索引束）和  [InvInvVariety]  （一个深度为2的法则，常数束）都已封闭，而第二个是更尖锐的展示，因为它本身位于  [GroupOp] 。因此 [GroupVariety] 和 [GroupVariety_Bool] 特意没有包含在 [make print-assumptions] 门中——把它们包含进去会使公理审核报告成为一个标准库公理——而 docs/AXIOMS.md 则包含了它们，并附上了这个原因。这个文件中的其他所有内容都是包含在门中的，包括四个 [Variety_Forget] [Program] 义务和两个构造函数，它们对于 [.glob] 头部统计是不可见的，并且在第一次统计时被遗漏，当时声称这个文件没有义务。

 ** 未交付没有通向 Theory/Lawvere/Model.v 的桥梁，只有一个已说明的连接：请参见本文件末尾的 [variety_lawvere_connection]，它是一个注释而不是定理，以及它所指的后续问题。没有 [GroupVariety ≅[Cat] Grp]: Instance/Variety/GroupComparison.v 提供一个完全忠实的比较函子，并说明为什么无法获得同构。没有通过等式合同商得出 [Tree]。没有移除 Instance/Comp.v 中的两个被注释掉的实例，这是对该文件的修改，并且被显示出来而没有被执行。
*)

(*
 Instance/Comp.v's record fields [carrier], [eq] and [map] would shadow
 the library's if this module were imported, so it is aliased and
 qualified throughout — the same decision, for the same reason, as
 Instance/Roster.v. 

 --------
 如果导入此模块，Instance/Comp.v 的记录字段 [carrier]、[eq] 和 [map] 会覆盖库中的字段，因此该模块在整个过程中都使用了别名和限定——出于同样的原因，对 Instance/Roster.v 也做出了相同的决定。
*)
Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Variety.

Context (S : UA.OpSignature).
Context (E : UA.EqSignature S).

(* * ** Satisfaction, and the full subcategory it cuts out / * ** 满意度，以及它切出的完整子类别 *)

(*
 [Subcategory]'s [sobj] lands in [Type], so satisfaction is stated as a
 [Type]-valued ∀ whose body is a Leibniz equation between two elements of
 the carrier.  It is DEFINITIONALLY the [equations] field of
 Instance/Comp.v, which is what makes the two presentations
 reflexivity-inverse below.

 Every coercion is written out.  Instance/Comp.v declares [eq :> Type]
 and [carrier :> Type] inside [Module UniversalAlgebra], and a module
 ALIAS does not activate coercions — only an [Import] would, which is
 the thing Instance/Roster.v warns against because [eq], [carrier]
 and [map] would shadow the library's.  So [UA.eq S E] and
 [UA.carrier A] appear in full below wherever the coercion would
 otherwise fire. 

 --------
 [Subcategory] 的 [sobj] 属于 [Type]，因此满足条件被表示为一个取值于 [Type] 的 ∀，其主体是承载体两个元素之间的莱布尼茨方程。这在定义上是 Instance/Comp.v 的 [equations] 字段，这也使得下面的两个表示具有自反-逆性质。

 每个强制转换都被完整写出。Instance/Comp.v 在 [Module UniversalAlgebra] 内声明了 [eq :> Type] 和 [carrier :> Type]，并且一个模块 ALIAS 不会激活强制转换——只有 [Import] 会，这正是 Instance/Roster.v 警告的情况，因为 [eq]、[carrier] 和 [map] 会遮蔽库中的同名项。因此，[UA.eq S E] 和 [UA.carrier A] 在下面完整出现，无论强制转换本来会在何处触发。
*)

Definition satisfies (A : UA.OpAlgebra S) : Type :=
  ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.carrier A),
    UA.lhs e args = UA.rhs e args.

Definition Variety_sub : Subcategory (@UA.Algs S) :=
  @Build_Subcategory (@UA.Algs S)
    satisfies
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Variety : Category := Sub (@UA.Algs S) Variety_sub.

(*
 Full: every homomorphism between algebras that satisfy the laws is a
 morphism of the variety. 

 --------
 完全：满足这些律的代数之间的每个同态都是该多样性的态射。
*)
Definition Variety_Full : Full (@UA.Algs S) Variety_sub :=
  fun _ _ _ _ _ => I.

Definition Variety_Incl : Variety ⟶ @UA.Algs S := Incl (@UA.Algs S) Variety_sub.

Definition Variety_Incl_Faithful : Functor.Faithful Variety_Incl :=
  Incl_Faithful (@UA.Algs S) Variety_sub.

(*
 The inclusion is FULL as a functor, not merely full as a subcategory:
 Construction/Subcategory.v already turns the one into the other, and
 an audit pointed out that this costs one line. 

 --------
 包含是作为函子完全的，而不仅仅是作为子范畴完全的：
 Construction/Subcategory.v 已经将一个变为另一个，并且
 审核指出这会多花一行代码。
*)
Definition Variety_Incl_Full : Functor.Full Variety_Incl :=
  Full_Implies_Full_Functor (@UA.Algs S) Variety_sub Variety_Full.

(* * ** The record presentation, and its round trips / * ** 记录展示及其往返 *)

Definition Variety_pack (A : UA.Algebra S E) : Variety :=
  (UA.alg S E A; UA.equations S E A).

Definition Variety_unpack (x : Variety) : UA.Algebra S E :=
  {| UA.alg := `1 x ; UA.equations := `2 x |}.

(*
 Propositional [=] on the packed OBJECT data — the sanctioned case; no
 morphism equality is asserted. 

 --------
 关于打包 OBJECT 数据的命题 [=] — 批准的情况；没有断言任何同态等式。
*)

Lemma Variety_unpack_pack (A : UA.Algebra S E) :
  Variety_unpack (Variety_pack A) = A.
Proof. destruct A; reflexivity. Qed.

Lemma Variety_pack_unpack (x : Variety) :
  Variety_pack (Variety_unpack x) = x.
Proof. destruct x; reflexivity. Qed.

(*
   * ** The forgetful functor to Sets

   Awodey's §9.8 asks for the category AND its forgetful functor.  The
   carrier is a bare type, so it lands on the DISCRETE setoid
   (Lib/Setoid.v's [eq_Setoid]); the functor is faithful, which is the
   concreteness the free-algebra theorem consumes. 

   --------
   * ** 忘记函子到集合

   Awodey 的 §9.8 要求给出该范畴及其忘记函子。承载对象是一个裸类型，因此它落在离散集体（Lib/Setoid.v 中的 [eq_Setoid]）；该函子是忠实的，这就是自由代数定理所使用的具体性。
*)

Program Definition Variety_Forget : Variety ⟶ Sets := {|
  fobj := fun A => {| carrier   := UA.carrier (`1 A)
                    ; is_setoid := eq_Setoid (UA.carrier (`1 A)) |};
  fmap := fun _ _ f => {| morphism := UA.map (`1 f) |}
|}.

Lemma Variety_Forget_Faithful : Functor.Faithful Variety_Forget.
Proof. construct; simpl in *; auto. Qed.

End Variety.

(*
 The signature is recoverable from the equation signature at every use
 site, so it is implicit throughout — [Variety E], not [Variety S E].
 [Arguments] here rather than inside the section, because a section's
 [Context] binders are explicit on the constants it closes over. 

 --------
 签名可以从每个使用点的方程签名中恢复，因此它在整个过程中都是隐式的——[Variety E]，而不是[Variety S E]。这里是[Arguments]，而不是在段落内部，因为段落的[Context] 绑定器在闭合的常量上是显式的。
*)
Arguments satisfies {_} _ _.
Arguments Variety_sub {_} _.
Arguments Variety {_} _.
Arguments Variety_Full {_} _.
Arguments Variety_Incl {_} _.
Arguments Variety_Incl_Faithful {_} _.
Arguments Variety_pack {_ _} _.
Arguments Variety_unpack {_ _} _.
Arguments Variety_unpack_pack {_ _} _.
Arguments Variety_pack_unpack {_ _} _.
Arguments Variety_Forget {_} _.
Arguments Variety_Forget_Faithful {_} _.

(*
   * ** The group variety

   The instantiation Mac Lane's §V.6 and the issue ask for, under a name
   that does NOT collide with Instance/Grp.v's [Grp] — there is exactly
   one [Grp] in this tree and it is that one.

   THIS CONSTANT CARRIES [functional_extensionality_dep], for the reason
   given in the header: it mentions [GroupEq], which is [Defined] using
   the axiom.  It is not gated; docs/AXIOMS.md records it. 

   --------
   * ** 群类

   实例化 Mac Lane 的 §V.6 并提出的问题，在一个不与 Instance/Grp.v 的 [Grp] 冲突的名称下 — 在这棵树中正好有一个 [Grp] ，就是它。

   这个常量携带 [functional_extensionality_dep] ，原因如标题所示：它提到 [GroupEq] ，根据公理，这是 [Defined] 。它没有被限制；docs/AXIOMS.md 记录了它。
*)

Definition GroupVariety : Category := Variety UA.GroupEq.

(*
 ℤ/2 under exclusive or, the witness Instance/Comp.v already builds,
 as an OBJECT of the category rather than an inhabitant of a type. 

 --------
 ℤ/2 在异或下，见证实例 Instance/Comp.v 已经构建，作为范畴的一个对象，而不是类型的一个元素。
*)
Definition GroupVariety_Bool : GroupVariety := Variety_pack UA.Bool.

(*
   * ** Where the axiom is not needed, exhibited twice

   First shape: REINDEXING bundles.  One binary operation, one law
   (commutativity), whose two naturality fields are [op_commute] itself
   at [args] and at [args ∘ comm_swap] — so no bundle is rebuilt and no
   extensionality is needed.  [Print Assumptions] on every constant in
   this block says “Closed under the global context”, and all are
   gated. 

   --------
   * ** 当公理不需要时，展示两次

   第一种形式：重新索引捆绑包。一个二元运算，一个定律（交换律），其两个自然性域为 [op_commute] 本身，在 [args] 和 [args ∘ comm_swap] — 因此没有捆绑包被重建，也不需要外延性。[Print Assumptions] 在该块的每个常量上都表示“在全局上下文下封闭”，且所有都已受控。
*)

Inductive magma_op : Set := magma_mul.

Definition MagmaOp : UA.OpSignature :=
  {| UA.operation := magma_op ; UA.arity := fun _ => UA.binary |}.

Inductive comm_eq : Set := comm_law.

Definition comm_swap (i : UA.binary) : UA.binary :=
  match i with UA.Fst => UA.Snd | UA.Snd => UA.Fst end.

Definition CommEq : UA.EqSignature MagmaOp.
Proof.
  refine {| UA.eq       := comm_eq
          ; UA.eq_arity := fun _ => UA.binary
          ; UA.lhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul args
          ; UA.rhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul (fun i => args (comm_swap i))
         |}.
  - intros A B f [] args; exact (UA.op_commute A B f magma_mul args).
  - intros A B f [] args;
      exact (UA.op_commute A B f magma_mul (fun i => args (comm_swap i))).
Defined.

Definition CommMagmaVariety : Category := Variety CommEq.

(*
   * ** Second shape: CONSTANT bundles, at DEPTH 2, over [GroupOp] itself

   This is the sharper exhibit, and it is what refutes the depth
   diagnosis.  [inv (inv x) = x] is a depth-2 equation over the SAME
   signature whose group laws force the axiom, and it is axiom-free:
   both of its bundles are CONSTANT ([fun _ => args Only] and
   [fun _ => inv' (args Only)]), so the outer naturality step is
   [f_equal] against the constant-bundle former and the inner one is
   [op_commute].  Nothing about the depth of the term enters.

   Note what this does and does not say.  It does NOT give an axiom-free
   group variety: [InvInvVariety] imposes only this one law, and the
   group axioms proper each build a [mul] bundle of the mixed shape the
   header describes. 

   --------
   * ** 第二种形态：常量束，在深度 2，作用于 [GroupOp] 本身

   这是更明确的例子，它驳斥了深度判断。[inv (inv x) = x] 是在相同类型签名下的深度 2 方程，它的群律强制生成公理，但它本身无公理：
   它的两个束都是常量（[fun _ => args Only] 和 [fun _ => inv' (args Only)]），所以外层的自然性步骤是
   [f_equal] 针对常量束前身，内层步骤是 [op_commute]。项的深度对此没有任何影响。

   注意这说明了什么，也说明了什么没有。它并没有给出一个无公理的群簇：[InvInvVariety] 只施加了这个法则，
   而真正的群公理各自构建了一个 [mul] 束，具有标题描述的混合形态。
*)

Inductive invinv_eq : Set := invinv.

Definition InvInvEq : UA.EqSignature UA.GroupOp.
Proof.
  refine {| UA.eq       := invinv_eq
          ; UA.eq_arity := fun _ => UA.unary
          ; UA.lhs      := fun (A : UA.OpAlgebra UA.GroupOp) _ args =>
                             UA.inv' (UA.inv' (args UA.Only))
          ; UA.rhs      := fun (A : UA.OpAlgebra UA.GroupOp) _ args =>
                             args UA.Only
         |}.
  - intros A B f [] args.
    unfold UA.inv'.
    rewrite UA.op_commute.
    apply (f_equal (fun z => UA.op B UA.inv (fun _ : UA.unary => z))).
    exact (UA.op_commute A B f UA.inv (fun _ => args UA.Only)).
  - intros A B f [] args; reflexivity.
Defined.

Definition InvInvVariety : Category := Variety InvInvEq.

(*
   * ** The connection to Lawvere theories, stated and not proved

   Work item 3 of the issue asks that the connection to
   Theory/Lawvere/Model.v be RECORDED.  Here it is, as prose, because the
   proof is a separate development and is listed as not delivered.

   For a presentation ⟨S,E⟩ the associated Lawvere theory has [nat] for
   objects, the [E]-congruence classes of n-tuples of derived operators
   for morphisms m ~> n, and finite products given by addition; its
   [Models] in [Sets] (Theory/Lawvere/Model.v) ought to be equivalent
   to [Variety E].  Two things block the equivalence here and neither is
   incidental.  Building the theory needs the clone as a CATEGORY, with
   the congruence as its hom-setoid and the two propositional object
   equalities [law_zero_terminal] and [law_plus_product]
   (Theory/Lawvere.v).  And the comparison then meets the same wall as
   Instance/Variety/GroupComparison.v: [Models T Sets] has SETOID carriers where
   [Variety]'s are Leibniz types, so essential surjectivity needs
   quotients.  Instance/Variety/Clone.v supplies the derived operators and
   their substitution calculus, which is the first half of the first
   obstruction; the rest is filed as a follow-on. 

   --------
   * ** 与劳弗雷范畴（Lawvere理论）的联系，已说明但未证明

   问题的工作项3要求将与
   Theory/Lawvere/Model.v 的联系记录下来。这里以文字形式给出，
   因为证明是一个独立的开发，并被列为未完成。对于一个表示 ⟨S,E⟩，其关联的Lawvere理论在对象上有 [nat]，在态射 m ~> n 上有 n 元导出算子的 [E] 同余类，有限积由加法给出；其 [Models] 在 [Sets]（Theory/Lawvere/Model.v）中应当与 [Variety E] 等价。有两件事阻碍了这里的等价性，而且都不是偶然的。构建理论需要将克隆作为一个范畴，并用同余作为其同态集（hom-setoid），并使用两个命题对象等式 [law_zero_terminal] 和 [law_plus_product]（Theory/Lawvere.v）。然后比较会遇到与 Instance/Variety/GroupComparison.v 相同的障碍：[Models T Sets] 有 SETOID 的承载对象，而 [Variety] 的承载对象是 Leibniz 类型，因此本质上的满射性需要商。Instance/Variety/Clone.v 提供了派生运算符及其替换演算，这是第一个障碍的上半部分；其余部分作为后续提交。
*)
