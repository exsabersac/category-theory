Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * The slice over a terminal object is the ambient category / * * 终端对象上的切片是环境范畴 *)

(*
 Reference: Saunders Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., §II.6, p. 47, Exercise 2 [maclane:II.6:ex2] — in the
 catalog's paraphrase (doc/plan/books/maclane/inventory/II.json,
 not the book's wording): if t is a terminal object of C, the
 category (C ↓ t) of objects over t is isomorphic to C.  The same
 statement appears already on p. 45 as the worked example
 accompanying the definition of (C ↓ a) [maclane:II.6:def2]:
 since the one-point set is terminal in Set, the category of sets
 over it is isomorphic to Set.
 nLab:      https://ncatlab.org/nlab/show/over+category
 nLab:      https://ncatlab.org/nlab/show/terminal+object
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 The content is one sentence of mathematics.  An object of the slice C/t is
 an object a of C equipped with a structure morphism a ~> t; when t is
 terminal that morphism carries no information, since [one_unique] says any
 two arrows into t agree.  So “an object over t” is just “an object”, and a
 commuting triangle over t is just an arrow: the triangle condition
 `g' ∘ f ≈ g` is automatic.  The forgetful functor (a, g) ↦ a and the section
 a ↦ (a, !) implement the correspondence.

 Dually — [Coslice_Initial] in Block B — the coslice under an initial object
 is again the ambient category, `0/C ≅ C`.

 ** Strength: this is an EQUIVALENCE, and the gap is real

 Mac Lane says “isomorphic”, meaning an isomorphism of categories.  What is
 delivered here is [≅[Cat]], and in this library that is *equivalence* of
 categories, not isomorphism: Cat's hom-setoid is [Functor_Setoid]
 (Instance/Cat.v), which identifies functors that are naturally isomorphic.
 The weakening is not an artifact of the proof — the on-the-nose statement is
 FALSE here, for a reason worth naming, and the falsity is MACHINE-CHECKED:
 [slice_terminal_not_strict] (Construction/Comma/Special.v) exhibits a
 category — [Blur], one object, two parallel arrows identified by its
 hom-setoid — with a [Terminal] instance for which
 `Slice Blur ttt ≅[StrictCat] Blur` is refutable outright.

 In a set-based development the object *set* of C/t is in bijection with the
 object set of C, because “there is exactly one arrow a ~> t” is a statement
 about elements.  In this library terminality is stated up to `≈`
 ([one_unique] : f ≈ g), which is weaker than `f = g`.  The objects of
 [Slice] are the dependent pairs `∃ a : C, a ~> t`, so two `≈`-equal but
 distinct structure morphisms g and g' give two *distinct* objects (a; g) and
 (a; g') of the slice.  A strict isomorphism of categories would have to
 identify them, and nothing in the [Terminal] class does.  What is true is
 that they are canonically isomorphic *in the slice*, by the identity of C —
 and that is exactly the natural isomorphism supplied below.  So the honest
 reading is: the slice over a terminal object is equivalent to C, with the
 equivalence exhibited by an explicit adjoint-equivalence-shaped pair, not
 isomorphic to it on the nose.

 The two round trips therefore have DIFFERENT strengths, and both are
 recorded:

 - [Slice_Forget ◯ Slice_Section] is the identity functor on C at STRICT
 strength ([Slice_Terminal_strict_section]): its object map is
 definitionally `fun x => x` and its arrow map definitionally `fun f => f`,
 so the [Functor_StrictEq_Setoid] witness is `fun _ => eq_refl` and the
 coherence clause is `f ≈ f`.  [Slice_Section] is thus a strict section of
 [Slice_Forget], not merely a section up to isomorphism.

 - [Slice_Section ◯ Slice_Forget] is the identity on the slice only up to
 natural isomorphism, by the argument above.  Its components are carried by
 `id` in C ([slice_terminal_unit_carrier]), so the isomorphism is as
 canonical as it can be; it is not, and cannot be, an equality.

 ** Relation to the neighbouring files

 Construction/Slice.v proves the slice IS a comma category,
 `C/c ≅[Cat] (Id ↓ =(c))` ([Comma_Slice]), so this file's statement transports
 to the comma reading at the same strength.  Construction/Comma/Special.v
 handles the other end of Mac Lane's list of specializations, the comma of two
 constant functors. 

 --------
 参考文献：Saunders Mac Lane，《为工作数学家而设的范畴论》，第二版，第II.6节，第47页，练习2 [maclane:II.6:ex2] — 在目录的意译中（doc/plan/books/maclane/inventory/II.json，不是书中的原文）：如果 t 是 C 的终对象，那么 t 上的对象范畴 (C ↓ t) 与 C 同构。相同的陈述已经出现在第45页，作为 (C ↓ a) 定义的例子 [maclane:II.6:def2]：由于单点集合在 Set 中是终对象，单点集合上的集合范畴与 Set 同构。
 nLab: https://ncatlab.org/nlab/show/over+category
 nLab: https://ncatlab.org/nlab/show/terminal+object
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category内容是一句数学话。切片 C/t 的一个对象是 C 的一个对象 a，并配备一个结构态射 a → t；当 t 是终对象时，该态射不携带信息，因为 [one_unique] 表示任何指向 t 的两个箭头都相等。因此“在 t 上的一个对象”只是“一个对象”，在 t 上的可交换三角形只是一个箭头：三角形条件 `g' ∘ f ≈ g` 是自动满足的。忘记函子 (a, g) ↦ a 和截面 a ↦ (a, !) 实现了对应关系。

 对偶地——块 B 中的 [Coslice_Initial]——在初始对象下的余切片再次是原范畴 `0/C ≅ C`。

 ** 强度：这是一个等价，并且差距是真实存在的麦克莱恩说“同构”，意思是范畴的同构。这里给出的内容是 [≅[Cat] ]，而在这个库中，那是范畴的*等价*，不是同构：Cat 的态射集准则是 [Functor_Setoid] （Instance/Cat.v），它识别自然同构的函子。这种弱化不是证明的人工产物——精确表达的陈述在这里是错误的，有一个值得指出的原因，而且这个错误是机器检验过的：[slice_terminal_not_strict] （Construction/Comma/Special.v）展示了一个范畴——[Blur]，一个对象，两条由其态射集准则识别的平行箭头——对于其 [Terminal] 实例，`Slice Blur ttt ≅ [StrictCat]ZZ  Blur` 可以被直接反驳。在基于集合的发展中，C/t 的对象 *集合* 与 C 的对象集合是一一对应的，因为“正好有一个箭头 a ~> t”是关于元素的陈述。在这个库中，终端性是以 `≈` 表示（ [one_unique] : f ≈ g），这比 `f = g` 弱。[Slice] 的对象是依赖对 `∃ a : C, a ~> t`，因此两个 `≈` 相等但不同的结构态射 g 和 g' 会给出 slice 中两个 *不同* 的对象 (a; g) 和 (a; g')。类别的严格同构必须将它们认定为相同，而 [Terminal] 类中没有任何东西做到这一点。真实情况是，它们在 slice 中是自然同构的，由 C 的恒等映射保证——这正是下面提供的自然同构。所以，诚实的阅读是：在终对象上的切片等价于 C，这种等价通过一个明确的伴随等价形状的对来展示，而不是严格的同构。

 因此，这两个往返具有不同的强度，并且两者都被记录下来：

 - [Slice_Forget ◯ Slice_Section] 是 C 上在严格强度 ([Slice_Terminal_strict_section]) 下的恒等函子：它的对象映射在定义上是 `fun x => x`，箭头映射在定义上是 `fun f => f`，所以 [Functor_StrictEq_Setoid] 的见证是 `fun _ => eq_refl`，协调条款是 `f ≈ f`。因此，[Slice_Section] 是 [Slice_Forget] 的严格截面，而不仅仅是同构意义上的截面。-  [Slice_Section ◯ Slice_Forget] 仅在自然同构的意义上是片上的恒等函数，根据上面的论证。它的分量由  
 `id`  在 C ( [slice_terminal_unit_carrier] ) 中承载，所以该同构尽可能是典型的；它不是，也不可能是相等的。

 ** 与相邻文件的关系

 Construction/Slice.v 证明了片是一个逗号范畴，  
 `C/c ≅ [Cat]ZZ  (Id ↓ =(c))`  ( [Comma_Slice] )，因此本文件的陈述以同样的强度传递到逗号解释。Construction/Comma/Special.v  
 处理 Mac Lane 列表中特化的另一端，即两个常值函子之间的逗号。
*)

(* * ** Block A: the slice over a terminal object / * ** 块 A：终端对象上的切片 *)

Section SliceTerminal.

Context {C : Category}.
Context {T : @Terminal C}.

(*
 The forgetful functor C/1 ⟶ C: drop the structure morphism.  This is the
 comma projection [comma_proj1] read through [Comma_Slice]; it is spelled out
 directly here so that both its object and arrow maps are the literal first
 projections and hence compute. 

 --------
 遗忘函子 C/1 ⟶ C：丢弃结构态射。这是逗号投影 [comma_proj1]，通过 [Comma_Slice] 读取；这里直接写出它，以便它的对象映射和箭头映射都是字面上的第一投影，从而可以计算。
*)
Program Definition Slice_Forget :
  @Slice C (@terminal_obj C T) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(*
 The section C ⟶ C/1: equip an object with its unique arrow into 1.  The
 triangle condition for an arrow f is `one ∘ f ≈ one`, discharged by
 [one_unique] (equivalently, it is the corollary [one_comp]) — the only place
 terminality is used in this direction. 

 --------
 C ⟶ C/1 这一节：为一个对象配备其指向 1 的唯一箭头。箭头 f 的三角形条件是 `one ∘ f ≈ one`，由 [one_unique] 消解（等价地，它是推论 [one_comp]）——这是在这个方向上使用终端性的唯一地方。
*)
Program Definition Slice_Section :
  C ⟶ @Slice C (@terminal_obj C T) := {|
  fobj := fun x => (x; one);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply one_unique. Qed.

(*
 Every slice object is canonically isomorphic to its “renormalised” form
 (a; !).  The carrier of the isomorphism is the identity of C in both
 directions; only the triangle proofs differ, and [one_unique] supplies both.
 This is the natural-isomorphism component of the round trip below, isolated
 so that the strength claim in the header can be read off. 

 --------
 每一个切片对象在范畴同构意义上与其“重整化”形式 (a; !) 同构。该同构的载体在两个方向上都是 C 的恒等映射；唯一区别在三角形证明上，而 [one_unique] 提供了两者。这是下面往返过程的自然同构分量，被单独列出，以便可以直接读取标题中的强度声明。
*)
Program Definition slice_terminal_unit (x : @Slice C (@terminal_obj C T)) :
  Slice_Section (Slice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(*
 The component is carried by the identity of C, in both directions. 

 --------
 该组件由 C 的身份携带，在两个方向上都是如此。
*)
Corollary slice_terminal_unit_carrier
  (x : @Slice C (@terminal_obj C T)) :
  (`1 (to (slice_terminal_unit x)) ≈ id) ∧
  (`1 (from (slice_terminal_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(*
 Mac Lane, §II.6, Exercise 2 [maclane:II.6:ex2].  Note the strength: `≅[Cat]`
 is EQUIVALENCE of categories in this library (Instance/Cat.v), and the header
 explains why the on-the-nose isomorphism Mac Lane states is unavailable
 here. 

 --------
 Mac Lane，第 II.6 节，练习 2  [maclane:II.6:ex2] 。 注意强度：`≅ [Cat]ZZ ` 在这个库（Instance/Cat.v）中是范畴的等价，并且标题解释了为什么 Mac Lane 所说的准确同构在这里不可用。
*)
Program Definition Slice_Terminal :
  @Slice C (@terminal_obj C T) ≅[Cat] C := {|
  to   := Slice_Forget;
  from := Slice_Section
|}.
(*
 The C-side clause `Slice_Forget ◯ Slice_Section ≈ Id[C]` is discharged by the
 library's default obligation tactic — that composite is the identity on
 objects definitionally, so [iso_id] components suffice; the explicit and
 sharper statement is [Slice_Terminal_strict_section] below.  The clause left
 over is the slice-side one. 

 --------
 C 侧子句 `Slice_Forget ◯ Slice_Section ≈ Id [C]ZZ ` 被库的默认义务策略解除——该复合在定义上是对象的恒等映射，因此 [iso_id] 组件就足够了；更明确、更精确的表述见下文的 [Slice_Terminal_strict_section]。剩下的子句是切片侧的那个。
*)
Next Obligation.
  (*
 Slice_Section ◯ Slice_Forget ≈ Id[C/1]: the components are the
 renormalisation isomorphisms above; naturality is `id ∘ f ∘ id ≈ f` on the
 underlying C-morphisms, the slice hom-setoid comparing nothing else. 

 --------
 Slice_Section ◯ Slice_Forget ≈ Id [C/1]：组成部分是上述的重整化同构；自然性是在基础 C-态射上的 `id ∘ f ∘ id ≈ f`，比对其他任何事物的切片同态集合。
*)
  exists slice_terminal_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

(*
 The C-side round trip at strict strength: [Slice_Section] is a STRICT
 section of [Slice_Forget].  Both maps of the composite are definitionally
 the identity's, so the [Functor_StrictEq_Setoid] object witness is
 `fun _ => eq_refl` and the arrow coherence is `f ≈ f`.  This is strictly
 stronger than the [Cat]-level clause of [Slice_Terminal] and is the precise
 sense in which one half of Mac Lane's isomorphism does survive. 

 --------
 严格强度下的 C 边往返：[Slice_Section] 是 [Slice_Forget] 的一个严格部分。复合的两个映射从定义上都是恒等映射，因此 [Functor_StrictEq_Setoid] 对象的证明是 `fun _ => eq_refl`，箭头一致性是 `f ≈ f`。这严格强于 [Slice_Terminal] 的 [Cat] 级子句，并且正是在这个意义上，Mac Lane 同构的一半确实得以保留。
*)
Lemma Slice_Terminal_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Slice_Forget ◯ Slice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End SliceTerminal.

(* * ** Block B: the coslice under an initial object / * ** 模块 B：初始对象下的余切片 *)

(*
 Why this is proved directly rather than transported from Block A.

 `Initial C` is literally `Terminal (C^op)` (Structure/Initial.v), so the
 dual statement OUGHT to be Block A read in the opposite category.  It is
 not, and the obstruction is presentational rather than mathematical.
 Unfolding, the opposite of the slice over C^op has homs

 ∃ f : `1 x ~> `1 y,  f ∘ `2 x ≈ `2 y

 whereas Construction/Slice.v's [Coslice] record has homs

 ∃ f : `1 x ~> `1 y,  `2 y ≈ f ∘ `2 x

 — the same equation written in the other orientation.  Those are distinct
 types, so `Coslice C c` is NOT definitionally `(Slice (C^op) c)^op` and the
 transport would have to be mediated by an explicit comparison isomorphism
 built out of [symmetry] in the hom-setoid, plus the action of the duality
 functor [Op : Cat ⟶ Cat] (Instance/Cat/Opposite.v) on isomorphisms.  That is
 strictly more work, and a heavier dependency, than restating the four short
 definitions with [zero_unique] in place of [one_unique] — which is what
 follows.  Nothing below re-proves any mathematics that Block A proved; the
 two arguments are each two appeals to the uniqueness law. 

 --------
 为什么这是直接证明的，而不是从区块A中转移过来的。

 `Initial C` 字面上就是 `Terminal (C^op)`（Structure/Initial.v），因此
 对偶命题应该是在相反范畴中读取的区块A。实际上并非如此，阻碍是表述上的，而非数学上的。
 展开来看，在 C^op 上的片的对偶有态射

 ∃ f :  `1 x ~> ` 1 y,  f ∘  `2 x ≈ ` 2 y

 而 Construction/Slice.v 中的 [Coslice] 记录的态射为

 ∃ f :  `1 x ~> ` 1 y,   `2 y ≈ f ∘ ` 2 x——以另一种方向书写的相同方程。那些是不同的类型，因此 `Coslice C c` 在定义上不是 `(Slice (C^op) c)^op`，并且这种传递必须通过在同态集合中用 [symmetry] 构建的显式比较同构来介导，再加上对同构应用对偶函子 [Op : Cat ⟶ Cat]（Instance/Cat/Opposite.v）。这明显比用 [zero_unique] 替代 [one_unique] 重述四个简短定义所需的工作和依赖更多——下文正是这样做的。下面的内容没有重新证明 Block A 已经证明的任何数学内容；这两个论证各自都是对唯一性定律的两次引用。
*)

Section CosliceInitial.

Context {C : Category}.
Context {I : @Initial C}.

(* Drop the structure morphism out of 0. / 从0中去掉结构态射。 *)
Program Definition Coslice_Forget :
  @Coslice C (@initial_obj C I) ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

(*
 Equip an object with its unique arrow out of 0; the triangle condition
 `zero ≈ f ∘ zero` is discharged by [zero_unique] (equivalently, the
 corollary [zero_comp]). 

 --------
 用0为物体配备其独特的箭头；三角形条件 `zero ≈ f ∘ zero` 被 [zero_unique] 解除（等价于推论 [zero_comp]）。
*)
Program Definition Coslice_Section :
  C ⟶ @Coslice C (@initial_obj C I) := {|
  fobj := fun x => (x; zero);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply zero_unique. Qed.

Program Definition coslice_initial_unit (x : @Coslice C (@initial_obj C I)) :
  Coslice_Section (Coslice_Forget x) ≅ x := {|
  to   := (id; _);
  from := (id; _)
|}.
Next Obligation. apply zero_unique. Qed.
Next Obligation. apply zero_unique. Qed.

Corollary coslice_initial_unit_carrier
  (x : @Coslice C (@initial_obj C I)) :
  (`1 (to (coslice_initial_unit x)) ≈ id) ∧
  (`1 (from (coslice_initial_unit x)) ≈ id).
Proof. split; reflexivity. Qed.

(*
 The dual of [Slice_Terminal], at the same strength and for the same
 reason. 

 --------
 [Slice_Terminal] 的对偶，在同样的强度下，并出于同样的原因。
*)
Program Definition Coslice_Initial :
  @Coslice C (@initial_obj C I) ≅[Cat] C := {|
  to   := Coslice_Forget;
  from := Coslice_Section
|}.
(*
 As in Block A the C-side clause is discharged by the default obligation
 tactic — the composite is the identity on objects definitionally — and the
 explicit, sharper form is [Coslice_Initial_strict_section] below. 

 --------
 正如在A区块中，C侧条款通过违约义务策略被解除 —— 复合体在对象上本质上是恒等的 —— 其明确、精确的形式如下所示 [Coslice_Initial_strict_section]。
*)
Next Obligation.
  exists coslice_initial_unit.
  intros x y f; simpl.
  now rewrite id_left, id_right.
Qed.

Lemma Coslice_Initial_strict_section :
  @equiv _ Functor_StrictEq_Setoid (Coslice_Forget ◯ Coslice_Section) Id[C].
Proof.
  exists (fun _ => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

End CosliceInitial.
