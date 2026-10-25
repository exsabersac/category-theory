(*
   * * Ab-enrichment: Enriched over (Ab, ⊗, ℤ) is exactly AbEnriched 

   --------
   * * Ab-加丰富性：在 (Ab, ⊗, ℤ) 上加丰富的正好是 AbEnriched
*)

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §I.8, printed pp. 28–29 (PDF pp. 38–39) — maclane:I.8:def5
 nLab:      https://ncatlab.org/nlab/show/Ab-enriched+category
 Wikipedia: https://en.wikipedia.org/wiki/Preadditive_category

 Mac Lane's remark after the tensor-data definition: an Ab-category
 "can be described completely in these terms" — hom-groups, composition
 morphisms A(b,c) ⊗ A(a,b) → A(a,c), and units ℤ → A(a,a) subject to
 associativity and unit laws.  With Instance/Ab/Tensor.v's tensor and
 Instance/Ab/Monoidal.v's monoidal structure in hand, that remark is a
 theorem of this library:

 [Enriched_Ab_iff_AbEnriched :
 @Enriched Ab Ab_Monoidal ↔
 { C : Category & (LocallyPropositional C * AbEnriched C)%type }]

 in the same Type-valued-↔ form as Construction/Enriched.v's
 [Category_is_Enriched_over_Set] and Construction/Enriched/Two.v's
 [Enriched_Two_preorder].  The two directions:

 - [Enriched_of_AbEnriched]: an [AbEnriched] category (the direct
 Structure/AbCategory.v class) yields tensor data — hom-objects
 are the hom-groups, [eid] sends n to n·id by the integer action,
 [ecompose] is the ⊗-factorization of composition, whose
 bilinearity is exactly [compose_padd_left]/[compose_padd_right].
 - [Category_of_Enriched_Ab] + [AbEnriched_of_Enriched_Ab]: tensor
 data yields a category — composition is [ecompose] at a
 generator, identity is [eid] at 1 — that is [AbEnriched], its
 bilinearity read back off the generator relations of the tensor.

 Design:

 1. EVERY LAW IS A GENERATOR COMPUTATION.  In the forward direction
 the three enrichment equations are morphism equalities out of
 (iterated) tensors, so [tensor_hom_ext]/[tensor_hom_ext2] reduce
 them to generators, where the mediators compute: the unit laws
 become the integer-action equations n·id ∘ f ≈ n·f (an instance
 of [zsmul_hom] at the pre/postcomposition homomorphisms) and the
 associativity equation becomes [comp_assoc].  In the reverse
 direction the SAME three equations are consumed at generator
 arguments, where they compute to the category laws being built.

 2. PRE/POSTCOMPOSITION ARE HOMOMORPHISMS.  [precomp_hom]/
 [postcomp_hom] package (− ∘ f) and (g ∘ −) as [AbHom]s of the
 hom-groups — their additivity is the other half of bilinearity —
 so the ℤ-action bridge n·g ∘ f ≈ n·(g ∘ f) is one application of
 Instance/Ab/Monoidal.v's [zsmul_hom] rather than a fresh
 induction.

 3. BOTH DIRECTIONS ARE IDENTITY ON OBJECTS AND HOM-CARRIERS.  The
 forward direction sets [eobj := obj[C]] and the carrier of each
 hom-object to [x ~> y] itself; the reverse reads them back
 unchanged, and composition at a generator reduces to the original
 [∘].  The correspondence is thus a repackaging of the same data —
 which is exactly Mac Lane's claim — with no equivalence-of-
 categories apparatus invoked, and [Enriched_Ab_itself] below
 exercises the forward direction at the concrete [Ab_AbEnriched].
 (Bare [1%Z] at [carrier ZAb] positions is harmless here because
 the [@ts_gen ZAb …] applications pin the object first, so the
 projection reduces to [Z] before the literal is matched —
 Instance/Ab/Monoidal.v's header note on [ZAb_one] scopes the
 danger to unresolved [carrier ?G] evars.)

 4. NOTHING IS ASSUMED BEYOND THE CLASSES.  Both directions are
 constructions, closed under the global context; the reverse
 direction never inspects [eobj] and the forward one never
 inspects the ambient category beyond its [AbEnriched] fields
 and its [LocallyPropositional] instance (note 5).

 5. A RECORDED STRENGTH CHANGE: THE FORWARD DIRECTION TAKES ONE
 HYPOTHESIS IT DID NOT TAKE BEFORE, AND THE BICONDITIONAL IS
 RESTATED.  An earlier revision of this header quoted
 [Enriched_Ab_iff_AbEnriched] with right-hand side
 [{ C : Category & AbEnriched C }] and described the forward
 direction as running on an arbitrary [AbEnriched] category.
 Since the PR "algebraic carriers are sets" (2026-09-17) an
 [AbObject] carries [cmon_prop], a [PropEquiv] for its carrier
 setoid, and [ehom_ab] takes its carrier setoid straight from
 [C]'s hom-setoid; an arbitrary category supplies no [Prop]
 mirror of its `≈` — in [Cat] an [F ≈ G] IS a family of
 isomorphisms (Lib/Setoid/Propositional.v,
 Instance/Sets/Propositional.v's header).  So the whole of
 Section FromAbEnriched now assumes
 [{LP : LocallyPropositional C}], which is where the hypothesis
 belongs: at the PASSAGE from the internal enrichment to a
 concrete object of [Ab], not in [AbEnriched] itself, which is
 untouched and keeps the ambient `≈` (the SCOPE paragraph of
 Structure/Complete.v's size note, item 4).

 The eight constants of that section carry it: [ehom_ab],
 [precomp_hom], [postcomp_hom], [zsmul_precomp], [zsmul_postcomp],
 [ab_eid], [ab_ecompose] and [Enriched_of_AbEnriched].  The
 biconditional is restated to match, its right-hand side now
 [{ C : Category & (LocallyPropositional C * AbEnriched C)%type }].
 That extra factor is not a hypothesis smuggled in: the REVERSE
 direction produces it ([LocallyPropositional_of_Enriched_Ab]),
 so the equivalence is the same one with its content made
 explicit.  Nothing in Section ToAbEnriched gained a hypothesis.
 The class is discharged by resolution at every concrete ambient:
 [Ab_LocallyPropositional] (Instance/Ab.v) is what
 [Enriched_Ab_itself] uses, and [RMod_LocallyPropositional]
 (Instance/Mod.v), [CMon_LocallyPropositional]
 (Instance/CMon.v) and [DeloopRig_LocallyPropositional]
 (Theory/Algebra/Rig.v) serve the others. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第二版，
 §I.8，印刷页 28–29（PDF 页 38–39）— maclane:I.8:def5
 nLab：https://ncatlab.org/nlab/show/Ab-enriched+category 
 维基百科：https://en.wikipedia.org/wiki/Preadditive_category 

 Mac Lane 在张量数据定义之后的评论：一个 Ab-范畴
 “可以完全用这些术语描述”——同态群，组合
 态射 A(b,c) ⊗ A(a,b) → A(a,c)，以及单位 ℤ → A(a,a)，满足
 结合律和单位律。结合 Instance/Ab/Tensor.v 的张量结构和
 Instance/Ab/Monoidal.v 的单体结构，这一评论在该库中成为
 一个定理：

 [Enriched_Ab_iff_AbEnriched :
 @Enriched Ab Ab_Monoidal ↔
 { C : Category & (LocallyPropositional C * AbEnriched C)%type }]以与 Construction/Enriched.v 的 [Category_is_Enriched_over_Set] 和 Construction/Enriched/Two.v 的 [Enriched_Two_preorder] 相同的 Type-valued-↔ 形式。这两个方向：

 - [Enriched_of_AbEnriched] ：一个 [AbEnriched] 类别（直接的 Structure/AbCategory.v 类）生成张量数据——同态对象是同态群，[eid] 通过整数作用将 n 送到 n·id，[ecompose] 是组合的 ⊗-分解，其双线性恰好是 [compose_padd_left] / [compose_padd_right]。
 - [Category_of_Enriched_Ab] + [AbEnriched_of_Enriched_Ab] ：张量数据生成一个类别——组合在一个生成元处是 [ecompose]，单位在 1 处是 [eid]——即 [AbEnriched]，其双线性通过张量的生成元关系读回。

 设计:1. 每一条定律都是一个生成器计算。在正向过程中，三个增广方程是从（迭代）张量出的态射同等式，因此 [tensor_hom_ext] / [tensor_hom_ext2] 将它们化简为生成器，其中介子计算：单位律变为整数作用方程 n·id ∘ f ≈ n·f（在预/后组合同态的情况下是 [zsmul_hom] 的一个实例），结合律方程变为 [comp_assoc]。在反向过程中，同样的三条方程在生成器参数处被使用，其中它们计算为正在构建的范畴律。2. 前/后合成为同态。[precomp_hom]/[postcomp_hom] 将 (− ∘ f) 和 (g ∘ −) 作为同态群的 [AbHom] —— 它们的加法性是双线性另一半 —— 因此 ℤ-作用桥 n·g ∘ f ≈ n·(g ∘ f) 是 Instance/Ab/Monoidal.v 的 [zsmul_hom] 的一次应用，而不是一个新的归纳。3. 双向在对象和 Hom-载体上都是恒等的。正向将 [eobj := obj[C] 和每个 hom 对象的载体设置为 [x ~> y] 本身；反向则将它们原样读取回来，在生成元处的组合简化为原始的 [∘]。因此，这种对应关系只是对相同数据的一种重新打包——这正是 Mac Lane 的主张——没有调用范畴等价的机制，而下面的 [Enriched_Ab_itself] 在具体的 [Ab_AbEnriched] 上执行正向。(在 [carrier ZAb] 位置的裸 [1%Z] 在这里是无害的，因为 [@ts_gen ZAb …] 的应用先固定了对象，所以在匹配字面值之前投影简化为 [Z] ——Instance/Ab/Monoidal.v 的头部注释关于 [ZAb_one] 将危险限制在未解决的 [carrier ?G] evars 上。)4. 除了类之外，不做任何假设。两个方向都是构造，且在全局上下文中封闭；逆向从不检查 [eobj]，而正向从不检查环境类别中其 [AbEnriched] 字段和 [LocallyPropositional] 实例之外的内容（见注5）。5. 一个记录的强度变化：正向方向采取了之前未采取的一个假设，并且双条件被重述。该标题的早期修改引用了 [Enriched_Ab_iff_AbEnriched]，其右侧为 [{ C : Category & AbEnriched C }]，并将正向方向描述为在任意 [AbEnriched] 类别上运行。自从 PR “代数载体是集合”（2026-09-17）以来，[AbObject] 承载 [cmon_prop]，一个 [PropEquiv] 对于其载体同构集，而 [ehom_ab] 直接从 [C] 的同态集获取其载体同构集；任意类别不提供其 `≈` 的 [Prop] 镜像——在 [Cat] 中，[F ≈ G] 是同构族（Lib/Setoid/Propositional.v，Instance/Sets/Propositional.v 的标题）。因此，FromAbEnriched 的整个部分现在假设 [{LP : LocallyPropositional C}]，这也是假设所属的地方：在从内部丰富到 [Ab] 的具体对象的过渡中，而不是在 [AbEnriched] 本身，它保持不变，并且保持环境 `≈`（Structure/Complete.v 的范围段的大小说明，第4项）。该部分的八个常量如下：[ehom_ab]、[precomp_hom]、[postcomp_hom]、[zsmul_precomp]、[zsmul_postcomp]、[ab_eid]、[ab_ecompose] 和 [Enriched_of_AbEnriched]。该双条件也重新陈述以匹配，其右侧现在为 [{ C : Category & (LocallyPropositional C * AbEnriched C)%type }]。这个额外因素不是偷偷加入的假设：反向方向会产生它（[LocallyPropositional_of_Enriched_Ab]），所以等价关系就是那个内容明确化的相同等价关系。ToAbEnriched 节中的任何内容都没有获得假设。该类通过每个具体环境的解析被解除：[Ab_LocallyPropositional]（Instance/Ab.v）是 [Enriched_Ab_itself] 使用的，而 [RMod_LocallyPropositional]（Instance/Mod.v）、[CMon_LocallyPropositional]（Instance/CMon.v）和 [DeloopRig_LocallyPropositional]（Theory/Algebra/Rig.v）用于其他情况。
*)

Require Import Coq.ZArith.BinInt.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Monoidal.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** From an AbEnriched category to tensor data / * ** 从 AbEnriched 范畴到张量数据 *)

Section FromAbEnriched.

Context {C : Category} {A : AbEnriched C}.

(*
 [LP] is new since the PR "algebraic carriers are sets" (2026-09-17): an
 [AbObject] carries [cmon_prop], and [ehom_ab] below takes its carrier
 setoid straight from [C]'s hom-setoid, which an arbitrary category does not
 supply a [Prop] mirror for (Instance/Sets/Propositional.v's header records
 the measurement for [Cat]).  It is a class, so at [Ab] and at [RMod R] it
 is discharged by resolution from the instances in Instance/Ab.v and
 Instance/Mod.v.  Adjunction/Additive.v's [hom_ab] takes the same
 hypothesis, for the same reason. 

 --------
 [LP] 自 PR “代数承载体是集合” (2026-09-17) 以来是新的：一个 [AbObject] 承载 [cmon_prop]，并且下面的 [ehom_ab] 直接从 [C] 的同态集合取得它的承载体集合，而任意范畴并不提供 [Prop] 镜像（Instance/Sets/Propositional.v 的头记录记录了 [Cat] 的测量）。它是一个类，所以在 [Ab] 和 [RMod R] 时，它通过 Instance/Ab.v 和 Instance/Mod.v 中的实例解析被释放。Adjunction/Additive.v 的 [hom_ab] 因同样的原因采用相同的假设。
*)
Context {LP : LocallyPropositional C}.

(*
 The hom-group of a hom-set: Structure/AbCategory.v's fields, packaged
 as an object of Ab. 

 --------
 Hom-集合的 Hom-群：Structure/AbCategory.v 的字段，作为 Ab 的一个对象打包。
*)
Definition ehom_ab (x y : C) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := x ~> y; is_setoid := @homset C x y |};
    cmon_zero := @pzero C _ x y;
    cmon_plus := @padd C _ x y;
    cmon_plus_respects := @padd_respects C _ x y;
    cmon_plus_assoc := @padd_assoc C _ x y;
    cmon_plus_comm := @padd_comm C _ x y;
    cmon_plus_zero_l := @padd_zero_left C _ x y;
    cmon_prop := locally_prop x y
  |};
  ab_neg := @abneg C A x y;
  ab_neg_respects := @abneg_respects C A x y;
  ab_neg_left := fun f =>
    transitivity (@padd_comm C _ x y (abneg f) f) (padd_abneg f)
|}.

(*
 Precomposition with f, as a homomorphism of hom-groups: additivity is
 [compose_padd_right], zero-preservation [compose_pzero_left]. 

 --------
 与 f 的前组合，作为同态群的同态：可加性是 [compose_padd_right]，零保持是 [compose_pzero_left]。
*)
Program Definition precomp_hom {x y z : C} (f : x ~> y) :
  AbHom (ehom_ab y z) (ehom_ab x z) := {|
  cmon_map := {| morphism := fun g : y ~> z => g ∘ f |}
|}.
Next Obligation.
  intros x y z f g g' Hg.
  exact (compose_respects _ _ Hg _ _ (reflexivity f)).
Qed.
Next Obligation.
  intros x y z f; simpl.
  exact (@compose_pzero_left C _ x y z f).
Qed.
Next Obligation.
  intros x y z f g g'; simpl.
  exact (@compose_padd_right C _ x y z g g' f).
Qed.

(*
 Postcomposition with g, likewise: [compose_padd_left] and
 [compose_pzero_right]. 

 --------
 与 g 的后合成同样：[compose_padd_left] 和 [compose_pzero_right]。
*)
Program Definition postcomp_hom {x y z : C} (g : y ~> z) :
  AbHom (ehom_ab x y) (ehom_ab x z) := {|
  cmon_map := {| morphism := fun f : x ~> y => g ∘ f |}
|}.
Next Obligation.
  intros x y z g f f' Hf.
  exact (compose_respects _ _ (reflexivity g) _ _ Hf).
Qed.
Next Obligation.
  intros x y z g; simpl.
  exact (@compose_pzero_right C _ x y z g).
Qed.
Next Obligation.
  intros x y z g f f'; simpl.
  exact (@compose_padd_left C _ x y z g f f').
Qed.

(*
 The ℤ-action commutes with composition on either side — instances of
 [zsmul_hom] at the two homomorphisms above (design note 2). 

 --------
 ℤ-作用与任一侧的复合运算交换——上面两个同态处的 [zsmul_hom] 实例（设计说明 2）。
*)
Lemma zsmul_precomp {x y z : C} (n : Z) (g : y ~> z) (f : x ~> y) :
  zsmul (ehom_ab y z) n g ∘ f ≈ zsmul (ehom_ab x z) n (g ∘ f).
Proof.
  exact (zsmul_hom (precomp_hom f) n g).
Qed.

Lemma zsmul_postcomp {x y z : C} (n : Z) (g : y ~> z) (f : x ~> y) :
  g ∘ zsmul (ehom_ab x y) n f ≈ zsmul (ehom_ab x z) n (g ∘ f).
Proof.
  exact (zsmul_hom (postcomp_hom g) n f).
Qed.

(*
 The unit ℤ → A(x,x): n ↦ n·id.  Additivity in n is [zsmul_add]. 

 --------
 单位 ℤ → A(x,x)：n ↦ n·id。在 n 上的可加性是 [zsmul_add]。
*)
Program Definition ab_eid (x : C) : AbHom ZAb (ehom_ab x x) := {|
  cmon_map := {| morphism := fun n : Z => zsmul (ehom_ab x x) n (@id C x) |}
|}.
Next Obligation.
  intros x n m Hnm.
  rewrite (ZAb_eq n m Hnm).
  reflexivity.
Qed.
Next Obligation.
  intros x; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x n m; simpl.
  exact (zsmul_add (ehom_ab x x) n m (@id C x)).
Qed.

(*
 Composition A(y,z) ⊗ A(x,y) → A(x,z): the ⊗-factorization of ∘, its
 bilinearity the two composition-bilinearity fields of Preadditive. 

 --------
 组合 A(y,z) ⊗ A(x,y) → A(x,z)：∘ 的 ⊗ 分解，其双线性是 Preadditive 的两个组合双线性场。
*)
Program Definition ab_ecompose (x y z : C) :
  AbHom (AbTensor (ehom_ab y z) (ehom_ab x y)) (ehom_ab x z) :=
  tensor_ump (@Build_Bilinear (ehom_ab y z) (ehom_ab x y) (ehom_ab x z)
    (fun g f => g ∘ f) _ _ _).
Next Obligation.
  intros x y z g g' f; simpl.
  exact (@compose_padd_right C _ x y z g g' f).
Qed.
Next Obligation.
  intros x y z g f f'; simpl.
  exact (@compose_padd_left C _ x y z g f f').
Qed.

(*
 The enrichment.  Each equation is [tensor_hom_ext] to generators, a
 mediator computation, and a category/action law (design note 1).

 AN EARLIER REVISION took only [C] and [A]: since the PR "algebraic
 carriers are sets" (2026-09-17) this is the section's [LP] as well, and
 [Proof using] records all three.  Design note 5 of the header names the
 eight constants of this section that gained it and what discharges it. 

 --------
 丰富化。每个方程都是 [tensor_hom_ext] 对生成元、中介计算和类别/作用律（设计说明 1）。

 早期的修订只采用了 [C] 和 [A]：由于 PR “代数载体是集合”（2026-09-17），这一节现在也是 [LP]，并且 [Proof using] 记录了所有三个。页眉的设计说明 5 指明了本节的八个获得它的常数及其释放情况。
*)
Definition Enriched_of_AbEnriched : @Enriched Ab Ab_Monoidal.
Proof using A C LP.
  unshelve refine
    (@Build_Enriched Ab Ab_Monoidal obj[C] ehom_ab ab_eid ab_ecompose
       _ _ _).
  - (* eid_left : ecompose ∘ eid ⨂ id ≈ unit_left / eid_left : ecompose ∘ eid ⨂ id ≈ unit_left *)
    intros x y s; revert s.
    apply tensor_hom_ext.
    intros n f; simpl.
    refine (transitivity (zsmul_precomp n (@id C y) f) _).
    exact (zsmul_respects (ehom_ab x y) n _ _ (id_left f)).
  - (* eid_right : ecompose ∘ id ⨂ eid ≈ unit_right / eid_right : ecompose ∘ id ⨂ eid ≈ unit_right *)
    intros x y s; revert s.
    apply tensor_hom_ext.
    intros f n; simpl.
    refine (transitivity (zsmul_postcomp n f (@id C x)) _).
    exact (zsmul_respects (ehom_ab x y) n _ _ (id_right f)).
  - (* ecompose_assoc / 重组成联合 *)
    intros x y z w s; revert s.
    apply tensor_hom_ext2.
    intros h g f; simpl.
    exact (symmetry (comp_assoc h g f)).
Defined.

End FromAbEnriched.

(* * ** From tensor data to an AbEnriched category / * ** 从张量数据到 AbEnriched 范畴 *)

Section ToAbEnriched.

Context (E : @Enriched Ab Ab_Monoidal).

(*
 The category: composition is [ecompose] at a generator, identity is
 [eid] at 1.  The laws are E's equations consumed at generators, where
 both sides compute. 

 --------
 该范畴：在一个生成元处的组合是 [ecompose]，单位元是在 1 处的 [eid]。公理是生成元处消耗的 E 方程，其中两边都进行了计算。
*)
Program Definition Category_of_Enriched_Ab : Category := {|
  obj := @eobj Ab Ab_Monoidal E;
  hom := fun x y => carrier (@ehom Ab Ab_Monoidal E x y);
  homset := fun x y =>
    is_setoid (cmon_setoid (ab_cmon (@ehom Ab Ab_Monoidal E x y)));
  id := fun x => cmon_map (@eid Ab Ab_Monoidal E x) 1%Z;
  compose := fun x y z g f =>
    cmon_map (@ecompose Ab Ab_Monoidal E x y z) (ts_gen g f)
|}.
Next Obligation.
  (* compose_respects / 致敬 *)
  intros x y z g g' Hg f f' Hf.
  exact (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
           _ _ (te_gen Hg Hf)).
Qed.
Next Obligation.
  (* id_left: eid_left at the generator ts_gen 1 f / id_left：eid_left 在发电机 ts_gen 1 f *)
  intros x y f.
  pose proof (@eid_left Ab Ab_Monoidal E x y
                (@ts_gen ZAb (@ehom Ab Ab_Monoidal E x y) 1%Z f)) as Hl.
  simpl in Hl.
  refine (transitivity Hl _).
  exact (zsmul_one (@ehom Ab Ab_Monoidal E x y) f).
Qed.
Next Obligation.
  (*
 id_right: eid_right at the generator ts_gen f 1 

 --------
 id_right：在发电机 ts_gen f 1 上的 eid_right
*)
  intros x y f.
  pose proof (@eid_right Ab Ab_Monoidal E x y
                (@ts_gen (@ehom Ab Ab_Monoidal E x y) ZAb f 1%Z)) as Hr.
  simpl in Hr.
  refine (transitivity Hr _).
  exact (zsmul_one (@ehom Ab Ab_Monoidal E x y) f).
Qed.
Next Obligation.
  (*
 comp_assoc: ecompose_assoc at ts_gen (ts_gen f g) h 

 --------
 comp_assoc: 在 ts_gen (ts_gen f g) h 上使用 ecompose_assoc
*)
  intros x y z w f g h.
  pose proof (@ecompose_assoc Ab Ab_Monoidal E x y z w
                (@ts_gen (AbTensor (@ehom Ab Ab_Monoidal E z w)
                                   (@ehom Ab Ab_Monoidal E y z))
                         (@ehom Ab Ab_Monoidal E x y)
                   (@ts_gen (@ehom Ab Ab_Monoidal E z w)
                            (@ehom Ab Ab_Monoidal E y z) f g) h)) as Ha.
  simpl in Ha.
  exact (symmetry Ha).
Qed.
Next Obligation.
  (* comp_assoc_sym / 复合_结合_对称 *)
  intros x y z w f g h.
  pose proof (@ecompose_assoc Ab Ab_Monoidal E x y z w
                (@ts_gen (AbTensor (@ehom Ab Ab_Monoidal E z w)
                                   (@ehom Ab Ab_Monoidal E y z))
                         (@ehom Ab Ab_Monoidal E x y)
                   (@ts_gen (@ehom Ab Ab_Monoidal E z w)
                            (@ehom Ab Ab_Monoidal E y z) f g) h)) as Ha.
  simpl in Ha.
  exact Ha.
Qed.

(*
 The AbEnriched structure: hom-group operations from the hom-objects;
 bilinearity of composition is the generator relations of the tensor
 pushed through [ecompose]'s homomorphism property. 

 --------
 AbEnriched 结构：来自同态对象的同态群操作；组合的双线性是张量的生成关系，通过 [ecompose] 的同态性质传递。
*)
(*
 The category built from tensor data is LOCALLY PROPOSITIONAL for free: its
 hom-setoid IS the carrier setoid of an object of [Ab], which since the PR
 "algebraic carriers are sets" (2026-09-17) carries [cmon_prop]. 

 --------
 由张量数据构建的范畴是局部命题性的：它的同态集合体是  [Ab] 对象的承载集合体，由于 PR “代数承载是集合”（2026-09-17），它承载  [cmon_prop] 。
*)
Definition LocallyPropositional_of_Enriched_Ab :
  LocallyPropositional Category_of_Enriched_Ab.
Proof.
  constructor.
  intros x y.
  exact (cmon_prop (ab_cmon (@ehom Ab Ab_Monoidal E x y))).
Defined.

Program Definition AbEnriched_of_Enriched_Ab :
  AbEnriched Category_of_Enriched_Ab := {|
  abenriched_preadditive := {|
    padd := fun x y f g =>
      cmon_plus (ab_cmon (@ehom Ab Ab_Monoidal E x y)) f g;
    pzero := fun x y =>
      cmon_zero (ab_cmon (@ehom Ab Ab_Monoidal E x y))
  |};
  abneg := fun x y f => ab_neg (@ehom Ab Ab_Monoidal E x y) f
|}.
Next Obligation.
  intros x y f g h.
  exact (cmon_plus_assoc _ f g h).
Qed.
Next Obligation.
  intros x y f g.
  exact (cmon_plus_comm _ f g).
Qed.
Next Obligation.
  intros x y f.
  exact (cmon_plus_zero_l _ f).
Qed.
Next Obligation.
  (*
 compose_padd_left: h ∘ (f + g) ≈ h ∘ f + h ∘ g 

 --------
 compose_padd_left: h ∘ (f + g) ≈ h ∘ f + h ∘ g
*)
  intros x y z h f g; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (te_bilin_r h f g)) _).
  exact (cmon_map_plus (@ecompose Ab Ab_Monoidal E x y z)
           (ts_gen h f) (ts_gen h g)).
Qed.
Next Obligation.
  (*
 compose_padd_right: (f + g) ∘ h ≈ f ∘ h + g ∘ h 

 --------
 compose_padd_right: (f + g) ∘ h ≈ f ∘ h + g ∘ h
*)
  intros x y z f g h; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (te_bilin_l f g h)) _).
  exact (cmon_map_plus (@ecompose Ab Ab_Monoidal E x y z)
           (ts_gen f h) (ts_gen g h)).
Qed.
Next Obligation.
  (* compose_pzero_left: 0 ∘ f ≈ 0 / compose_pzero_left: 0 ∘ f ≈ 0 *)
  intros x y z f; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (ts_gen_zero_l f)) _).
  exact (cmon_map_zero (@ecompose Ab Ab_Monoidal E x y z)).
Qed.
Next Obligation.
  (* compose_pzero_right: f ∘ 0 ≈ 0 / compose_pzero_right: f ∘ 0 ≈ 0 *)
  intros x y z f; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (ts_gen_zero_r f)) _).
  exact (cmon_map_zero (@ecompose Ab Ab_Monoidal E x y z)).
Qed.
Next Obligation.
  (* padd_abneg: f + (− f) ≈ 0 / padd_abneg: f + (− f) ≈ 0 *)
  intros x y f.
  exact (ab_neg_right (@ehom Ab Ab_Monoidal E x y) f).
Qed.

End ToAbEnriched.

(** ** The correspondence / ** 通讯 *)

(*
 Mac Lane's "can be described completely in these terms", as a
 Type-valued equivalence of the two presentations — the same shape as
 [Category_is_Enriched_over_Set] and [Enriched_Two_preorder]. 

 --------
 Mac Lane 的“可以用这些术语完全描述”，作为两种表述的类型值等价——与 [Category_is_Enriched_over_Set] 和 [Enriched_Two_preorder] 的形状相同。
*)
(*
 The forward direction, exercised at the concrete witness: Ab is an
 Ab-category, so it is enriched over itself. 

 --------
 正向方向，在具体证人上应用：Ab 是一个 Ab-范畴，所以它是自我充实的。
*)
Definition Enriched_Ab_itself : @Enriched Ab Ab_Monoidal :=
  @Enriched_of_AbEnriched Ab Ab_AbEnriched Ab_LocallyPropositional.

(*
 AN EARLIER REVISION stated the right-hand side as [{ C : Category &
 AbEnriched C }].  Since the PR "algebraic carriers are sets" (2026-09-17)
 the objects of [Ab] are abelian groups on SETS -- their `≈` is
 propositional -- so a category enriched over [Ab] necessarily has
 propositional hom-setoids, and conversely an [AbEnriched] category is
 enriched over [Ab] only if it does.  The extra factor states that, and it
 is not a hypothesis smuggled in: the forward direction PRODUCES it
 ([LocallyPropositional_of_Enriched_Ab] below), so the biconditional is the
 same equivalence with its content made explicit. 

 --------
 早期的修订将右侧表示为 [{ C : Category & AbEnriched C }]。自从 PR “代数载体是集合” (2026-09-17) 后，[Ab] 的对象是集合上的阿贝尔群 —— 它们的 `≈` 是命题性的 —— 因此一个在 [Ab] 上富集的范畴必然具有命题性的 Hom 集合体，反之，一个 [AbEnriched] 范畴仅在它也具有该性质时才在 [Ab] 上富集。额外的因素说明了这一点，这并不是偷偷引入的假设：正向方向会产生它（见下文 [LocallyPropositional_of_Enriched_Ab]），因此该双条件与其内容明确化后的等价是相同的。
*)
Theorem Enriched_Ab_iff_AbEnriched :
  @Enriched Ab Ab_Monoidal ↔
  { C : Category & (LocallyPropositional C * AbEnriched C)%type }.
Proof.
  split.
  - intro E.
    exact (Category_of_Enriched_Ab E;
           (LocallyPropositional_of_Enriched_Ab E,
            AbEnriched_of_Enriched_Ab E)).
  - intros [C [LP A]].
    exact (@Enriched_of_AbEnriched C A LP).
Defined.
