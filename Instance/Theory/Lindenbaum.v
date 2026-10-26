Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.

Generalizable All Variables.

(* * * The Lindenbaum category of an elementary theory / * * 初等理论的林登鲍姆范畴 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §IV.6, printed p. 98, Exercise 2
 (catalog id maclane:IV.6:ex2).  Verbatim from the printed page:

 “In some elementary theory T, consider the set S = {p, q, ...} of
 sentences of T as a preorder, with p ≤ q meaning ”p entails q“
 (i.e., q is a consequence of p on the basis of the axioms of T).
 Prove that S is a cartesian closed category, with product given by
 conjunction and exponential q^p given by ”p implies q“.”

 (The book prints the relation symbol as the double-bar ≦; it is
 rendered ≤ above.  The exercise sits on the same page as Exercises 1,
 3, 4 and 5, none of which is treated here.)

 nLab:      https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra
 nLab:      https://ncatlab.org/nlab/show/Heyting+algebra
 nLab:      https://ncatlab.org/nlab/show/deduction+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Lindenbaum%E2%80%93Tarski_algebra
 Wikipedia: https://en.wikipedia.org/wiki/Deduction_theorem
 Book:      Lambek and Scott, “Introduction to Higher Order Categorical
 Logic”, Cambridge Studies in Advanced Mathematics 7, 1986,
 Part I §§1-3 (the deductive system of a cartesian closed
 category).

 ** What this file builds

 [Sent V] is a deliberately MINIMAL propositional syntax over a type V
 of atoms: an atom former, truth, conjunction and implication, and
 nothing else.  That is the whole of what Mac Lane's exercise needs —
 product is conjunction, terminal is truth, exponential is implication
 — and a full first-order language (quantifiers, equality, function
 and relation symbols, a signature, substitution) is OUT OF SCOPE
 here.  Nothing below is claimed about first-order theories, and
 [Sent] is not proposed as a model of one.

 A theory is a bare set of sentences, [Theo V := Sent V -> Prop]; no
 deductive closure is imposed on it, and no consistency is required.
 Entailment RELATIVE to that theory, [Entails T p q], is Mac Lane's
 “q is a consequence of p on the basis of the axioms of T”: it is an
 inductive family in Prop, so that [Instance/Proset.v]'s [Proset] —
 whose relation argument is a stdlib [relation A], hence Prop-valued —
 applies directly, and the resulting category is thin ([lind_thin])
 with no truncation or squashing anywhere.

 ** The design decision that makes the exercise cheap

 The rules of [Entails] are given in NATURAL DEDUCTION form, and this
 was a choice rather than the only option.  The consequence is that the
 deduction theorem is the CONSTRUCTOR [ent_curry] and evaluation is the
 CONSTRUCTOR [ent_eval], so the currying bijection of a cartesian
 closed category is available with no induction at all.  Presented
 instead as a Hilbert system — K and S plus modus ponens axiomatise
 the IMPLICATIONAL fragment, and [Entails] carries conjunction and
 truth as well, so a Hilbert presentation matching it needs analogues
 of [ent_top], [ent_pair], [ent_fst] and [ent_snd] besides — the
 deduction theorem is a metatheorem whose proof is an induction over
 derivations, and that induction would then have to be carried out
 before [Lind_Closed] could be stated.  That the two presentations
 define the same relation is the standard equivalence and is NOT
 established here.

 ** Which rule each structure consumes (measured, not asserted)

 Each of the nine constructors was deleted in turn from [Entails] and
 the file recompiled up to the end of section (D); the first site that
 then stopped resolving is recorded here.

 ent_refl   -> [entails_PreOrder], i.e. [id] of [Lind]
 ent_cut    -> [entails_PreOrder], i.e. [compose] of [Lind]
 ent_ax     -> NOTHING: sections (A)-(D) compile unchanged without it
 ent_top    -> [Lind_Terminal]  ([one])
 ent_pair   -> [Lind_Cartesian] ([fork])
 ent_fst    -> [Lind_Cartesian] ([exl])
 ent_snd    -> [Lind_Cartesian] ([exr])
 ent_curry  -> [Lind_Closed]    ([to exp_iso])
 ent_eval   -> [lind_uncurry],  i.e. [from exp_iso]

 So exactly eight of the nine are consumed by the four structures, and
 the ninth, the axiom rule [ent_ax], is what makes the theory parameter
 do any work at all: it is the only rule whose case in
 [entails_weaken] consumes the theory, and the only one used on the
 target side of section (G)'s [no_full_functor_empty_to_all].  The
 section is not built from it alone — [entails_weaken] is an induction
 applying all nine constructors by name — but it is the rule the
 section turns on, where two different axiom sets are shown to give
 two categories that are not equivalent.  No rule was dropped as
 redundant, and no rule is claimed
 here to be underivable from the others — that would take a countermodel
 per rule, and none is built.

 ** What is free because the category is thin

 Every hom-setoid of [Lind T] is trivially true ([Proset]'s [equiv] is
 [fun _ _ => True]), so [lind_thin] holds by [I].  Consequently every
 obligation of the four structures is discharged by [Program]'s
 default tactic with no proof written in this file.  Counted off
 [Print Module], they are fourteen: [one_unique] for [Lind_Terminal];
 [fork_respects] and [ump_products] for [Lind_Cartesian]; for
 [Lind_Closed] the two [proper_morphism] certificates of the transpose
 and its inverse (they are morphisms of [Sets]), both isomorphism laws
 of [exp_iso], and [ump_exponents']; and [fmap_respects], [fmap_id],
 [fmap_comp] three times over for each of [LindSound] and
 [LindWeaken].  So uniqueness of the transpose is free, and is not
 proved here because there is nothing to prove; the four structures
 carry exactly the data of the nine rules and no equational content.

 ** The comparison with Instance/Props.v

 [Instance/Props.v] is the semantic side: its objects are Props,
 its arrows implications, and its header already records that cartesian
 closure there is the deduction theorem.  The bridge is a valuation:
 given [val : V -> Prop] under which every axiom of T holds,
 [ent_soundness] carries derivations to implications, and [LindSound]
 packages that as a functor [Lind T ⟶ Props].  Its measured strength,
 with nothing claimed beyond what compiles below:

 - it is a functor (all three functor laws are free, Props is thin);
 - it preserves the terminal object, binary products and
 exponentials ON THE NOSE, at Leibniz equality of objects
 ([sound_terminal], [sound_product], [sound_exponent], all
 [eq_refl]);
 - it is Faithful, but VACUOUSLY: the source is thin, so [f ≈ g]
 there is [True] and EVERY functor out of [Lind T] is faithful —
 that general statement is [lind_any_Faithful], and
 [LindSound_Faithful] is literally it;
 - it is NOT full ([sound_not_Full]) and NOT essentially surjective
 ([sound_not_EssentiallySurjective]), hence not an equivalence,
 both refuted at the empty theory under the valuation that sends
 every atom to True.

 So the CCC structure of [Props] is reproduced on the nose by the
 comparison, while the two refutations show that THIS comparison is
 neither full nor essentially surjective.  They are statements about
 the single functor [LindSound T_empty val_true val_true_empty], and
 no constant here says that [Lind T_empty] and [Props] are
 inequivalent.  Fullness would be COMPLETENESS of the calculus with
 respect to a single valuation, which is a strictly stronger statement
 than the exercise asks for and is refuted here rather than attempted.

 ** Engineering findings

 [Lib.v] sets [Uniform Inductive Parameters] for the whole
 development, so inside the body of [Inductive Sent (V : Type)] the
 name [Sent] already stands for [Sent V]; writing the parameter
 explicitly there is rejected with “Illegal application
 (Non-functional construction)”, an error that names the parameter but
 neither the flag nor the cause: it reports [Sent] as a non-functional
 term applied to [V], without saying that [Sent] has already absorbed
 the parameter.  The same applies inside [Entails].

 [PreOrder] in this file's scope is [CRelationClasses.PreOrder], the
 crelation-valued one, because [Category.Lib] exports it; the one
 [Proset] wants is the Prop-valued [RelationClasses.PreOrder], written
 qualified in [entails_PreOrder].  No extra [Require] is needed for the
 qualified name, since that module is already loaded transitively.

 [lind_thin] is proved here in one term rather than by requiring
 [Instance/Proset/Order.v]'s [proset_thin], which is the donor and
 applies to [Lind T] by conversion.  That is a measurement, not a
 preference: the transitive in-project closure of this file is 27
 modules, and adding [Instance/Proset/Order] takes it to 35. 

 --------
 Mac Lane, 《为工作数学家准备的范畴论》，第2版，Springer GTM 5, 1998, §IV.6, 印刷第98页，练习2（目录编号 maclane:IV.6:ex2）。逐字翻译自印刷页：

 “在某个初等理论T中，考虑句子集合S = {p, q, ...}作为一个预序集，其中p ≤ q表示‘p蕴含q’（即，q在T的公理基础上是p的一个推论）。证明S是一个笛卡尔闭范畴，其积由合取给出，并且指数对象q^p由‘p蕴含q’给出。”

 （书中打印的关系符号为双杠≦；上文中渲染为≤。该练习与练习1、3、4和5位于同一页，本处未涉及其他练习。）nLab:       https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra
 nLab:       https://ncatlab.org/nlab/show/Heyting+algebra
 nLab:       https://ncatlab.org/nlab/show/deduction+theorem
 Wikipedia:  https://en.wikipedia.org/wiki/Lindenbaum%E2%80%93Tarski_algebra
 Wikipedia:  https://en.wikipedia.org/wiki/Deduction_theorem
 书籍:      Lambek 和 Scott, 《高阶范畴逻辑导论》, 剑桥高等数学研究丛书 7, 1986, 第 I 部 §§1-3（笛卡尔闭范畴的演绎系统）。

 ** 本文件构建的内容[Sent V] 是一个刻意设计的极简命题语法，基于一个类型为 V 的原子集合：包含原子构造、真值、合取和蕴含，仅此而已。这就是 Mac Lane 练习所需要的全部内容——积对应合取，终结元对应真值，指数对应蕴含——完整的一阶语言（量词、等号、函数和关系符号、符号表、替换）不在讨论范围内。以下内容不涉及一阶理论，[Sent] 也不是作为一阶理论的模型提出的。一个理论是一组简单的句子，[Theo V := Sent V -> Prop]；没有对它施加演绎闭包，也不要求一致性。相对于该理论的蕴涵，[Entails T p q]，是麦克莱恩的“q 是基于 T 的公理的 p 的结果”: 它是 Prop 中的一个归纳族，因此 [Instance/Proset.v] 的 [Proset] —— 其关系参数是 stdlib [relation A]，因此取值类型为 Prop —— 可以直接应用，并且生成的范畴是稀薄的 ([lind_thin])，在任何地方都没有截断或压缩。

 ** 使该练习成本低的设计决策[Entails] 的规则以自然演绎的形式给出，这是一个选择而非唯一的方案。其结果是演绎定理是构造子 [ent_curry]，求值是构造子 [ent_eval]，因此闭笛卡尔范畴的柯里化双射可以在不使用归纳的情况下使用。若改为希尔伯特系统表示——K 和 S 加上假言推理对蕴涵片段进行公理化，而 [Entails] 同时涵盖了合取和真值，因此与之匹配的希尔伯特表示还需要 [ent_top]、[ent_pair]、[ent_fst] 和 [ent_snd] 的类似物——演绎定理是一个元定理，其证明是对推导的归纳，而该归纳必须在陈述 [Lind_Closed] 之前完成。两个展示定义相同关系是标准等价性，但这里并未建立该等价性。

 ** 每个结构所使用的规则（测量的，而非断言的）

 九个构造器中的每一个都依次从 [Entails] 中删除，并将文件重新编译直到(D)节结束；随后停止解析的第一个位置在这里记录。

 ent_refl   ->  [entails_PreOrder] ，即 [id] 的 [Lind]
 ent_cut    ->  [entails_PreOrder] ，即 [compose] 的 [Lind]
 ent_ax     -> 无：A-(D) 节在没有它的情况下编译不变
 ent_top    ->  [Lind_Terminal] （ [one] ）
 ent_pair   ->  [Lind_Cartesian] （ [fork] ）
 ent_fst    ->  [Lind_Cartesian] （ [exl] ）
 ent_snd    ->  [Lind_Cartesian] （ [exr] ）
 ent_curry  ->  [Lind_Closed] （ [to exp_iso] ）
 ent_eval   ->  [lind_uncurry] ，即 [from exp_iso]所以正好九个中的八个被四个结构消耗，而第九个，即公理规则 [ent_ax]，使理论参数能够真正起作用：它是唯一一个在 [entails_weaken] 中其情形会消耗理论的规则，也是唯一一个在 (G) 节的 [no_full_functor_empty_to_all] 目标端使用的规则。该节并非仅由它构建——[entails_weaken] 是一个通过名称应用所有九个构造子的归纳——但它是该节依赖的规则，在这里展示了两个不同的公理集合生成了两个不等价的范畴。没有规则被认为是多余而省略的，也没有规则在此被声称可以从其他规则推出——那需要为每个规则构建一个反例模型，而没有构建任何模型。

 ** 因为范畴是稀薄的，所以该规则是自由的[Lind T] 的每个同态集族都是平凡成立的（[Proset] 的 [equiv] 是 [fun _ _ => True]），所以 [lind_thin] 由 [I] 成立。因此，四个结构的每个义务都由 [Program] 的默认策略完成，而在此文件中没有书写证明。数清楚 [Print Module]，它们共有十四个：[one_unique] 对于 [Lind_Terminal]；[fork_respects] 和 [ump_products] 对于 [Lind_Cartesian]；对于 [Lind_Closed]，转置及其逆的两个 [proper_morphism] 证书（它们是 [Sets] 的态射），[exp_iso] 的两个同构律，以及 [ump_exponents']；以及 [fmap_respects]、[fmap_id]、[fmap_comp] 分别对 [LindSound] 和 [LindWeaken] 三次。因此转置的唯一性是免费的，这里没有证明，因为没有需要证明的；这四个结构正好携带九条规则的数据，并且没有任何等式内容。

 ** 与 Instance/Props.v 的比较

 [Instance/Props.v] 是语义方面：它的对象是命题（Props），箭头是蕴涵，其头部已经记录了笛卡尔闭包在那里的演绎定理。桥梁是一个赋值：给定 [val : V -> Prop]，在其下 T 的每个公理都成立，[ent_soundness] 将推导转换为蕴涵，而 [LindSound] 将其打包为函子 [Lind T ⟶ Props]。它的度量强度，在下面编译的内容之外没有其他主张：- 它是一个函子（所有三个函子定律都是自由的，Props 是薄的）；
 - 它精确地保持终对象、二元积和指数对象，在对象的莱布尼茨相等下（[sound_terminal]、[sound_product]、[sound_exponent]，全部 [eq_refl]）；
 - 它是忠实的，但实际上是空洞的：源是薄的，所以 [f ≈ g] 那里有 [True]，并且从 [Lind T] 出发的每个函子都是忠实的——这个一般性陈述是 [lind_any_Faithful]，而且 [LindSound_Faithful] 就是字面上的它；
 - 它不是满的（[sound_not_Full]）也不是本质上满射的（[sound_not_EssentiallySurjective]），因此不是等价函子，在将每个原子映射为 True 的赋值下，空理论都能反驳这些结论。因此，[Props] 的 CCC 结构在比较中被精确重现，而两个反驳表明，这种比较既不完全也不本质上是满的。它们是关于单个函子 [LindSound T_empty val_true val_true_empty] 的陈述，这里没有任何常量说明 [Lind T_empty] 和 [Props] 是不等价的。满性将是关于单一赋值的演算的完备性，这是一个比练习要求严格得多的陈述，这里被反驳而非尝试实现。

 ** 工程发现[Lib.v] 为整个开发设置了 [Uniform Inductive Parameters]，所以在 [Inductive Sent (V : Type)] 的主体内部，名称 [Sent] 已经代表 [Sent V]；在那里显式编写参数会被拒绝，并显示“非法应用（非功能性构造）”，该错误命名了参数，但既没有标识符也没有说明原因：它报告 [Sent] 作为对 [V] 的非功能性项应用，但没有说明 [Sent] 已经吸收了该参数。同样的情况也适用于 [Entails] 内部。

 此文件范围内的 [PreOrder] 是 [CRelationClasses.PreOrder]，即 crelation 值的那个，因为 [Category.Lib] 导出了它；[Proset] 想要的是 Prop 值的 [RelationClasses.PreOrder]，在 [entails_PreOrder] 中以限定形式写出。限定名称不需要额外的 [Require]，因为该模块已经通过传递方式加载。[lind_thin] 在这里通过一个术语来证明，而不是依赖 [Instance/Proset/Order.v] 的 [proset_thin]，后者是捐赠者并通过转换适用于 [Lind T]。这是一个测量，而不是偏好：此文件的项目内传递闭包为 27 个模块，添加 [Instance/Proset/Order] 后增加到 35 个。
*)

(** ** (A) Syntax *)

(* Atoms, truth, conjunction, implication. Nothing else; see the scope note in the header. / 原子，真理，合取，蕴涵。没有别的；请参阅标题中的范围说明。 *)
Inductive Sent (V : Type) : Type :=
  | s_var : V -> Sent
  | s_top : Sent
  | s_and : Sent -> Sent -> Sent
  | s_imp : Sent -> Sent -> Sent.

Arguments s_var {V} _.
Arguments s_top {V}.
Arguments s_and {V} _ _.
Arguments s_imp {V} _ _.

(*
 A theory is a bare set of sentences: its axioms.  It is not required
 to be deductively closed, consistent, or inhabited. 

 --------
 一个理论是一组最基本的句子：它的公理。它不要求具有演绎封闭性、一致性或被实现性。
*)
Definition Theo (V : Type) : Type := Sent V -> Prop.

(* * ** (B) Entailment relative to a theory / * **（B）相对于一个理论的蕴涵 *)

(*
 Mac Lane's “q is a consequence of p on the basis of the axioms of T”.
 Prop-valued, so [Proset] accepts it and the category below is thin
 without any truncation. 

 --------
 麦克莱恩的“q是基于T的公理的p的一个结果”。
 值为命题型，所以[Proset]接受它，并且下面的范畴是稀薄的
 没有任何截断。
*)
Inductive Entails {V : Type} (T : Theo V) : Sent V -> Sent V -> Prop :=
  (* assumption / reflexivity / 假设 / 反身性 *)
  | ent_refl p : Entails p p
  (* cut / transitivity / 切 / 及物性 *)
  | ent_cut p q r : Entails p q -> Entails q r -> Entails p r
  (* the axiom rule: an axiom of T follows from anything / 公理规则：T 的公理可以从任何事物中推导出来 *)
  | ent_ax p a : T a -> Entails p a
  (* ⊤-introduction / ⊤-介绍 *)
  | ent_top p : Entails p s_top
  (* ∧-introduction / ∧-介绍 *)
  | ent_pair p q r : Entails p q -> Entails p r -> Entails p (s_and q r)
  (* the two ∧-eliminations / 两个 ∧-消解 *)
  | ent_fst p q : Entails (s_and p q) p
  | ent_snd p q : Entails (s_and p q) q
  (* →-introduction: the deduction theorem, here a CONSTRUCTOR / →-介绍：演绎定理，这里是一个构造器 *)
  | ent_curry p q r : Entails (s_and p q) r -> Entails p (s_imp q r)
  (* evaluation / modus ponens in sequent form / 序列形式下的评估 / 前件肯定式 *)
  | ent_eval q r : Entails (s_and (s_imp q r) q) r.

(*
 Reflexivity is [ent_refl] and transitivity is [ent_cut], so the
 preorder is the two structural rules and nothing more.  Given as a
 record literal rather than through [Program] so that [id] and
 [compose] of [Lind] reduce; see [lind_id] and [lind_compose]. 

 --------
 自反性是 [ent_refl]，传递性是 [ent_cut]，因此预序就是这两个结构规则而已。以记录字面值给出，而不是通过 [Program]，这样 [Lind] 的 [id] 和 [compose] 可以化简；参见 [lind_id] 和 [lind_compose]。
*)
Definition entails_PreOrder {V} (T : Theo V) :
  RelationClasses.PreOrder (Entails T) :=
  {| RelationClasses.PreOrder_Reflexive := ent_refl T
   ; RelationClasses.PreOrder_Transitive :=
       fun p q r H K => ent_cut T p q r H K |}.

(* * ** (C) The category of sentences ordered by entailment / * ** (C) 按蕴涵顺序排列的句子类别 *)

Definition Lind {V} (T : Theo V) : Category :=
  Proset (entails_PreOrder T).

Example lind_obj {V} (T : Theo V) : obj[Lind T] = Sent V := eq_refl.

Example lind_hom {V} (T : Theo V) (p q : Sent V) :
  (p ~{Lind T}~> q) = Entails T p q := eq_refl.

Example lind_id {V} (T : Theo V) (p : Sent V) :
  @id (Lind T) p = ent_refl T p := eq_refl.

Example lind_compose {V} (T : Theo V) (p q r : Sent V)
  (f : Entails T p q) (g : Entails T q r) :
  (g ∘[Lind T] f) = ent_cut T p q r f g := eq_refl.

(*
 Every hom-setoid is trivially true, so the category is thin.  This is
 [proset_thin] at [entails_PreOrder T] by conversion; see the closure
 measurement in the header for why it is restated in one term. 

 --------
 每个同态集合都是平凡成立的，所以该范畴是稀疏的。这在[proset_thin]到[entails_PreOrder T]通过转换是成立的；参见标题中的闭包测度，了解为什么它在一个项中被重述。
*)
Definition lind_thin {V} (T : Theo V) : Thin (Lind T) :=
  fun _ _ _ _ => I.

(*
 Thinness of the SOURCE makes faithfulness vacuous: the conclusion
 [f ≈ g] of [fmap_inj] is True whatever the functor does, so every
 functor out of [Lind T] is faithful and no property of the functor is
 consulted.  [LindSound_Faithful] in section (F) is this term, so the
 vacuity is visible in the definition rather than argued in prose. 

 --------
 来源的稀薄使忠实性变得空洞：结论 [f ≈ g] 的 [fmap_inj] 是 True，无论函子做什么，所以从 [Lind T] 出发的每个函子都是忠实的，并且不考虑函子的任何属性。第(F)节中的 [LindSound_Faithful] 就是这个项，因此空洞性在定义中就能看出，而不是在文字描述中论证。
*)
Definition lind_any_Faithful {V} (T : Theo V) {D : Category}
  (F : Lind T ⟶ D) : Faithful F :=
  @Build_Faithful (Lind T) D F (fun x y f g _ => I).

(* * ** (D) Terminal, cartesian and closed / * ** (D) 端点，笛卡尔和闭合 *)

(*
 Terminal object: truth.  [one] is ⊤-introduction; [one_unique] is
 free by thinness. 

 --------
 终端对象：真理。[one] 是 ⊤-引入；[one_unique] 是由于稀薄而自由的。
*)
#[export] Program Instance Lind_Terminal {V} (T : Theo V) :
  @Terminal (Lind T) := {
  terminal_obj := s_top;
  one := fun p => ent_top T p
}.

(* Product: conjunction, exactly as the exercise says. [fork] is ∧-introduction, the projections are the two ∧-eliminations; [fork_respects] and [ump_products] are free by thinness. / 产品：连接词，完全按照练习所说。[fork] 是 ∧-引入，投影是两个 ∧-消解；[fork_respects] 和 [ump_products] 是由稀薄性自由的。 *)
#[export] Program Instance Lind_Cartesian {V} (T : Theo V) :
  @Cartesian (Lind T) := {
  product_obj := s_and;
  fork := fun p q r f g => ent_pair T p q r f g;
  exl  := fun p q => ent_fst T p q;
  exr  := fun p q => ent_snd T p q
}.

(*
 The inverse transpose.  This is the one derived rule in the file: it
 pairs the given entailment with the second projection and cuts
 against evaluation, so it consumes ent_cut, ent_pair, ent_fst,
 ent_snd and ent_eval, and nothing else. 

 --------
 逆转置。这是文件中推导出的唯一规则：它将给定的蕴涵与第二投影配对，并对评估进行裁剪，因此它会消耗 ent_cut、ent_pair、ent_fst、ent_snd 和 ent_eval，而不消耗其他任何东西。
*)
Definition lind_uncurry {V} {T : Theo V} {p q r : Sent V}
  (f : Entails T p (s_imp q r)) : Entails T (s_and p q) r :=
  ent_cut T (s_and p q) (s_and (s_imp q r) q) r
    (ent_pair T (s_and p q) (s_imp q r) q
       (ent_cut T (s_and p q) p (s_imp q r) (ent_fst T p q) f)
       (ent_snd T p q))
    (ent_eval T q r).

(*
 Exponential: implication.  In this library [exponent_obj x y] is
 displayed [y ^ x], so [exponent_obj := s_imp] gives q ^ p = “p
 implies q”, which is Mac Lane's q^p.  [to exp_iso] is the deduction
 theorem [ent_curry]; [from exp_iso] is [lind_uncurry]; both
 isomorphism laws and [ump_exponents'] are free by thinness. 

 --------
 指数：蕴含。在这个库中 [exponent_obj x y] 显示为 [y ^ x]，因此 [exponent_obj := s_imp] 给出 q ^ p = “p 蕴含 q”，这是 Mac Lane 的 q^p。[to exp_iso] 是演绎定理 [ent_curry]；[from exp_iso] 是 [lind_uncurry]；同构定律和 [ump_exponents'] 都是由薄性自由的。
*)
#[export] Program Instance Lind_Closed {V} (T : Theo V) :
  @Closed (Lind T) _ := {
  exponent_obj := s_imp;
  exp_iso := fun p q r =>
    {| to   := {| morphism := fun f => ent_curry T p q r f |}
     ; from := {| morphism := fun f => lind_uncurry f |} |}
}.

(* The exercise's three identifications, pinned so that a later edit cannot drift away from them. / 这项练习的三个认定，被固定下来，以确保后续编辑不会偏离它们。 *)
Example lind_terminal_is_top {V} (T : Theo V) :
  @terminal_obj (Lind T) (Lind_Terminal T) = s_top := eq_refl.

Example lind_product_is_and {V} (T : Theo V) (p q : Sent V) :
  @product_obj (Lind T) (Lind_Cartesian T) p q = s_and p q := eq_refl.

Example lind_exponent_is_imp {V} (T : Theo V) (p q : Sent V) :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp p q := eq_refl.

(* Currying IS the deduction rule, on the nose. / 柯里化就是那个推导规则，正中要害。 *)
Example lind_curry_is_rule {V} (T : Theo V) (p q r : Sent V)
  (f : Entails T (s_and p q) r) :
  @curry (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q r f
    = ent_curry T p q r f := eq_refl.

(* ...and the counit is [lind_uncurry] at the identity derivation. / ...并且余单位在恒等导数处是 [lind_uncurry]。 *)
Example lind_eval_unfold {V} (T : Theo V) (q r : Sent V) :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) q r
    = lind_uncurry (ent_refl T (s_imp q r)) := eq_refl.

(* * ** (E) Soundness under a valuation / * **（E）在赋值下的正确性 *)

(* The interpretation of a sentence under a valuation of the atoms. Conjunction goes to /\ and implication to ->, which is what makes section (F)'s three preservation statements hold at eq_refl. / 在原子的赋值下对一个句子的解释。 合取表示为 /\，蕴含表示为 ->，这就是使得第 (F) 节的三个保持性陈述在 eq_refl 下成立的原因。 *)
Fixpoint sdenote {V} (val : V -> Prop) (p : Sent V) : Prop :=
  match p with
  | s_var v   => val v
  | s_top     => True
  | s_and a b => sdenote val a /\ sdenote val b
  | s_imp a b => sdenote val a -> sdenote val b
  end.

(*
 Soundness: if every axiom of T holds under val, then every derivation
 carries the interpretation of its premise to that of its conclusion.
 By induction on the derivation; the only case that consumes the
 hypothesis on T is [ent_ax]. 

 --------
 健全性：如果 T 的每个公理在 val 下成立，那么每个推导都会将其前提的解释传递给其结论的解释。通过对推导进行归纳；唯一使用 T 上假设的情况是 [ent_ax]。
*)
Theorem ent_soundness {V} (T : Theo V) (val : V -> Prop)
  (HT : forall a, T a -> sdenote val a) {p q : Sent V} :
  Entails T p q -> sdenote val p -> sdenote val q.
Proof.
  intros D; induction D; simpl in *; try tauto.
  - intros _; exact (HT a H).
Qed.

(* * ** (F) The comparison functor into Instance/Props.v / * **（F）到 Instance/Props.v 的比较函子 *)

(*
 The soundness map packaged as a functor.  All three functor laws are
 free: Props is thin, so every equation between its arrows is True. 

 --------
 健全性映射被打包为函子。所有三个函子律都是免费的：Props 很薄，因此它的箭头之间的每一个方程都为真。
*)
Program Definition LindSound {V} (T : Theo V) (val : V -> Prop)
  (HT : forall a, T a -> sdenote val a) : Lind T ⟶ Props := {|
  fobj := sdenote val;
  fmap := fun p q f => ent_soundness T val HT f
|}.

(*
 Preservation of the three pieces of cartesian closed structure, at
 Leibniz equality of objects rather than up to isomorphism. 

 --------
 在对象的莱布尼茨等价下，而不是仅仅到同构，保持三个笛卡尔闭结构的完整性。
*)
Example sound_terminal {V} (T : Theo V) val HT :
  fobj[LindSound T val HT] (@terminal_obj (Lind T) (Lind_Terminal T))
    = @terminal_obj Props Props_Terminal := eq_refl.

Example sound_product {V} (T : Theo V) val HT (p q : Sent V) :
  fobj[LindSound T val HT]
      (@product_obj (Lind T) (Lind_Cartesian T) p q)
    = @product_obj Props Props_Cartesian
        (fobj[LindSound T val HT] p) (fobj[LindSound T val HT] q)
  := eq_refl.

Example sound_exponent {V} (T : Theo V) val HT (p q : Sent V) :
  fobj[LindSound T val HT]
      (@exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q)
    = @exponent_obj Props Props_Cartesian Props_Closed
        (fobj[LindSound T val HT] p) (fobj[LindSound T val HT] q)
  := eq_refl.

(*
 Faithful, but VACUOUSLY so: this IS [lind_any_Faithful], so nothing
 about soundness is consulted and the vacuity is not a claim about the
 proof but the definition itself. 

 --------
 忠实，但非常空洞：这就是 [lind_any_Faithful]，所以没有考虑可靠性，空洞性不是对证明的评论，而是对定义本身的评论。
*)
#[export] Instance LindSound_Faithful {V} (T : Theo V) val HT :
  Faithful (LindSound T val HT) :=
  lind_any_Faithful T (LindSound T val HT).

(* * ** (G) Two axiom sets, two categories / * **（G）两个公理集，两个范畴 *)

(*
 Monotonicity of entailment in the theory: enlarging the axiom set
 only adds derivations.  By induction; every case but [ent_ax] is the
 corresponding constructor applied to the inductive hypotheses. 

 --------
 理论中蕴涵的单调性：扩大公理集只会增加推导。通过归纳法；除了 [ent_ax] 外，每一种情况都是将对应的构造器应用于归纳假设。
*)
Lemma entails_weaken {V} {T T' : Theo V} (HTT : forall a, T a -> T' a)
  {p q : Sent V} : Entails T p q -> Entails T' p q.
Proof.
  intros D; induction D;
    [ apply ent_refl
    | eapply ent_cut; eassumption
    | apply ent_ax; apply HTT; assumption
    | apply ent_top
    | apply ent_pair; assumption
    | apply ent_fst
    | apply ent_snd
    | apply ent_curry; assumption
    | apply ent_eval ].
Defined.

(* ...as an identity-on-objects functor between the two categories. / ……作为两个范畴之间在对象上同一的函子。 *)
Program Definition LindWeaken {V} {T T' : Theo V}
  (HTT : forall a, T a -> T' a) : Lind T ⟶ Lind T' := {|
  fobj := fun p => p;
  fmap := fun p q f => entails_weaken HTT f
|}.

(* Two atoms, and three theories over them: no axioms, the single implication between the atoms, and every sentence an axiom. / 两个原子，以及关于它们的三种理论：没有公理、原子之间的单一蕴含，以及每个句子都是公理。 *)
Definition sv (b : bool) : Sent bool := s_var b.

Definition T_empty : Theo bool := fun _ => False.
Definition T_mp : Theo bool := fun s => s = s_imp (sv true) (sv false).
Definition T_all : Theo bool := fun _ => True.

(* The separating valuation: the first atom true, the second not. / 分离估值：第一个原子为真，第二个不为真。 *)
Definition val_sep (b : bool) : Prop := b = true.

Lemma val_sep_empty : forall a, T_empty a -> sdenote val_sep a.
Proof. intros a []. Qed.

(* Non-derivability at the empty theory, by soundness at [val_sep]. This is the half that cannot be got by exhibiting a derivation. / 在空理论下不可推导，通过在 [val_sep] 处的有效性。这是一半无法通过展示推导来得到的部分。 *)
Theorem not_entails_empty :
  Entails T_empty (sv true) (sv false) -> False.
Proof.
  intros D.
  pose proof (@ent_soundness bool T_empty val_sep val_sep_empty _ _ D
                eq_refl) as Hf.
  discriminate Hf.
Qed.

(*
 Derivability at the theory whose one axiom is that implication.  The
 derivation is categorical: pair the identity with itself to get the
 diagonal, then uncurry the axiom and cut — that is, modus ponens read
 off the cartesian closed structure rather than assumed as a rule. 

 --------
 在其唯一公理为该蕴含的理论中的可推导性。推导是范畴论的：将恒等式与其自身配对以得到对角线，然后将公理逆旋并切断——也就是说，从笛卡尔闭结构中读出而不是作为规则假设的假言推理。
*)
Theorem entails_mp : Entails T_mp (sv true) (sv false).
Proof.
  apply (ent_cut _ _ (s_and (sv true) (sv true))).
  - apply ent_pair; apply ent_refl.
  - apply (@lind_uncurry bool T_mp).
    apply ent_ax; reflexivity.
Defined.

Definition empty_sub_mp : forall a, T_empty a -> T_mp a :=
  fun a H => match H return T_mp a with end.

(*
 The comparison functor between the two categories is identity on
 objects, and it is NOT full: [entails_mp] has no preimage. 

 --------
 这两个范畴之间的比较函子在对象上是恒等的，并且它不是满的：[entails_mp] 没有原像。
*)
Theorem weaken_not_Full : Full (LindWeaken empty_sub_mp) -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty (pre (sv true) (sv false) entails_mp)).
Qed.

(*
 [empty_sub_all] is declared for the reader rather than consumed: no
 constant below applies it, and this file names no functor
 [Lind T_empty ⟶ Lind T_all].  One exists — [LindWeaken empty_sub_all]
 typechecks at exactly that type — so the quantifier in the next
 theorem is not empty, but that is recorded here rather than pinned by
 a constant. 

 --------
 [empty_sub_all] 被声明供读者使用而非被消费：下面没有常量应用它，并且这个文件没有命名任何函子 [Lind T_empty ⟶ Lind T_all]。存在一个——[LindWeaken empty_sub_all] 在确切的类型上通过类型检查——所以下一个定理中的量词并非空，但这里记录了这一点，而不是由常量固定。
*)
Definition empty_sub_all : forall a, T_empty a -> T_all a :=
  fun a H => match H return T_all a with end.

(*
 Stronger, and independent of any choice of comparison: NO full
 functor at all goes from the empty theory's category to the category
 of the theory that asserts everything.  Only [ent_ax] is used on the
 target side, and only [not_entails_empty] on the source side. 

 --------
 更强，并且独立于任何比较选择：没有任何完全函子从空理论的范畴到断言一切的理论的范畴。目标端只使用 [ent_ax]，源端只使用 [not_entails_empty]。
*)
Theorem no_full_functor_empty_to_all (F : Lind T_empty ⟶ Lind T_all) :
  Full F -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty
           (pre (sv true) (sv false)
              (ent_ax T_all (fobj[F] (sv true)) (fobj[F] (sv false)) I))).
Qed.

(*
 ...hence the two categories are not equivalent, since the functor of
 an equivalence is full ([Equivalence_Full]).  This is the strongest
 form of “two different axiom sets give two different categories”
 delivered here. 

 --------
 ...因此这两个范畴不是等价的，因为等价函子是满的（[Equivalence_Full]）。这是这里所提供的“两个不同的公理集合给出两个不同的范畴”的最强形式。
*)
Theorem no_equivalence_empty_to_all (F : Lind T_empty ⟶ Lind T_all) :
  EquivalenceOfCategories F -> False.
Proof.
  intros E.
  exact (no_full_functor_empty_to_all F (Equivalence_Full E)).
Qed.

(* * ** (H) The comparison with Props is not an equivalence / * **（H）与 Props 的比较并不等同 *)

(* The valuation under which every atom, hence every sentence, holds. / 每个原子，因此每个句子，都成立的评估。 *)
Definition val_true (b : bool) : Prop := True.

Lemma val_true_empty : forall a, T_empty a -> sdenote val_true a.
Proof. intros a []. Qed.

Lemma sdenote_all {V} (val : V -> Prop)
  (Hv : forall v, val v) (p : Sent V) : sdenote val p.
Proof.
  induction p; simpl;
    [ apply Hv | exact I | split; assumption | intros _; assumption ].
Qed.

(* Not full: fullness at this valuation would be completeness, and it would hand back the underivable entailment of [not_entails_empty]. / 不完整：在这种评估下的完整性将是完全性，并且它将返回 [not_entails_empty] 的不可推导的必然结果。 *)
Theorem sound_not_Full :
  Full (LindSound T_empty val_true val_true_empty) -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty (pre (sv true) (sv false) (fun x => x))).
Qed.

(*
 Every object in the image of this comparison is inhabited, so none of
 them is isomorphic to False in Props. 

 --------
 在此比较的图像中的每个对象都是有居住的，因此它们都不与 Props 中的 False 同构。
*)
Theorem sound_misses_False (p : Sent bool) :
  @Isomorphism Props (sdenote val_true p) False -> False.
Proof.
  intros i.
  exact (to i (sdenote_all val_true (fun _ => I) p)).
Qed.

(* Not essentially surjective, by the previous result at False. / 不本质上是满射，根据前面的结果为 False。 *)
Theorem sound_not_EssentiallySurjective :
  EssentiallySurjective (LindSound T_empty val_true val_true_empty)
    -> False.
Proof.
  intros [pick iso].
  exact (sound_misses_False (pick False) (iso False)).
Qed.
