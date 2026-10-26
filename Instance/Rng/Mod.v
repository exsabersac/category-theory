(*
   * * Restriction of scalars, and the category of all modules

   Mac Lane's §II.2 pairs contravariance with a worked algebraic
   example.  Construction 8 is restriction of scalars: a homomorphism of
   rings ρ : R → S turns every S-module into an R-module, by letting r
   act as ρ r does, and the assignment is CONTRAVARIANT — ρ points from
   R to S while the induced functor points from S-modules to R-modules.
   Construction 9 collects the fibres into a single category of all
   modules over all rings, whose objects are pairs (R, M) and whose
   morphisms carry a ring map alongside a map of the underlying groups
   (Categories for the Working Mathematician, 2nd ed., §II.2, printed
   p. 35, [maclane:II.2:construction8] and [maclane:II.2:construction9];
   the locations follow issue jwiegley/category-theory#256's convention,
   and as there the printed text was not consulted while writing this
   file).
   nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
   nLab: https://ncatlab.org/nlab/show/Grothendieck+construction
   Wikipedia: https://en.wikipedia.org/wiki/Restriction_of_scalars

   WHAT IS BUILT ON.  Instance/Mod.v supplies [RModObject]/[RModHom] and
   the categories [RMod R]; Instance/Rng.v and Theory/Algebra/Rig.v
   supply [Rng], whose objects are [RingObject] and whose morphisms are
   [RigHom]s of the underlying rigs.  Nothing about modules is restated:
   [RestrictObj] keeps [rm_ab] LITERALLY the same term, so every module
   fact — the group laws, [rm_smul_zero_l], [ab_map_neg] — transfers
   unchanged, and each of the five module obligations is M's own law
   with ρ's preservation of the relevant operation spliced in front.
   Distributing over a sum of scalars spends [rig_map_add],
   associativity spends [rig_map_mul], unitality spends [rig_map_one],
   and distributing over a sum of vectors spends nothing at all.

   LEFT AND RIGHT.  Mac Lane's modules are right modules, so his
   construction 8 reads “for a right S-module”.  The tree's primitive is
   the LEFT module ([RModObject] of Instance/Mod.v), with right modules
   defined there as left modules over the opposite ring,
   [ModR R := RMod (Ring_op R)].  The right-hand reading therefore costs
   one observation and no second construction: a ring homomorphism is
   its own homomorphism of the opposite rings, since ρ (b · a) ≈ ρ b · ρ a
   IS ρ's multiplicativity read backwards ([RigHom_op]), and
   [RestrictR ρ := Restrict (RigHom_op ρ)].  The two are the same
   construction at different rings, by definition rather than by a
   separate proof.

   THE FIRST INDEXED CATEGORY INSTANTIATED AT A CONCRETE VARYING
   FAMILY.  Three [IndexedCat] values existed before [ModIndexed], and
   the claim must be measured against them precisely.  Two are GENERAL
   CONSTRUCTORS that do discharge all fifteen coherence fields for
   varying fibres — Construction/Grothendieck/RoundTrip.v's
   [RT_Indexed] (from a split cleaving, with real coherence proofs)
   and Construction/Grothendieck/Strict.v's
   [IndexedCat_of_StrictFunctor] (from a [StrictCat]-valued functor
   under fibrewise UIP) — but neither is APPLIED to a concrete family
   anywhere outside its own file.  The third, that same file's
   [Constant_IndexedCat], is the one concrete Grothendieck the tree
   instantiates, and it has every fibre the SAME category, every
   reindexing the identity functor and every mediator [iso_id].  So
   what is new here is the INSTANTIATION: [ModIndexed] is the first
   [IndexedCat] whose fifteen fields are discharged at a concrete
   family whose fibres genuinely vary with the base object.  The
   fields still come cheap, for one structural
   reason worth stating because it is what makes the exercise tractable:
   EVERY structural isomorphism of [ModIndexed] is an identity-carrier
   one.  Reindexing never touches the abelian group, only the action, so
   the comparison morphisms are all the identity map of a shared group
   and are built by the single smart constructor [rmod_iso_of_ab].  Two
   of the three even have DEFINITIONALLY equal actions — [idx_id]
   because the identity ring map is the identity function, [idx_comp]
   because [rig_hom_compose] is function composition — so their
   obligations close by [reflexivity]; only [idx_resp] does any work,
   and that work is one application of [rm_smul_respects].  The ten law
   fields are then pointwise identities and close by [reflexivity] as
   well.

   TWO TOTAL CATEGORIES, AND WHICH ONE IS MAC LANE'S.  Construction 9's
   category of all modules over all rings is [ModFibred], fibred over
   [Rng], and its morphisms are Mac Lane's on the nose: a morphism
   (R; M) ~> (S; N) is a pair (ρ; f) with ρ : R ~> S a homomorphism of
   rings — running WITH the total arrow — and f an R-module map
   [M ~> RestrictObj ρ N], that is, an additive f : M → N with
   f (r · m) ≈ ρ r · f m.  That condition is the standard notion of a
   SEMILINEAR map, and the word is reserved for it here
   ([ModFibred_semilinear] one way, [mod_semilinear_hom] back).
   Composition is Mac Lane's pasting: ring legs compose as ρ' ∘ ρ
   ([ModFibred_compose_ring]) and fibre legs as (Restrict ρ f') ∘ f
   ([ModFibred_compose_fibre]).

   [ModTotal] is the OPFIBRED companion, and it is what the tree's
   covariant [IndexedCat] together with [Grothendieck] yields DIRECTLY,
   which is why it is built first and keeps its name.  Its morphisms are
   pairs (ρ; g) with ρ : S ~> R — running OPPOSITE to the total arrow —
   and g an S-module map [RestrictObj ρ M ~> N], that is, an additive
   g : M → N with g (ρ s · m) ≈ s · g m.  That is the mirror condition,
   called COSEMILINEAR here so the standard word stays with Mac Lane's
   ([ModTotal_cosemilinear], [mod_cosemilinear_hom]).  The two
   categories are NOT opposite to one another: comparing the two hom
   types shows that passing to the opposite reverses the fibre leg as
   well as the base, so each has to be built rather than derived from
   the other by [Opposite].

   How [ModFibred] is reached costs no new mathematics.  [OpModIndexed]
   is the same assignment with the fibres read backwards —
   [idx_fib R := (RMod R)^op], reindexing by [Opposite_Functor] of the
   same [Restrict], every structural isomorphism
   Construction/Opposite.v's [Isomorphism_Opposite] of the same
   identity-carrier isomorphism — and
   [ModFibred := (Grothendieck OpModIndexed)^op].  Extension of scalars,
   the left adjoint of restriction, is a different matter and is NOT
   built: the tree has no tensor product for it.

   What is definitional and what is up to ≈, stated exactly, and it is
   the same on both sides.  The OBJECT and HOM TYPES are definitional:
   [ModTotal_obj_unfold], [ModTotal_hom_unfold], [ModFibred_obj_unfold]
   and [ModFibred_hom_unfold] are all [eq_refl], as are the ring legs of
   composites ([ModTotal_compose_ring], [ModFibred_compose_ring]) and
   the collapse [(Rng^op)^op = Rng] that lets [ModFibredProj] be typed
   at [Rng] with no transport.  (Those ring-leg [eq_refl] Examples DO
   compare Rng morphisms with [=] — a deliberate strengthening, sound
   exactly because the two sides are convertible; the ≈-only
   discipline governs statements about morphisms that are not, which
   is why the MODULE leg of a composite is stated up to ≈.)  On
   the fibred side the mediating comparison is genuinely present rather
   than absent — [RestrictObj ρ (RestrictObj ρ' P)] and
   [RestrictObj (ρ' ∘ ρ) P] have the same action but different law
   fields, so they are distinct records — and
   [ModFibred_compose_fibre] displays it, while
   [ModFibred_compose_carrier] shows it is invisible on carriers.  Here
   the ≈ carries real weight and is not standing in for [=]: the two
   morphism terms of [ModFibred_compose_fibre] are NOT convertible, a
   whole-term [reflexivity] being refused, and the equation closes
   pointwise instead.  The carrier-level statements
   ([ModTotal_compose_carrier], [ModFibred_compose_carrier]) do close by
   whole-term [reflexivity].  No claim is made anywhere that two
   morphisms with ≈-equal components are [eq];
   the hom-setoid of [Total] compares base arrows by ≈ and transports
   fibre arrows along that proof.

   FIBRATION STATUS.  The in-tree [IndexedCat] is COVARIANT and its
   Grothendieck construction produces an OPfibration whose canonical
   opcleaving satisfies the split laws — Construction/Grothendieck/
   Fibration.v, cited and not re-proved here, and cited at the strength
   it delivers: that file's own header records that the split laws are
   standalone lemmas ([Grothendieck_Split]) rather than an instance of
   Theory/Fibration.v's strict [SplitCleaving] record.  So [ModProj] is
   that opfibration over [Rng^op].  Nothing here re-derives the dual
   statement for [ModFibredProj]: that it is a fibration over [Rng]
   follows from the same citation read through the opposite, and is not
   formalized.

   THE FIBRES.  [ModTotal_fibre] instantiates
   Construction/Grothendieck/Fiber.v's [fiber_grothendieck_equiv] at
   [ModIndexed]: the fibre of [ModTotal] over a ring R is equivalent to
   [RMod R], by an equivalence that is the identity on objects, and the
   target is [RMod R] on the nose ([ModTotal_fibre_target], [eq_refl]).
   On the fibred side the same instantiation at [OpModIndexed] lands at
   [(RMod R)^op] ([ModFibred_fibre_op]), and [ModFibred_fibre] carries
   it across by Theory/Equivalence/Limit.v's
   [EquivalenceOfCategories_op] to land at [RMod R], the double opposite
   collapsing definitionally.  Disclosed: [ModFibred] is not itself
   presented as the total category of a displayed category over [Rng],
   so [Fiber] is applied to the underlying Grothendieck and transported,
   rather than computed for [ModFibred] directly.

   WITNESS.  ℤ is initial in [Rng] (Instance/Rng.v's [Rng_Initial_Z]),
   so restriction along the unique map ℤ → R makes every R-module a
   ℤ-module: [ZRestrict].  The same datum is an arrow in each category,
   pointing opposite ways: [mod_to_Z] runs out of every object of
   [ModTotal], and [mod_from_Z] runs into every object of [ModFibred],
   both with ring leg the unique map ℤ → R and identity fibre leg.  At ℤ
   itself the action computes, [3 · 4 = 12] by [eq_refl]. 

   --------
   * * 标量的限制，以及所有模的范畴Mac Lane 的 §II.2 将逆变性与一个具体的代数例子配对。构造 8 是标量限制：一个环同态 ρ : R → S 会将每个 S-模转换为 R-模，通过让 r 的作用方式等同于 ρ(r) 的作用，并且这个赋值是逆变的——ρ 从 R 指向 S，而所诱导的函子从 S-模指向 R-模。构造 9 将所有纤维收集到一个包含所有环上所有模的单一范畴中，其对象是 (R, M) 对，态射则同时伴随一个环映射和一个底层群的映射（《为工作数学家准备的范畴论》，第 2 版，§II.2，印刷版第 35 页，[maclane:II.2:construction8] 和 [maclane:II.2:construction9]；这些位置遵循 issue jwiegley/category-theory#256 的惯例，正如在编写此文件时没有参照印刷文本一样）。nLab:  https://ncatlab.org/nlab/show/restriction+of+scalars 
   nLab:  https://ncatlab.org/nlab/show/Grothendieck+construction 
   维基百科:  https://en.wikipedia.org/wiki/Restriction_of_scalars 

   建立在什么之上。Instance/Mod.v 提供  [RModObject] / [RModHom] 以及类别  [RMod R] ；Instance/Rng.v 和 Theory/Algebra/Rig.v 提供  [Rng] ，其对象是  [RingObject] ，其态射是基础环的  [RigHom] 。关于模的内容没有重新表述：[RestrictObj] 使 [rm_ab] 保持完全相同的项，因此每一个模的事实——群律，[rm_smul_zero_l]，[ab_map_neg]——都会保持不变地传递，并且五个模的义务中的每一个都是 M 自己的律，并且在前面嵌入了 ρ 对相关运算的保持。对标量和的分配使用了 [rig_map_add]，结合律使用了 [rig_map_mul]，单位性使用了 [rig_map_one]，对向量和的分配则完全不消耗任何内容。左与右。Mac Lane 的模是右模，因此他的构造 8 是“对于一个右 S-模”。该树的原始对象是左模（Instance/Mod.v 中的 [RModObject]），而右模在那里被定义为对偶环上的左模 [ModR R := RMod (Ring_op R)]。因此右侧的读法只需要一个观察而不需要第二个构造：环同态自身就是对偶环的同态，因为 ρ (b · a) ≈ ρ b · ρ a 是 ρ 的乘法性倒着读（[RigHom_op]），并且 [RestrictR ρ := Restrict (RigHom_op ρ)]。根据定义而非单独证明，这两者是在不同环上的相同构造。在具体可变族中实例化的第一个索引类别。在 [ModIndexed] 之前存在三个 [IndexedCat] 值，并且该主张必须精确地与它们进行比较。其中两个是通用构造器，它们确实释放了可变纤维的所有十五个相干性域——Construction/Grothendieck/RoundTrip.v 的 [RT_Indexed]（来自一个分裂切割，并有真实的相干性证明）和 Construction/Grothendieck/Strict.v 的 [IndexedCat_of_StrictFunctor]（来自一个 [StrictCat] 值函子在纤维逐点 UIP 下）——但是在自身文件之外没有任何应用于具体族。第三个，同一文件的 [Constant_IndexedCat]，是树实例化的具体格罗滕迪克，并且它的每个纤维都是相同的类别，每个重索引都是恒等函子，每个中介者都是 [iso_id]。那么，这里的新内容是实例化：[ModIndexed] 是第一个 [IndexedCat]，其十五个域在一个具体的族上被释放，该族的纤维会根据基对象真正地变化。域仍然很便宜，有一个值得说明的结构原因，因为它使得这个演练可处理：[ModIndexed] 的每个结构同构都是载有恒等的。重新索引从不接触阿贝尔群，只影响作用，因此比较态射都是共享群的恒等映射，并且是由单个智能构造器 [rmod_iso_of_ab] 构建的。三个中有两个实际上在定义上具有相等的动作——[idx_id] 因为恒等环映射是恒等函数，[idx_comp] 因为 [rig_hom_compose] 是函数组合——因此它们的义务通过 [reflexivity] 关闭；只有 [idx_resp] 实际执行了工作，而这项工作是对 [rm_smul_respects] 的一次应用。然后这十个法律字段是逐点恒等，并且也通过 [reflexivity] 关闭。总共有两个类别，以及哪一个是 Mac Lane 的。构造 9 的所有环上的所有模的类别是 [ModFibred]，纤维在 [Rng] 上，其态射正是 Mac Lane 的：一个态射 (R; M) → (S; N) 是一对 (ρ; f)，其中 ρ: R → S 是一个环同态——随总箭头移动——而 f 是一个 R-模映射 [M ~> RestrictObj ρ N]，即一个加法映射 f: M → N，满足 f(r · m) ≈ ρ r · f m。这个条件是半线性映射的标准概念，这里保留了该词（[ModFibred_semilinear] 一种方式，[mod_semilinear_hom] 回去）。复合是 Mac Lane 的拼接：环腿复合为 ρ' ∘ ρ ([ModFibred_compose_ring])，纤维腿复合为 (Restrict ρ f') ∘ f ([ModFibred_compose_fibre])。[ModTotal] 是 OPFIBRED 的伴随对象，它是树的协变 [IndexedCat] 与 [Grothendieck] 直接产生的结果，这也是它首先被构建并保持其名称的原因。它的态射是对 (ρ; g)，其中 ρ : S ~> R —— 与总箭头方向相反 —— 且 g 是 S-模映射 [RestrictObj ρ M ~> N]，也就是说，是一个加法映射 g : M → N，满足 g (ρ s · m) ≈ s · g m。这就是所谓的镜像条件，在此处称为 COSEMILINEAR，因此标准术语仍保留在 Mac Lane 的定义中 ([ModTotal_cosemilinear], [mod_cosemilinear_hom])。这两个范畴彼此并非对偶：比较两者的 Hom 型显示，通过取对偶会同时反转纤维支和基底，因此每个范畴必须独立构建，而不能通过 [Opposite] 从另一个派生。如何得到 [ModFibred] 并不需要新的数学。[OpModIndexed] 是相同的分配，只是纤维顺序倒过来——[idx_fib R := (RMod R)^op]，通过 [Opposite_Functor] 重新索引相同的 [Restrict]，每个结构同构 Construction/Opposite.v 的 [Isomorphism_Opposite] 对相同的恒等载体同构——以及 [ModFibred := (Grothendieck OpModIndexed)^op]。标量扩展，即限制的左伴随，是另一回事，并未构建：树上没有为它准备的张量积。什么是定义性的，什么是约等的，确切地说明，它在两边都是相同的。对象和同态类型是定义性的：[ModTotal_obj_unfold]、[ModTotal_hom_unfold]、[ModFibred_obj_unfold] 和 [ModFibred_hom_unfold] 都是 [eq_refl]，复合体的环腿（[ModTotal_compose_ring]、[ModFibred_compose_ring]）也是如此，以及使 [ModFibredProj] 可以在 [Rng] 下被类型化而无需传输的塌缩 [(Rng^op)^op = Rng]。（那些环-腿  [eq_refl]  示例确实比较了 Rng 同态与  [=]  —— 这是有意加强，恰恰因为两边是可转换的；≈-唯一的规则控制的是关于不可转换同态的陈述，这就是为什么复合的 MODULE 部分是按 ≈ 来陈述的。）在纤维化的一侧，中介比较是真实存在的而不是缺失的 ——  [RestrictObj ρ (RestrictObj ρ' P)]  和  [RestrictObj (ρ' ∘ ρ) P]  有相同的作用但法则域不同，因此它们是不同的记录 —— 而  [ModFibred_compose_fibre]  展示了这一点，  [ModFibred_compose_carrier]  显示在承载上它是不可见的。在这里，≈ 承载真实的分量，而不是代替  [=] ：[ModFibred_compose_fibre] 的两个同态项不可转换，整体项 [reflexivity] 被拒绝，方程点态闭合。载体级别的语句
   （[ModTotal_compose_carrier]，[ModFibred_compose_carrier]）确实通过
   整个术语 [reflexivity] 关闭。没有任何地方声称两个具有 ≈ 相等分量的态射是 [eq]；
   [Total] 的同态集合通过 ≈ 比较基箭，并沿该证明传递纤维箭头。纤维化状态。树内的 [IndexedCat] 是协变的，其 Grothendieck 构造产生了一个 OPfibration，其规范的 opcleaving 满足拆分定律——Construction/Grothendieck/Fibration.v 中引用且未重新证明，并且在其自身提供的强度下引用：该文件的标题记录表明拆分定律是独立引理（[Grothendieck_Split]），而不是 Theory/Fibration.v 的严格 [SplitCleaving] 记录的一个实例。因此 [ModProj] 是 [Rng^op] 上的该 opfibration。此处没有重新推导 [ModFibredProj] 的对偶陈述：它是 [Rng] 上的一个 fibration 可以从相同的引用通过对立阅读得出，并未形式化。纤维。[ModTotal_fibre] 实例化了 Construction/Grothendieck/Fiber.v 的 [fiber_grothendieck_equiv] 于 [ModIndexed]：[ModTotal] 在环 R 上的纤维等价于 [RMod R]，通过一个在对象上为恒等的等价，并且目标在 [RMod R] 上完全一致（[ModTotal_fibre_target], [eq_refl]）。在纤维那一边，同样在 [OpModIndexed] 的实例化落在 [(RMod R)^op]（[ModFibred_fibre_op]），并且 [ModFibred_fibre] 通过 Theory/Equivalence/Limit.v 的 [EquivalenceOfCategories_op] 将其传递到 [RMod R]，定义上双重对偶发生塌缩。公开：[ModFibred] 本身并没有被呈现为 [Rng] 上的显示范畴的整体范畴，因此 [Fiber] 作用于底层的格罗滕迪克并被传递，而不是直接为 [ModFibred] 计算。见证。ℤ 在 [Rng]（Instance/Rng.v 的 [Rng_Initial_Z]）中是初始的，因此沿着唯一映射 ℤ → R 的限制使每个 R-模成为 ℤ-模：[ZRestrict]。相同的数据在每个范畴中都是箭头，指向相反的方向：[mod_to_Z] 从每个 [ModTotal] 的对象出发，[mod_from_Z] 进入每个 [ModFibred] 的对象，两者的环腿都是唯一的映射 ℤ → R，并且纤维腿是恒等映射。在 ℤ 本身，作用的计算为 [3 · 4 = 12] 通过 [eq_refl]。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.
Require Import Category.Construction.Grothendieck.Fiber.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

(*
 Both [C^op] on categories and [F^op] on functors are notations for
 [_ ^op] at level 7, in [category_scope] and [functor_scope]
 respectively, and Functor/Opposite.v opens the latter; reopening
 [category_scope] here keeps [Rng^op] and [(RMod R)^op] reading as
 categories.  Opposite FUNCTORS are therefore written out as
 [Opposite_Functor], which is what Instance/Cat/Opposite.v does
 throughout for the same reason. 

 --------
 在范畴上，[C^op] 和在函子上，[F^op] 都是对七级的 [_ ^op] 的记号，分别位于 [category_scope] 和 [functor_scope] 中，而 Functor/Opposite.v 打开的是后者；在此重新打开 [category_scope] 可以保持 [Rng^op] 和 [(RMod R)^op] 被读取为范畴。因此，对立的函子被写作 [Opposite_Functor]，这正是 Instance/Cat/Opposite.v 出于同样原因在整个过程中所做的。
*)
Open Scope category_scope.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** Restriction of scalars: Mac Lane's construction 8 / * ** 标量的限制：Mac Lane 的构造8 *)

(*
   * Along ρ : R → S, an S-module M becomes an R-module with r acting as
   ρ r does.  The underlying abelian group is UNCHANGED — [rm_ab] is
   [rm_ab M], the same term — which is what makes every comparison
   further down an identity-carrier one. 

   --------
   * 沿着 ρ : R → S，一个 S-模 M 会变成一个 R-模，R 中的元素 r 的作用方式与 ρ r 的作用方式相同。基础的阿贝尔群保持不变 — [rm_ab] 仍然是 [rm_ab M]，相同的项 — 这正是使得下面的每一个比较都成为恒等承载的原因。
*)
Definition RestrictObj {R S : RingObject} (rho : R ~{Rng}~> S)
  (M : RModObject S) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab   := rm_ab M;
    rm_smul := fun r m => rm_smul M (rig_map rho r) m
  |}.
  - (* rm_smul_respects / rm_smul_respects *)
    intros r r' Hr m m' Hm.
    now rewrite Hr, Hm.
  - (* rm_smul_distr_l: no property of ρ is spent / rm_smul_distr_l：ρ 的属性没有被使用 *)
    intros r m n.
    apply rm_smul_distr_l.
  - (* rm_smul_distr_r: ρ is additive / rm_smul_distr_r: ρ 是可加的 *)
    intros r r' m.
    rewrite (rig_map_add rho r r').
    apply rm_smul_distr_r.
  - (* rm_smul_assoc: ρ is multiplicative / rm_smul_assoc: ρ 是乘法性的 *)
    intros r r' m.
    rewrite (rig_map_mul rho r r').
    apply rm_smul_assoc.
  - (* rm_smul_one: ρ preserves the unit / rm_smul_one: ρ 保持单位 *)
    intros m.
    rewrite (rig_map_one rho).
    apply rm_smul_one.
Defined.

(*
   * A map of S-modules IS a map of the restricted R-modules: the same
   homomorphism of abelian groups, its linearity read at the scalar
   ρ r. 

   --------
   * S-模的一个映射就是受限 R-模的一个映射：同一个阿贝尔群的同态，其线性在标量 ρ r 下理解。
*)
Program Definition RestrictHom {R S : RingObject} (rho : R ~{Rng}~> S)
  {M N : RModObject S} (f : M ~{RMod S}~> N) :
  RestrictObj rho M ~{RMod R}~> RestrictObj rho N := {|
  rm_hom := rm_hom f
|}.
Next Obligation.
  intros R S rho M N f r m.
  exact (rm_map_smul f (rig_map rho r) m).
Qed.

(*
   * Restriction of scalars as a functor.  Both functor laws hold because
   the arrow part changes nothing: identities and composites of module
   maps ARE identities and composites of the underlying group maps. 

   --------
   * 将标量限制作为函子。两个函子律都成立，因为箭头部分什么都不改变：模映射的恒等式和复合映射就是底层群映射的恒等式和复合映射。
*)
Program Definition Restrict {R S : RingObject} (rho : R ~{Rng}~> S) :
  RMod S ⟶ RMod R := {|
  fobj := RestrictObj rho;
  fmap := fun M N f => RestrictHom rho f
|}.
Next Obligation. intros R S rho M N f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R S rho M a; reflexivity. Qed.
Next Obligation. intros R S rho M N P f g a; reflexivity. Qed.

(** ** The right-module reading / ** 右模块阅读 *)

(*
   * A ring homomorphism is its own homomorphism of the OPPOSITE rings:
   ρ (b ·op a) = ρ (a · b) ≈ ρ a · ρ b = ρ b ·op ρ a, which is
   [rig_map_mul] with its two arguments exchanged.  Everything else is
   the original field, since Instance/Mod.v's [Rig_op] keeps the setoid,
   the zero, the addition and the unit as the very same terms.  The
   constructor is named explicitly for the reason Instance/Mod.v's
   [bimodule_right_RMod] records: a record literal here would elaborate
   the first field's type against [R] and infer the parameters to be
   [R] and [S] rather than their opposites, the two being convertible,
   and the multiplication clause would then be checked in the wrong
   argument order. 

   --------
   * 一个环同态是其自身的对偶环同态：
   ρ (b ·op a) = ρ (a · b) ≈ ρ a · ρ b = ρ b ·op ρ a，这就是
   [rig_map_mul]  交换了它的两个参数。其他的都是原来的域，因为 Instance/Mod.v 的 [Rig_op] 保持了同值关系、零元、加法和单位元素作为完全相同的项。
   构造函数之所以被显式命名，是因为 Instance/Mod.v 的 [bimodule_right_RMod] 记录了这一点：这里使用记录字面量会使第一个字段的类型根据 [R] 展开，并推导参数为 [R] 和 [S]，而不是它们的对偶，这两个是可转换的，乘法子句随后会在错误的参数顺序下被检查。
*)
Definition RigHom_op {R S : RingObject} (rho : R ~{Rng}~> S) :
  Ring_op R ~{Rng}~> Ring_op S :=
  @Build_RigHom (Rig_op (ring_rig R)) (Rig_op (ring_rig S))
    (rig_map rho) (rig_map_zero rho) (rig_map_add rho)
    (rig_map_one rho) (fun a b => rig_map_mul rho b a).

(*
   * Restriction of scalars for RIGHT modules — Mac Lane's own statement
   of construction 8.  It is [Restrict] at the opposite rings, by
   definition; no obligation is discharged a second time. 

   --------
   * 右模的标量限制——Mac Lane 自己对构造 8 的陈述。根据定义，它是在对合环上 [Restrict]；没有任何义务会被第二次履行。
*)
Definition RestrictR {R S : RingObject} (rho : R ~{Rng}~> S) :
  ModR S ⟶ ModR R := Restrict (RigHom_op rho).

(* * ** The comparison isomorphisms, all identity-carrier / * ** 比较同构，全部为恒等载体 *)

(*
   * The smart constructor.  A pair of mutually inverse homomorphisms of
   the UNDERLYING abelian groups, each commuting with the two actions,
   is an isomorphism of modules.  Stating the hypotheses through an
   explicit [AbHom] rather than through the carriers is what keeps the
   constructor usable at arbitrary M and N: at every call site below the
   two groups are the same term and both maps are the identity, so the
   inverse laws close by [reflexivity] and only the two action clauses
   carry content. 

   --------
   * 智能构造器。两个相互逆的群同态，它们是底层阿贝尔群的同态，并且分别与两个作用相交换，是模之间的同构。通过显式的 [AbHom] 来陈述假设，而不是通过承载对象，可以使构造器在任意 M 和 N 下可用：在下面的每一个调用点，这两个群都是相同的项，并且两个映射都是恒等映射，因此逆律通过 [reflexivity] 得以成立，只有两个作用的条款包含实际内容。
*)
Program Definition rmod_iso_of_ab {R : RingObject} {M N : RModObject R}
  (h : AbHom (rm_ab M) (rm_ab N)) (k : AbHom (rm_ab N) (rm_ab M))
  (Hh : ∀ r m, cmon_map h (rm_smul M r m) ≈ rm_smul N r (cmon_map h m))
  (Hk : ∀ r n, cmon_map k (rm_smul N r n) ≈ rm_smul M r (cmon_map k n))
  (Hhk : ∀ n, cmon_map h (cmon_map k n) ≈ n)
  (Hkh : ∀ m, cmon_map k (cmon_map h m) ≈ m) :
  M ≅[RMod R] N := {|
  to   := {| rm_hom := h; rm_map_smul := Hh |};
  from := {| rm_hom := k; rm_map_smul := Hk |}
|}.
Next Obligation.
  intros R M N h k Hh Hk Hhk Hkh n; exact (Hhk n).
Qed.
Next Obligation.
  intros R M N h k Hh Hk Hhk Hkh m; exact (Hkh m).
Qed.

(*
   * Reindexing, packaged with the op-direction fixed once: a morphism
   x ~> y of [Rng^op] IS a ring map y → x, and restriction along it
   carries x-modules to y-modules. 

   --------
   * 重新索引，在修复了操作方向后打包：一个态射  
   x ~> y 在 [Rng^op] 中是一个环映射 y → x，并且沿其限制会将 x-模转换为 y-模。
*)
Definition mod_map {x y : RingObject} (f : x ~{Rng^op}~> y) :
  RMod x ⟶ RMod y := Restrict f.

(*
   * ≈-equal ring maps reindex isomorphically.  The one comparison of the
   three that does any work, and the work is one application of
   [rm_smul_respects] to the pointwise equality of the two ring maps. 

   --------
   * ≈-相等的环映射以同构方式重新索引。三者中唯一有实际作用的比较，其工作是将 [rm_smul_respects] 应用于两个环映射的逐点相等性。
*)
Definition mod_resp_iso {x y : RingObject} {f g : x ~{Rng^op}~> y}
  (e : f ≈ g) (a : RMod x) : mod_map f a ≅[RMod y] mod_map g a.
Proof.
  (*
 The two modules are pinned explicitly: both comparison maps being
 the identity of ONE group, the elaborator would otherwise identify
 the source and target modules with each other. 

 --------
 这两个模块被明确固定：两个比较映射都是一个群的同一映射，否则展开器会将源模块和目标模块相互识别。
*)
  unshelve notypeclasses refine
    (@rmod_iso_of_ab y (mod_map f a) (mod_map g a)
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m.
    exact (rm_smul_respects a _ _ (e r) m m (reflexivity m)).
  - intros r n.
    exact (rm_smul_respects a _ _ (symmetry (e r)) n n (reflexivity n)).
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(*
   * Reindexing along the identity is the identity ON THE ACTION, not
   merely up to isomorphism: the identity ring map is the identity
   function, so the two actions are the same term and all four
   obligations close by [reflexivity]. 

   --------
   * 沿恒等重新索引是在作用上的恒等，而不仅仅是同构意义上的恒等：恒等环映射就是恒等函数，因此这两个作用是相同的项，并且所有四个义务都由 [reflexivity] 封闭。
*)
Definition mod_id_iso {x : RingObject} (a : RMod x) :
  mod_map (@id (Rng^op) x) a ≅[RMod x] a.
Proof.
  unshelve notypeclasses refine
    (@rmod_iso_of_ab x (mod_map (@id (Rng^op) x) a) a
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m; reflexivity.
  - intros r n; reflexivity.
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(*
   * Reindexing twice is reindexing along the composite, again on the
   action: composition in [Rng] is composition of the underlying
   functions, so ρ₂ (ρ₁ s) · m is literally the same term on both
   sides. 

   --------
   * 两次重新索引就是沿复合进行重新索引，再在操作上进行重新索引：[Rng] 中的复合就是底层函数的复合，所以 ρ₂ (ρ₁ s) · m 在两边字面上是相同的项。
*)
Definition mod_comp_iso {x y z : RingObject} (f : y ~{Rng^op}~> z)
  (g : x ~{Rng^op}~> y) (a : RMod x) :
  mod_map f (mod_map g a) ≅[RMod z] mod_map (f ∘ g) a.
Proof.
  unshelve notypeclasses refine
    (@rmod_iso_of_ab z (mod_map f (mod_map g a)) (mod_map (f ∘ g) a)
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m; reflexivity.
  - intros r n; reflexivity.
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(* * ** The indexed category of modules / * ** 模块的索引类别 *)

(*
   * Modules indexed by rings, contravariantly — that is, covariantly over
   [Rng^op], which is what Construction/Indexed.v's covariant
   [IndexedCat] asks for.  The ten law fields are pointwise identities:
   every comparison above is the identity map of a shared abelian group,
   and [fmap] of a restriction functor changes no underlying map, so
   each equation is an identity of carrier functions. 

   --------
   * 模块按环进行反变索引——也就是说，在 [Rng^op] 上是协变的，这正是 Construction/Indexed.v 的协变 [IndexedCat] 所要求的。十个律域是按点的恒等：上面的每个比较都是共享阿贝尔群的恒等映射，而限制函子 [fmap] 不改变任何基础映射，因此每个方程都是载体函数的恒等式。
*)
Definition ModIndexed : IndexedCat (Rng^op).
Proof.
  unshelve notypeclasses refine
    (@Build_IndexedCat (Rng^op)
       (fun R : RingObject => RMod R)
       (fun x y f => mod_map f)
       (fun x y f g e a => mod_resp_iso e a)
       _ _ _
       (fun x a => mod_id_iso a)
       _
       (fun x y z f g a => mod_comp_iso f g a)
       _ _ _ _ _ _).
  - (* idx_resp_natural / idx_resp_natural *)
    intros x y f g e a b k m; reflexivity.
  - (* idx_resp_id / idx_resp_id *)
    intros x y f e a m; reflexivity.
  - (* idx_resp_trans / idx_resp_trans *)
    intros x y f g h e1 e2 a m; reflexivity.
  - (* idx_id_natural / idx_id_自然 *)
    intros x a b k m; reflexivity.
  - (* idx_comp_natural / idx_comp_natural *)
    intros x y z f g a b k m; reflexivity.
  - (* idx_comp_resp_l / idx_comp_resp_l *)
    intros x y z f f' g e e' a m; reflexivity.
  - (* idx_comp_resp_r / idx_comp_resp_r *)
    intros x y z f g g' e e' a m; reflexivity.
  - (* idx_unit_left / idx_unit_left *)
    intros x y f a m; reflexivity.
  - (* idx_unit_right / idx_unit_右 *)
    intros x y f a m; reflexivity.
  - (* idx_cocycle / idx_余循环 *)
    intros w x y z f g h a m; reflexivity.
Defined.

(* * ** The category of all modules: Mac Lane's construction 9 / * ** 所有模的范畴：Mac Lane 的构造 9 *)

(*
   * Objects are pairs (R; M) with M an R-module; morphisms are described
   below.  The name is the issue's. 

   --------
   * 对象是成对 (R; M)，其中 M 是 R-模；态射在下文描述。名称归该期刊所有。
*)
Definition ModTotal : Category := Grothendieck ModIndexed.

(*
   * The projection to rings, contravariantly.  By
   Construction/Grothendieck/Fibration.v it is an opfibration whose
   canonical opcleaving satisfies the split laws — cited at that
   strength, not re-proved here. 

   --------
   * 向环的投射，反变的。根据 Construction/Grothendieck/Fibration.v，它是一个上纤维化，其典范的上分解满足分裂定律——以该强度引用，此处不再重新证明。
*)
Definition ModProj : ModTotal ⟶ Rng^op := Grothendieck_Proj ModIndexed.

(* * *** What the objects and morphisms are, on the nose / * *** 对象和态射的具体内容 *)

Example ModTotal_obj_unfold :
  obj[ModTotal] = (∃ R : RingObject, RModObject R) := eq_refl.

(*
   * A morphism (R; M) ~> (S; N) is a ring map ρ : S → R — running
   OPPOSITE to the total arrow, which is what [Rng^op] as the base
   means — together with an S-module map out of the restriction of M
   along ρ.  This is an equality of TYPES, by [eq_refl]. 

   --------
   * 一个态射 (R; M) ~> (S; N) 是一个环映射 ρ : S → R —— 与总箭头的方向相反，这正是基对象 [Rng^op] 的意义 —— 以及一个从沿 ρ 限制的 M 出发的 S-模映射。这是类型上的相等，由 [eq_refl] 给出。
*)
Example ModTotal_hom_unfold (R S : RingObject)
  (M : RModObject R) (N : RModObject S) :
  ((R; M) ~{ModTotal}~> (S; N))
    = (∃ rho : S ~{Rng}~> R, RestrictObj rho M ~{RMod S}~> N) := eq_refl.

(*
   * The fibre leg unfolded: g is additive and satisfies
   g (ρ s · m) ≈ s · g m.  That is the MIRROR of Mac Lane's condition,
   not Mac Lane's own, so the standard word “semilinear” is reserved for
   [ModFibred] below and this one is called COSEMILINEAR. 

   --------
   * 纤维图边展开：g 是加法的并满足
   g (ρ s · m) ≈ s · g m。也就是说，这是 Mac Lane 条件的镜像，
   而不是 Mac Lane 本身的条件，因此标准术语“半线性”保留用于
   下面的 [ModFibred]，而这个称为余半线性（COSEMILINEAR）。
*)
Lemma ModTotal_cosemilinear {R S : RingObject} {M : RModObject R}
  {N : RModObject S} (rho : S ~{Rng}~> R)
  (g : RestrictObj rho M ~{RMod S}~> N)
  (s : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom g) (rm_smul M (rig_map rho s) m)
    ≈ rm_smul N s (cmon_map (rm_hom g) m).
Proof. exact (rm_map_smul g s m). Qed.

(** And back: that equation is all a fibre leg is. / 往返：那个方程式就是一条纤维腿的全部。 *)
Program Definition mod_cosemilinear_hom {R S : RingObject}
  {M : RModObject R} {N : RModObject S} (rho : S ~{Rng}~> R)
  (h : AbHom (rm_ab M) (rm_ab N))
  (Hs : ∀ s m, cmon_map h (rm_smul M (rig_map rho s) m)
                 ≈ rm_smul N s (cmon_map h m)) :
  RestrictObj rho M ~{RMod S}~> N := {|
  rm_hom := h
|}.
Next Obligation.
  intros R S M N rho h Hs s m.
  exact (Hs s m).
Qed.

(* * *** Composition is Mac Lane's (ρ, f)·(ρ', f') / * *** 复合是 Mac Lane 的 (ρ, f)·(ρ', f') *)

(*
   * The ring components compose in [Rng] in the REVERSE order, on the
   nose. 

   --------
   * 戒指组件按 [Rng] 的顺序逆向组合，在鼻子上。
*)
Example ModTotal_compose_ring {X Y Z : ModTotal} (b : Y ~> Z) (a : X ~> Y) :
  `1 (b ∘ a) = `1 a ∘[Rng] `1 b := eq_refl.

(*
   * The module components compose directly.  Stated up to ≈ because it
   is an equation between morphisms; the proof is [reflexivity], the
   mediating [from (idx_comp …)] being the identity map of the shared
   group. 

   --------
   * 模块组件直接组合。 使用 ≈ 表示，因为它是在态射之间的方程；证明是 [reflexivity]，中介 [from (idx_comp …)] 是共享群的恒等映射。
*)
Lemma ModTotal_compose_carrier {X Y Z : ModTotal} (b : Y ~> Z) (a : X ~> Y)
  (m : carrier (cmon_setoid (rm_ab (`2 X)))) :
  cmon_map (rm_hom (`2 (b ∘ a))) m
    ≈ cmon_map (rm_hom (`2 b)) (cmon_map (rm_hom (`2 a)) m).
Proof. reflexivity. Qed.

(** The projection really does take first components. / 投影确实会取首要分量。 *)
Example ModProj_fobj (X : ModTotal) : ModProj X = `1 X := eq_refl.

Example ModProj_fmap {X Y : ModTotal} (a : X ~> Y) :
  fmap[ModProj] a = `1 a := eq_refl.

(** *** The fibres / *** 纤维 *)

Example ModTotal_fibre_target (R : RingObject) :
  idx_fib ModIndexed R = RMod R := eq_refl.

(*
   * The fibre of [ModTotal] over R is equivalent to [RMod R], by
   Construction/Grothendieck/Fiber.v's equivalence — which is the
   identity on objects, both of its cells carrying identity
   components. 

   --------
   * [ModTotal] 在 R 上的纤维等价于 [RMod R]，根据 Construction/Grothendieck/Fiber.v 的等价——它在对象上是恒等的，其两个单元都携带恒等分量。
*)
Definition ModTotal_fibre (R : RingObject) :
  EquivalenceOfCategories (Fiber_Grothendieck_To ModIndexed R) :=
  fiber_grothendieck_equiv ModIndexed R.

(* * ** The fibred reading: Mac Lane's (ρ, f) on the nose / * **纤维化阅读：Mac Lane 的 (ρ, f) 一针见血 *)

(*
   * The same assignment of modules to rings, with the fibres read
   BACKWARDS.  Restriction of scalars is not touched: every reindexing
   functor here is [Opposite_Functor] of the very one [ModIndexed]
   uses, and every structural isomorphism is Construction/Opposite.v's
   [Isomorphism_Opposite] of the very identity-carrier isomorphism
   [ModIndexed] uses.  Reversing the fibres is exactly what turns the
   opfibred morphisms of [ModTotal] into the fibred ones Mac Lane
   writes; the ten law fields close by [reflexivity] for the same reason
   they do there, composition in the opposite fibre being the same
   identity map of the same abelian group read the other way. 

   --------
   * 将模块分配到环上的相同分配，但纤维读取顺序是反的。标量限制未被触及：这里的每个重索引函子都是 [Opposite_Functor] 使用的 [ModIndexed]，而每个结构同构都是 Construction/Opposite.v 的 [Isomorphism_Opposite] 使用的同一身份载体同构。反转纤维正是将 [ModTotal] 的对纤维态射变为 Mac Lane 所写的纤维态射的方式；十个律域之所以关闭，是出于与那里相同的原因，反纤维中的复合就是相同阿贝尔群的相同恒等映射，只是读取方式相反。
*)
Definition OpModIndexed : IndexedCat (Rng^op).
Proof.
  unshelve notypeclasses refine
    (@Build_IndexedCat (Rng^op)
       (fun R : RingObject => (RMod R)^op)
       (fun x y f => Opposite_Functor (mod_map f))
       (fun x y f g e a => Isomorphism_Opposite (mod_resp_iso e a))
       _ _ _
       (fun x a => Isomorphism_Opposite (mod_id_iso a))
       _
       (fun x y z f g a => Isomorphism_Opposite (mod_comp_iso f g a))
       _ _ _ _ _ _).
  - (* idx_resp_natural / idx_resp_natural *)
    intros x y f g e a b k m; reflexivity.
  - (* idx_resp_id / idx_resp_id *)
    intros x y f e a m; reflexivity.
  - (* idx_resp_trans / idx_resp_trans *)
    intros x y f g h e1 e2 a m; reflexivity.
  - (* idx_id_natural / idx_id_自然 *)
    intros x a b k m; reflexivity.
  - (* idx_comp_natural / idx_comp_natural *)
    intros x y z f g a b k m; reflexivity.
  - (* idx_comp_resp_l / idx_comp_resp_l *)
    intros x y z f f' g e e' a m; reflexivity.
  - (* idx_comp_resp_r / idx_comp_resp_r *)
    intros x y z f g g' e e' a m; reflexivity.
  - (* idx_unit_left / idx_unit_left *)
    intros x y f a m; reflexivity.
  - (* idx_unit_right / idx_unit_右 *)
    intros x y f a m; reflexivity.
  - (* idx_cocycle / idx_余循环 *)
    intros w x y z f g h a m; reflexivity.
Defined.

(*
   * Mac Lane's category of all modules over all rings, fibred over
   [Rng]. 

   --------
   * Mac Lane 的所有环上所有模的范畴，纺织在 [Rng] 上。
*)
Definition ModFibred : Category := (Grothendieck OpModIndexed)^op.

(*
   * The projection to rings, COVARIANTLY.  No transport is needed to
   type it at [Rng] rather than at [(Rng^op)^op]: the double opposite
   collapses definitionally in this tree, by the auto-duality
   Construction/Opposite.v is built for. 

   --------
   * 投影到环，同变。无需将其从 [(Rng^op)^op] 传输到 [Rng] 来类型化：在此树中双对偶在定义上会塌缩，这是 Construction/Opposite.v 自动对偶构造所为。
*)
Definition ModFibredProj : ModFibred ⟶ Rng :=
  Opposite_Functor (Grothendieck_Proj OpModIndexed).

Example ModFibred_double_op_collapses : (Rng^op)^op = Rng := eq_refl.

(* * *** Mac Lane's (ρ, f), definitionally / * *** Mac Lane 的 (ρ, f)，按定义 *)

Example ModFibred_obj_unfold :
  obj[ModFibred] = (∃ R : RingObject, RModObject R) := eq_refl.

(*
   * A morphism (R; M) ~> (S; N) is a ring map ρ : R → S running WITH the
   total arrow, together with an R-module map from M into the
   restriction of N along ρ.  This is Mac Lane's (ρ, f) exactly, and it
   is an equality of TYPES, by [eq_refl]. 

   --------
   * 一个态射 (R; M) ~> (S; N) 是一个环映射 ρ : R → S，与总箭头一起运行，同时还有一个 R-模映射从 M 到沿 ρ 的 N 的限制。这正是 Mac Lane 的 (ρ, f)，并且这是类型的相等，由 [eq_refl]。
*)
Example ModFibred_hom_unfold (R S : RingObject)
  (M : RModObject R) (N : RModObject S) :
  ((R; M) ~{ModFibred}~> (S; N))
    = (∃ rho : R ~{Rng}~> S, M ~{RMod R}~> RestrictObj rho N) := eq_refl.

(*
   * The fibre leg unfolded: f is additive and SEMILINEAR in the standard
   sense, f (r · m) ≈ ρ r · f m.  This is Mac Lane's condition, which is
   why the word sits here rather than on [ModTotal_cosemilinear]. 

   --------
   * 纤维支腿展开：f 是可加的，并在标准意义上是半线性的，f (r · m) ≈ ρ r · f m。这是 Mac Lane 的条件，这就是为什么这个词出现在这里而不是在 [ModTotal_cosemilinear] 上。
*)
Lemma ModFibred_semilinear {R S : RingObject} {M : RModObject R}
  {N : RModObject S} (rho : R ~{Rng}~> S)
  (f : M ~{RMod R}~> RestrictObj rho N)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom f) (rm_smul M r m)
    ≈ rm_smul N (rig_map rho r) (cmon_map (rm_hom f) m).
Proof. exact (rm_map_smul f r m). Qed.

(** And back: that equation is all a fibre leg is. / 往返：那个方程式就是一条纤维腿的全部。 *)
Program Definition mod_semilinear_hom {R S : RingObject}
  {M : RModObject R} {N : RModObject S} (rho : R ~{Rng}~> S)
  (h : AbHom (rm_ab M) (rm_ab N))
  (Hs : ∀ r m, cmon_map h (rm_smul M r m)
                 ≈ rm_smul N (rig_map rho r) (cmon_map h m)) :
  M ~{RMod R}~> RestrictObj rho N := {|
  rm_hom := h
|}.
Next Obligation.
  intros R S M N rho h Hs r m.
  exact (Hs r m).
Qed.

(* * *** Composition is Mac Lane's pasting / * *** 组合是 Mac Lane 的拼接 *)

(*
   * The ring legs compose in [Rng] in Mac Lane's order, ρ' ∘ ρ, on the
   nose. 

   --------
   * 在 Mac Lane 的顺序中，ρ' ∘ ρ，戒指的腿在 [Rng] 上组合，正好在尖端。
*)
Example ModFibred_compose_ring {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y) :
  `1 (b ∘ a) = `1 b ∘[Rng] `1 a := eq_refl.

(*
   * The fibre legs paste as Mac Lane's (Restrict ρ f') ∘ f, with the one
   canonical comparison made visible: the composite lands in
   [RestrictObj ρ (RestrictObj ρ' P)] and the target is
   [RestrictObj (ρ' ∘ ρ) P], and those are DISTINCT records — their
   actions are the same term but their law fields are not — so the
   identity-carrier [mod_comp_iso] is what mediates.  The ≈ is doing
   real work: the two sides are NOT convertible as terms — a whole-term
   [reflexivity] is refused — so the equation is closed pointwise, which
   is what ≈ asks for in this hom-setoid. 

   --------
   * 纤维腿粘贴为 Mac Lane 的 (Restrict ρ f') ∘ f，并带有一个可见的典型比较：复合体落在 [RestrictObj ρ (RestrictObj ρ' P)]，目标是 [RestrictObj (ρ' ∘ ρ) P]，这些是不同的记录——它们的操作是相同的项，但它们的法律字段不同——因此身份载体 [mod_comp_iso] 起到调节作用。≈ 正在发挥实际作用：两边在项上不可转换——整个项 [reflexivity] 被拒绝——因此方程在每一点上封闭，这正是 ≈ 在这个同态集合中所要求的。
*)
Lemma ModFibred_compose_fibre {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y) :
  `2 (b ∘ a)
    ≈ to (mod_comp_iso (`1 a) (`1 b) (`2 Z))
        ∘ fmap[mod_map (`1 a)] (`2 b) ∘ `2 a.
Proof. intro m; reflexivity. Qed.

(*
   * On carriers the comparison is invisible and the fibre legs simply
   compose. 

   --------
   * 在承载体上，比较是不可见的，纤维支腿只是简单地组合。
*)
Lemma ModFibred_compose_carrier {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y)
  (m : carrier (cmon_setoid (rm_ab (`2 X)))) :
  cmon_map (rm_hom (`2 (b ∘ a))) m
    ≈ cmon_map (rm_hom (`2 b)) (cmon_map (rm_hom (`2 a)) m).
Proof. reflexivity. Qed.

Example ModFibredProj_fobj (X : ModFibred) :
  ModFibredProj X = `1 X := eq_refl.

Example ModFibredProj_fmap {X Y : ModFibred} (a : X ~> Y) :
  fmap[ModFibredProj] a = `1 a := eq_refl.

(** *** The fibres / *** 纤维 *)

(*
   * What is straightforwardly available, and exactly how far it goes.
   [ModFibred] is NOT itself presented as the total category of a
   displayed category over [Rng] — it is the opposite of one over
   [Rng^op] — so Construction/Grothendieck/Fiber.v's [Fiber] is applied
   to the underlying Grothendieck, where it lands at [(RMod R)^op], and
   the result is carried across by Theory/Equivalence/Limit.v's
   [EquivalenceOfCategories_op].  The double opposite collapses
   definitionally, so the transported equivalence lands at [RMod R] with
   no further work and no new general machinery. 

   --------
   * 直接可用的内容，以及它的确切范围。  
   [ModFibred] 本身并不是作为 [Rng] 上显示范畴的总范畴呈现的——它是 [Rng^op] 上某个范畴的对偶——因此 Construction/Grothendieck/Fiber.v 的 [Fiber] 被应用到基础的 Grothendieck 上，结果落在 [(RMod R)^op]，并且这个结果通过 Theory/Equivalence/Limit.v 的 [EquivalenceOfCategories_op] 被传递过去。双重对偶在定义上会塌缩，因此传递的等价性最终落在 [RMod R] 上，无需额外的工作，也不需要新的通用机制。
*)
Example ModFibred_fibre_target (R : RingObject) :
  (idx_fib OpModIndexed R)^op = RMod R := eq_refl.

Definition ModFibred_fibre_op (R : RingObject) :
  EquivalenceOfCategories (Fiber_Grothendieck_To OpModIndexed R) :=
  fiber_grothendieck_equiv OpModIndexed R.

Definition ModFibred_fibre (R : RingObject) :
  EquivalenceOfCategories
    (Opposite_Functor (Fiber_Grothendieck_To OpModIndexed R)) :=
  EquivalenceOfCategories_op (fiber_grothendieck_equiv OpModIndexed R).

(* * ** Every module is a ℤ-module: the witness / * ** 每个模都是一个 ℤ-模：证明 *)

(*
   * ℤ is initial in [Rng], so there is exactly one ring map ℤ → R, and
   restriction along it is the underlying-abelian-group functor read as
   a change of base. 

   --------
   * ℤ 在 [Rng] 中是初始的，所以恰好存在一个环映射 ℤ → R，并且沿它的限制就是将其作为底层阿贝尔群的函子来读取，作为基变换。
*)
Example rng_from_Z_is_initial_arrow (R : RingObject) :
  rng_from_Z R = @zero Rng Rng_Initial_Z R := eq_refl.

Definition ZRestrict (R : RingObject) : RMod R ⟶ RMod Int_Ring :=
  Restrict (rng_from_Z R).

(*
   * The arrow of [ModTotal] this produces, out of EVERY object: its ring
   leg is the unique map ℤ → R and its module leg is the identity,
   because the restriction is the target on the nose. 

   --------
   * [ModTotal] 的箭头对每个对象都会产生：它的环状腿是唯一的映射 ℤ → R，它的模腿是恒等映射，因为限制正好是目标。
*)
Definition mod_to_Z (R : RingObject) (M : RModObject R) :
  (R; M) ~{ModTotal}~> (Int_Ring; ZRestrict R M) :=
  (rng_from_Z R; @id (RMod Int_Ring) (ZRestrict R M)).

Example mod_to_Z_ring_leg (R : RingObject) (M : RModObject R) :
  fmap[ModProj] (mod_to_Z R M) = rng_from_Z R := eq_refl.

(*
   * The same datum read in [ModFibred], where the ring leg runs forward
   and the arrow therefore points the other way: Mac Lane's (ρ, f) with
   ρ the unique map ℤ → R and f the identity, exhibiting each module as
   its own underlying abelian group with the R-action added along ρ. 

   --------
   * 在 [ModFibred] 中读取的相同数据，其中环支向前延伸，因此箭头指向相反方向：Mac Lane 的 (ρ, f)，其中 ρ 是唯一的映射 ℤ → R，f 为恒等映射，展示每个模作为其自身的基础阿贝尔群，并沿 ρ 添加 R-作用。
*)
Definition mod_from_Z (R : RingObject) (M : RModObject R) :
  (Int_Ring; ZRestrict R M) ~{ModFibred}~> (R; M) :=
  (rng_from_Z R; @id (RMod Int_Ring) (ZRestrict R M)).

Example mod_from_Z_ring_leg (R : RingObject) (M : RModObject R) :
  fmap[ModFibredProj] (mod_from_Z R M) = rng_from_Z R := eq_refl.

(*
   * At ℤ itself the action computes: restriction along ℤ → ℤ leaves
   multiplication of integers where it was. 

   --------
   * 在 ℤ 本身，该作用计算为：沿着 ℤ → ℤ 的限制保留整数的乘法。
*)
Example int_ZRestrict_smul :
  rm_smul (ZRestrict Int_Ring Int_RMod) 3%Z 4%Z = 12%Z := eq_refl.

Example int_ZRestrict_group :
  rm_ab (ZRestrict Int_Ring Int_RMod) = rm_ab Int_RMod := eq_refl.

(*
   * The right-module reading unfolds on the nose: restricting a right
   S-module along ρ makes r act as ρ r acted.  This is the statement
   that carries the content; the ℤ computation below does not, ℤ being
   commutative, and is recorded only as evidence that the opposite-ring
   plumbing computes.  The argument exchange itself is what
   [RigHom_op]'s multiplication clause asserts, and the elaborator
   checks it against [Rig_op]'s definition. 

   --------
   * 右模的读法直观明了：沿着 ρ 限制一个右 S-模会使 r 的作用变为 ρ r 的作用。这是承载内容的陈述；下面的 ℤ 计算则不承载内容，因为 ℤ 是交换的，仅记录下来作为对偶环操作计算的证据。论证的交换本身正是 [RigHom_op] 的乘法条款所断言的，详细说明器会将其与 [Rig_op] 的定义进行核对。
*)
Example RestrictR_action {R S : RingObject} (rho : R ~{Rng}~> S)
  (M : RModObject (Ring_op S))
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  rm_smul (RestrictR rho M) r m = rm_smul M (rig_map rho r) m := eq_refl.

Example int_RestrictR_smul :
  rm_smul (RestrictR (rng_from_Z Int_Ring) (Ring_RMod (Ring_op Int_Ring)))
          3%Z 4%Z = 12%Z := eq_refl.
