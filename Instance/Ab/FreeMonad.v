Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.

Generalizable All Variables.

(* * * The free abelian group monad ℤ[−] on Set, and Ab ≅ Set^{ℤ[−]} / * * 在 Set 上的自由阿贝尔群单子 ℤ [−]，以及 Ab ≅ Set^{ℤ [−] } *)

(*
 Book: Riehl, “Category Theory in Context”, §5.3, the construction
 opening the section, printed pp. 195-196 (PDF pp. 215-216) —
 riehl:5.3:construction-ab-monadic, the box issue #472 appends
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §VI.4, Exercise 2, printed p. 146 (PDF p. 155) — the case R = ℤ
 of maclane:VI.4:ex2, whose general ring is
 Instance/Mod/FreeMonad.v
 nLab: https://ncatlab.org/nlab/show/free+abelian+group
 nLab: https://ncatlab.org/nlab/show/monadic+functor

 WHAT THE BOOK SAYS, read from the PDF.  “The free ⊣ forgetful
 adjunction … between sets and abelian groups … induces a monad Z[−] on
 Set.  Given a set S, Z[S] is the set of finite formal Z-linear
 combinations of elements of S, and the map Z[f] … carries a formal sum
 n1 s1 + ⋯ + nk sk … to the formal sum n1 f(s1) + ⋯ + nk f(sk) …  there
 is a unique functor from the category of abelian groups to the
 category of Z[−]-algebras that commutes with the left and right
 adjoints.  The image of an abelian group A is the algebra consisting of
 the underlying set of A together with the ”evaluation“ map
 ϵ_A : Z[A] → A that interprets a finite formal sum as a single element
 of A.  In fact, this functor defines an isomorphism of categories: to
 equip a set A with an ”evaluation“ function ev : Z[A] → A, so that
 diagrams … commute is precisely to give A the structure of an abelian
 group”, the triangle “a 'sanity check' … that it sends a singleton sum
 a ∈ Z[A] to the element a”, and an algebra homomorphism “a function
 f : A → B that preserves the evaluation of formal sums, i.e., a group
 homomorphism”.

 ROUTE (i), TAKEN.  Instance/Ab/Free.v's free abelian group, in the
 hom-set form [free_ab_adjunction_hom] #472 adds there (its counit
 computes; Ab/Free.v's CORRECTION (#472)).  [FreeAbF] is U ◯ F and
 [FreeAbMonad] is ℤ[−], Monad/Comparison.v's [Adjunction_Induced_Monad]
 of it: ℤ[X] is the free group's setoid of formal sums ([ZM_obj],
 [ZM_carrier]), η the insertion ([ZM_ret], [ZM_ret_fun]), μ = U ε F the
 flattening ([ZM_join_counit], [ZM_join_gen], [ZM_join_fun],
 [ZM_join_zero]), all at [eq_refl]; ℤ[f] relabels at ≈
 ([ZM_map_equiv]), refused at [eq_refl] (Test/ProbeFreeModule472.v,
 R26).  [Ab_K] is the comparison Ab → Set^{ℤ[−]}, [EM_Comparison] of
 the adjunction: K A = ⟨A, ε_A⟩, ε_A the evaluation of a formal sum
 ([Ab_K_alg_fun]), a ↦ a, 0 ↦ 0, ⟨a⟩ + ⟨b⟩ ↦ a + b and −⟨a⟩ ↦ −a at
 [eq_refl] ([Ab_K_alg_*]), K f = f ([Ab_K_map]); it commutes with the
 right adjoints and with the left ones, each up to a natural
 isomorphism whose components are identities (Monad/Comparison.v's two
 triangles at this adjunction, [Ab_K_Forget] and [Ab_K_Free]): that
 file's [EM_Comparison_Forget] and [EM_Comparison_Free] build them so
 (its header; [iso_id], and [EM_Comparison_Free_iso]'s identity
 arrows), and all four end [Qed], so that the components are identities
 is read from that file's source and no readback pins it here
 (Instance/Mod/FreeMonad.v's twins are [RMod_K_Forget] and
 [RMod_K_Free]).  CORRECTION (#482): [EM_Comparison_Forget] and
 [EM_Comparison_Free] end [Defined] since #482, and
 Monad/Comparison/Resolution.v reads their components back at
 [eq_refl] ([EM_Comparison_Forget_components],
 [EM_Comparison_Free_components]); [Ab_K_Forget] and [Ab_K_Free] still
 end [Qed], and no readback here pins them.
 [EM_to_AbS] sends (A, ev) to [zm_alg_ab]: 0 = ev⟨⟩, a + b =
 ev(⟨a⟩ + ⟨b⟩), −a = ev(−⟨a⟩); the triangle is [zm_alg_unit], every
 group law one instance of [zm_alg_eval_respects], and ev IS the sum in
 that group at ≈ ([zm_alg_fold]); an algebra map is additive
 ([zm_alg_hom_step]).  [Ab_EM_iso : Ab ≅[Cat] Set^{ℤ[−]}] has legs K
 and [EM_to_AbS] and identity components, to and from, at [eq_refl];
 [Ab_EM_equivalence] and [Ab_Forget_Monadic : Monadic Ab_Forget].  The
 argument is Instance/Mod/FreeMonad.v's part (c) without the action,
 and [PropEquiv] again costs no hypothesis ([zm_alg_prop]); issue #1357
 tracks a shared Eilenberg–Moore lemma for term-model monads, keeping
 identity components, that would remove this parallel and its siblings
 in #470 and #471.

 RIEHL'S “ISOMORPHISM OF CATEGORIES”.  By Instance/Cat.v an
 isomorphism in Cat is an equivalence of categories, which the identity
 components bring toward hers; the strict identity of Ab and its
 algebras is refused (R27 to R29).  Issue #484 keeps the strict reading
 ([StrictlyMonadic], isomorphism of categories on the nose).  Her Z[S]
 as integer combinations: the carrier here is Ab/Free.v's formal sums
 of generators and their negatives, and that each is a finite
 ℤ-combination is not proved for it (Ab/Free.v's WHAT IS NOT
 DELIVERED); T_R at [Int_Ring] has that reading, but its comparison
 with ℤ[−] is not made.

 ROUTE (ii), MEASURED AND NOT TAKEN.  ℤ[−] as T_R at [Int_Ring] with
 Ab ≅ RMod Int_Ring: no such equivalence is in the tree, only
 Instance/Mod/Cogenerator.v's one-way [Ab_to_ZMod] (#454).  #472's
 scout built it (every ℤ-module's action agrees with the iterated sum,
 ~25 lines) and composed it with [RMod_EM_iso Int_Ring]: the Require of
 Cogenerator.v takes the closure from 70 modules to 191, the composite's
 [iso_from_to] component is refused as the identity ([iso_compose]'s
 obligations), and no [Monadic Ab_Forget] follows, there being no
 monadicity-transport lemma in tree.  Two of the scout's findings
 complete that account.  The 121 modules are Cogenerator.v's own
 closure, not [Ab_to_ZMod]'s: relocated (about 40 lines) to a light
 file, it costs 7, measured on #472's tree by [Print Libraries] after a
 [Require] of Instance/Mod/FreeMonad.v (71 [Category] modules) with
 Instance/Ab/Monoidal.v, whose [zsmul] family it uses (78), and 11 with
 Adjunction/Unitalization.v too, where its [zsmul_mul] lives (82),
 against Cogenerator.v's 192.  And a composite built by hand rather than
 by [iso_compose] would keep identity components (not prototyped).
 Route (i) stays the one taken on fidelity, not cost: Riehl's statement
 is the comparison functor of the free-forgetful adjunction Set ⇄ Ab
 itself, which route (ii) does not give, and the tree has no lemma that
 would transport [Monadic] along Ab ≅ RMod Int_Ring.  Issue #1356 (Ab ≅
 RMod ℤ, and ℤ[−] ≅ T_ℤ as monads; linked to #1150) tracks that
 comparison.

 STRENGTHS.  Every [Example] holds at [eq_refl], restated in the probe.  At ≈
 only: [ZM_map_equiv], [zm_alg_step], [zm_alg_fold], [zm_alg_hom_step] (the
 twins of Instance/Mod/FreeMonad.v's first four) and the
 inverse laws of the isomorphism in Cat; [zm_fold_is_alg_eval] is Leibniz, by
 induction.  Eight proofs end [Defined] (counted by token) and seven are
 load-bearing, measured as in Instance/Mod/FreeMonad.v: [zm_alg_prop]
 ([EM_to_AbS_prop]), [zm_alg_hom_ab] ([EM_to_AbS]), [EM_to_AbS]
 ([Ab_EM_counit_iso]), [Ab_EM_counit_iso] and [Ab_EM_unit_iso]
 ([Ab_EM_equivalence]), [Ab_EM_equivalence] ([Ab_EM_counit_component]) and
 [Ab_EM_iso] ([Ab_EM_iso_to]); [Ab_Forget_Monadic] is [Defined] by the data
 convention only.  Eleven lemmas end [Qed].

 UNIVERSES, read off [About].  The section binds Sets@{c so} and every
 name binds c so first, with c < so.  A closed binder is refused, so
 each is extensible: forty-four names, ℤ[−] and the names built on it
 other than those below ([Ab_K_Forget] among them), bind six more,
 the group category's object level g (Set < g, c < g, Instance/Ab.v's
 [Ab]), Theory/Functor.v's [Compose] level and [FreeAb]'s four internal
 levels; ten bind g and the four: K, its eight readbacks ([Ab_K_carrier]
 to [Ab_K_alg_neg]) and [Ab_K_Free]; [fa_relabel]
 and [fa_flatten] bind g alone; five readbacks comparing across a
 composite bind a second copy (nine or twelve in all), and [ZM_carrier]
 one more for its equation's sort.  The isomorphism in Cat binds k
 (c < k, so < k) and there g is so (Set < so).  No [Set] but these
 bounds, and no equation; no explicit universe instance of a new
 constant is written.  On Coq 8.19.2 and 8.20.1 every name binds the
 same levels (compared by [About]).

 NOT DELIVERED.  The uniqueness of the comparison functor (Riehl's
 “unique functor”, Proposition 5.2.13; ADDENDUM (#482): in general,
 for comparisons coherent with the identification of the two monads,
 it is Monad/Comparison/Resolution.v's [EM_Comparison_unique], not
 instantiated here); the strict isomorphism (#484); a
 computing ℤ[f]; the comparison of ℤ[−] with T_R at [Int_Ring], and
 Ab ≃ RMod Int_Ring, which issue #1356 tracks (filed from #472's review,
 linked to #1150, whose ℤ comparison for tensor products waits on the
 same ℤ-module structure of [AbObject]). 

 --------
 书籍：Riehl，《情境中的范畴论》，§5.3，本节开头的构造，印刷页195-196（PDF页215-216）—— riehl:5.3:construction-ab-monadic，box问题#472附加
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，§VI.4，习题2，印刷页146（PDF页155）—— R = ℤ的情况 maclane:VI.4:ex2，其一般环为
 Instance/Mod/FreeMonad.v
 nLab: https://ncatlab.org/nlab/show/free+abelian+group
 nLab: https://ncatlab.org/nlab/show/monadic+functor根据书中所说，从 PDF 中阅读。“自由的遗忘伴随……在集合与阿贝尔群之间……导出一个在 Set 上的 monad ZZWW2WZZ。给定一个集合 S，[S] 是 S 元素的有限形式 Z 线性组合的集合，而映射 ZZWW4WZZ……将一个形式和 n1 s1 + ⋯ + nk sk ……映射到形式和 n1 f(s1) + ⋯ + nk f(sk) ……有一个唯一的从阿贝尔群范畴到 ZZWW5WZZ-代数范畴的函子，它与左伴随和右伴随交换。一个阿贝尔群 A 的像是由 A 的底集合以及“求值”映射 ϵ_A : ZZWW6WZZ → A 组成的代数，该映射将有限形式和解释为 A 的单个元素。”实际上，这个函子定义了范畴的同构：给一个集合 A 配备一个“评价”函数 ev : Z [A] → A，使得图…交换，正是赋予 A 交换群的结构；三角形“一个‘理智检查’… 它将单例和 a ∈ Z [A] 映射到元素 a”；以及代数同态“一个函数 f : A → B 保持形式和的评价，即一个群同态”。路线 (i)，已采取。实例/Ab/Free.v 的自由阿贝尔群，在同态集形式 [free_ab_adjunction_hom] #472 添加在那里（其余单位计算完成；Ab/Free.v 的修正 (#472)）。[FreeAbF] 是 U ◯ F，[FreeAbMonad] 是 ℤ [−]，Monad/Comparison.v 的 [Adjunction_Induced_Monad]：ℤ [X] 是自由群的正规和集合（[ZM_obj], [ZM_carrier]），η 为插入（[ZM_ret], [ZM_ret_fun]），μ = U ε F 为展平（[ZM_join_counit], [ZM_join_gen], [ZM_join_fun], [ZM_join_zero]），全部在 [eq_refl]；ℤ [f] 在 ≈（[ZM_map_equiv]）处重新标记，[eq_refl] 处被拒绝（Test/ProbeFreeModule472.v, R26）。[Ab_K] 是比较 Ab → Set^{ℤ [−] }，[EM_Comparison] 的伴随对：K A = ⟨A, ε_A⟩，ε_A 是形式和的评价 ([Ab_K_alg_fun])，a ↦ a，0 ↦ 0，⟨a⟩ + ⟨b⟩ ↦ a + b 和 −⟨a⟩ ↦ −a 在 [eq_refl] ([Ab_K_alg_*])，K f = f ([Ab_K_map])；它与右伴随以及左伴随对换，每一个都至自然同构，其分量是恒等映射（Monad/Comparison.v 中该伴随的两个三角形，[Ab_K_Forget] 和 [Ab_K_Free]）：该文件的 [EM_Comparison_Forget] 和 [EM_Comparison_Free] 构造它们这样（其头部；[iso_id]，以及 [EM_Comparison_Free_iso] 的恒等箭头），且所有四个结束 [Qed]，因此分量是恒等映射，从该文件源代码可读出，且无回读将其固定在这里（Instance/Mod/FreeMonad.v 的一对是 [RMod_K_Forget] 和 [RMod_K_Free]）。更正 (#482)：[EM_Comparison_Forget] 和 [EM_Comparison_Free] 自 #482 起终止于 [Defined]，并且 Monad/Comparison/Resolution.v 在 [eq_refl]（[EM_Comparison_Forget_components], [EM_Comparison_Free_components]）处读取它们的组件；[Ab_K_Forget] 和 [Ab_K_Free] 仍然终止于 [Qed]，这里没有读取回去固定它们。[EM_to_AbS] 将 (A, ev) 发送到 [zm_alg_ab]：0 = ev⟨⟩, a + b = ev(⟨a⟩ + ⟨b⟩), −a = ev(−⟨a⟩)；三角形是 [zm_alg_unit]，每个群法则是 [zm_alg_eval_respects] 的一个实例，ev 是该群在 ≈ ([zm_alg_fold]) 的和；一个代数映射是加法的 ([zm_alg_hom_step])。[Ab_EM_iso : Ab ≅[Cat] Set^{ℤ [−]}] 有腿 K 和 [EM_to_AbS] 以及在 [eq_refl] 处的身份组件；[Ab_EM_equivalence] 和 [Ab_Forget_Monadic : Monadic Ab_Forget]。该论点是 Instance/Mod/FreeMonad.v 的部分 (c) 没有动作，并且 [PropEquiv] 再次不需要假设 ([zm_alg_prop])；问题 #1357 跟踪了一个用于项模型 monads 的共享 Eilenberg–Moore 引理，保持身份组件，这将消除 #470 和 #471 中的这个平行及其类似情况。RIEHL的《范畴的同构》。通过Instance/Cat.v，在Cat中的同构是范畴的等价，其恒等分量将其带向她；Ab及其代数的严格恒等被拒绝（R27到R29）。问题#484保持严格的解读（[StrictlyMonadic]，范畴的同构按字面理解）。她的[S]作为整数组合：这里的载体是Ab/Free.v的生成元及其负元的形式和，并且没有证明每个都是有限的ℤ组合（Ab/Free.v没有交付的内容）；T_R在[Int_Ring]具有该解读，但与ℤ [−]的比较尚未进行。路线（ii），已测量但未采纳。ℤ [−] 作为 T_R 在 [Int_Ring] 处与 Ab ≅ RMod Int_Ring：在树中没有这样的等价关系，只有 Instance/Mod/Cogenerator.v 的单向 [Ab_to_ZMod]（#454）。#472 的侦察器构建了它（每个 ℤ 模的作用与迭代和一致，约25行）并将其与 [RMod_EM_iso Int_Ring] 组合：Cogenerator.v 的 Require 将闭包从 70 个模块扩展到 191 个，复合的 [iso_from_to] 组件被拒绝为恒等（[iso_compose] 的义务），且没有 [Monadic Ab_Forget] 后续，因为树中没有单子性传输引理。侦察器的两个发现完成了该说明。121 个模块是 Cogenerator.v 自己的闭包，而不是 [Ab_to_ZMod] 的：重定位（大约 40 行）到一个轻量文件上，花费为 7，由 [Print Libraries] 在 #472 的树上测量，经过 Instance/Mod/FreeMonad.v（71 个 [Category] 模块）与 Instance/Ab/Monoidal.v，使用了其 [zsmul] 家族（78 个），同时还包含 11 个 Adjunction/Unitalization.v，其中它的 [zsmul_mul] 位于其中（82），而 Cogenerator.v 则为 192。一个手工构建的复合结构而不是由 [iso_compose] 构建的复合结构将保留同一性组件（未原型化）。路线 (i) 仍然是按保真度选择的，而不是按成本：Riehl 的陈述是自由-遗忘伴随 Set ⇄ Ab 的比较函子本身，而路线 (ii) 不提供这一点，并且该树中没有引理可以沿 Ab ≅ RMod Int_Ring 传输 [Monadic]。问题 #1356（Ab ≅ RMod ℤ，且 ℤ [−] ≅ T_ℤ 作为单子；与 #1150 相关）跟踪该比较。

 优势。每个 [Example] 在 [eq_refl] 时都成立，在探针中重新表达。在 ≈ 下仅：[ZM_map_equiv]、[zm_alg_step]、[zm_alg_fold]、[zm_alg_hom_step]（Instance/Mod/FreeMonad.v 的前四个的孪生）以及 Cat 中同构的逆律；[zm_fold_is_alg_eval] 是莱布尼茨的，通过归纳法。八个证明结束于 [Defined]（按符号计数），七个是承重的，按照 Instance/Mod/FreeMonad.v 的方式衡量：[zm_alg_prop]（[EM_to_AbS_prop]）、[zm_alg_hom_ab]（[EM_to_AbS]）、[EM_to_AbS]（[Ab_EM_counit_iso]）、[Ab_EM_counit_iso] 和 [Ab_EM_unit_iso]（[Ab_EM_equivalence]）、[Ab_EM_equivalence]（[Ab_EM_counit_component]）以及 [Ab_EM_iso]（[Ab_EM_iso_to]）；[Ab_Forget_Monadic] 仅依靠数据惯例为 [Defined]。十一条引理结束于 [Qed]。宇宙，读取 [About]。该部分绑定 Sets@{c so}，每个名称首先绑定 c so，且 c < so。封闭绑定器被拒绝，因此每个都是可扩展的：四十四个名称，ℤ [−] 以及在其上构建的名称（除了以下内容（其中包括 [Ab_K_Forget]）），绑定另外六个，群类别的对象层 g（Set < g, c < g, Instance/Ab.v 的 [Ab]）、Theory/Functor.v 的 [Compose] 层和 [FreeAb] 的四个内部层；十个绑定 g 和四个：K，其八个读取回（[Ab_K_carrier] 到 [Ab_K_alg_neg]）以及 [Ab_K_Free]；[fa_relabel] 和 [fa_flatten] 单独绑定 g；五个读取回在合成中比较，绑定第二份（总共九或十二个），以及 [ZM_carrier] 为其方程的排序绑定一个额外。Cat 中的同构绑定 k（c < k, so < k），在那里 g 是 so（Set < so）。没有 [Set]，但有这些界限，并且没有方程；没有新常数的显式宇宙实例被写出。在 Coq 8.19.2 和 8.20.1 中，每个名字绑定相同的层级（通过 [About] 比较）。

 未交付。比较函子的唯一性（Riehl 的“唯一函子”，命题 5.2.13；附录（#482）：一般而言，对于与两个单子识别一致的比较，它是 Monad/Comparison/Resolution.v 的 [EM_Comparison_unique]，而非在此实例化）；严格同构（#484）；计算 ℤ [f]；ℤ [−] 与 T_R 在 [Int_Ring] 的比较，以及 Ab ≃ RMod Int_Ring，这些问题由 #1356 跟踪（从 #472 的审查提出，链接到 #1150，其张量积的 ℤ 比较等待 [AbObject] 的相同 ℤ-模结构）。
*)

Section FreeAbMonad.

Universes c so.

(* ℤ[−] = U ◯ F, with F Instance/Ab/Free.v's [FreeAb]. / ℤ [−] = U ◯ F，其中 F 的 Instance/Ab/Free.v 的 [FreeAb]。 *)
Definition FreeAbF@{+} : Sets@{c so} ⟶ Sets@{c so} := Ab_Forget ◯ FreeAb.

(*
 ℤ[−], the monad of the hom-set form of the free-forgetful
 adjunction. 

 --------
 ℤ [−]，自由-遗忘伴随的同态集形式的单子。
*)
Definition FreeAbMonad@{+} : @Monad Sets@{c so} FreeAbF :=
  Adjunction_Induced_Monad free_ab_adjunction_hom.

(* The relabelling of a formal sum along u: the fold of insert ∘ u. / 沿 u 的形式和的重新标记：插入 ∘ u 的折叠。 *)
Definition fa_relabel@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : FATerm X) : FATerm Y :=
  fa_eval (A := FreeAbObject Y) (free_ab_insert Y ∘ u) t.

(* A formal sum of formal sums, flattened: the fold of the identity. / 正式和的正式和，展开：同一性的折叠。 *)
Definition fa_flatten@{+} {X : Sets@{c so}}
  (k : FATerm (Ab_Forget (FreeAbObject X))) : FATerm X :=
  fa_eval (A := FreeAbObject X)
    (@id Sets@{c so} (Ab_Forget (FreeAbObject X))) k.

(* ℤ[X] is the free group's setoid, whose carrier is the formal sums. / ℤ [X] 是自由群的集合化结构，其承载体是形式和。 *)
Example ZM_obj@{+} (X : Sets@{c so}) :
  fobj[FreeAbF] X = Ab_Forget (FreeAbObject X) := eq_refl.

Example ZM_carrier@{+} (X : Sets@{c so}) :
  carrier (fobj[FreeAbF] X) = FATerm X := eq_refl.

(* η_X is the insertion of generators, as a setoid map, and x ↦ ⟨x⟩. / η_X 是生成元的插入，作为一个集同态映射，并且 x ↦ ⟨x⟩。 *)
Example ZM_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeAbMonad X = free_ab_insert X := eq_refl.

Example ZM_ret_fun@{+} (X : Sets@{c so}) (x : carrier X) :
  @ret _ _ FreeAbMonad X x = fa_gen x := eq_refl.

(* μ = U ε F, which flattens. / μ = U ε F，它会变平。 *)
Example ZM_join_counit@{+} (X : Sets@{c so}) :
  @join _ _ FreeAbMonad X
    = fmap[Ab_Forget] (@counit _ _ _ _ free_ab_adjunction_hom (FreeAb X))
  := eq_refl.

Example ZM_join_gen@{+} (X : Sets@{c so}) (t : FATerm X) :
  @join _ _ FreeAbMonad X (@fa_gen (Ab_Forget (FreeAbObject X)) t) = t
  := eq_refl.

Example ZM_join_fun@{+} (X : Sets@{c so})
  (k : FATerm (Ab_Forget (FreeAbObject X))) :
  @join _ _ FreeAbMonad X k = fa_flatten k := eq_refl.

Example ZM_join_zero@{+} (X : Sets@{c so}) :
  @join _ _ FreeAbMonad X fa_zero = fa_zero := eq_refl.

(*
 ℤ[u] relabels, up to ≈: Riehl's n1 s1 + ⋯ + nk sk ↦ n1 f(s1) + ⋯ +
 nk f(sk). 

 --------
 ℤ [u] 重标记，至 ≈: Riehl 的 n1 s1 + ⋯ + nk sk ↦ n1 f(s1) + ⋯ + nk f(sk).
*)
Lemma ZM_map_equiv@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : FATerm X) : fmap[FreeAbF] u t ≈ fa_relabel u t.
Proof.
  apply (free_ab_extend_unique (FreeAbObject Y) (free_ab_insert Y ∘ u)
           (fmap[FreeAb] u)).
  intro x. exact (free_ab_fmap_generators u x).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The comparison functor Ab → Set^{ℤ[−]} / * ** 比较函子 Ab → Set^{ℤ [−] } *)

Definition ZMAlg@{+} : Category@{so c c} :=
  @EilenbergMoore@{so so so c} Sets@{c so} FreeAbF FreeAbMonad.

Definition Ab_K@{+} : Ab ⟶ ZMAlg := EM_Comparison free_ab_adjunction_hom.

(*
 Riehl's “commutes with the left and right adjoints”: Monad/
 Comparison.v's two triangles, at this adjunction. 

 --------
 Riehl 的“与左伴随和右伴随交换”：Monad/Comparison.v 中的两个三角形，在这个挨生关系下。
*)
Theorem Ab_K_Forget@{+} :
  @EM_Forget Sets@{c so} FreeAbF FreeAbMonad ◯ Ab_K ≈ Ab_Forget.
Proof. exact (EM_Comparison_Forget free_ab_adjunction_hom). Qed.

Theorem Ab_K_Free@{+} :
  Ab_K ◯ FreeAb ≈ @EM_Free Sets@{c so} FreeAbF FreeAbMonad.
Proof. exact (EM_Comparison_Free free_ab_adjunction_hom). Qed.

Section Algebra.

Context {A : Sets@{c so}}.
Context (α : @TAlgebra Sets@{c so} FreeAbF FreeAbMonad A).

(* The group operations of an algebra (A, ev): 0 = ev⟨⟩, a + b = ev(⟨a⟩ + ⟨b⟩) and −a = ev(−⟨a⟩). / 代数 (A, ev) 的群运算：0 = ev⟨⟩，a + b = ev(⟨a⟩ + ⟨b⟩) 和 −a = ev(−⟨a⟩)。 *)
Definition zm_alg_zero@{+} : carrier A := t_alg[α] (@fa_zero A).

Definition zm_alg_plus@{+} (x y : carrier A) : carrier A :=
  t_alg[α] (@fa_plus A (fa_gen x) (fa_gen y)).

Definition zm_alg_neg@{+} (x : carrier A) : carrier A :=
  t_alg[α] (@fa_neg A (fa_gen x)).

(* The sum the formal sum names, through the operations just defined. / 通过刚定义的操作，对形式和名称求和。 *)
Fixpoint zm_alg_eval@{+} (t : FATerm A) : carrier A :=
  match t with
  | fa_gen x    => x
  | fa_zero     => zm_alg_zero
  | fa_plus s u => zm_alg_plus (zm_alg_eval s) (zm_alg_eval u)
  | fa_neg s    => zm_alg_neg (zm_alg_eval s)
  end.

(* Riehl's “sanity check”: ev sends a singleton sum a to a. / Riehl 的“理智检查”：ev 将单例和 a 发送到 a。 *)
Lemma zm_alg_unit@{+} (x : carrier A) : t_alg[α] (@fa_gen A x) ≈ x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* ev ∘ μ ≈ ev ∘ ℤ[ev], read through the relabelling. / ev ∘ μ ≈ ev ∘ ℤ [ev]，通读重新标记。 *)
Lemma zm_alg_step@{+} (K : FATerm (fobj[FreeAbF] A)) :
  t_alg[α] (@join _ _ FreeAbMonad A K) ≈ t_alg[α] (fa_relabel t_alg[α] K).
Proof.
  symmetry.
  refine (transitivity _ (@t_action _ _ _ _ α K)).
  apply (proper_morphism t_alg[α]).
  symmetry. exact (ZM_map_equiv t_alg[α] K).
Qed.

Lemma zm_alg_plus_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) zm_alg_plus.
Proof.
  intros x x' Hx y y' Hy.
  exact (proper_morphism t_alg[α] _ _ (fae_plus (fae_gen Hx) (fae_gen Hy))).
Qed.

Lemma zm_alg_neg_respects@{+} : Proper (equiv ==> equiv) zm_alg_neg.
Proof.
  intros x x' Hx.
  exact (proper_morphism t_alg[α] _ _ (fae_neg (fae_gen Hx))).
Qed.

(* The evaluation IS the sum in the derived group. / 评估是派生群中的总和。 *)
Lemma zm_alg_fold@{+} (t : FATerm A) : t_alg[α] t ≈ zm_alg_eval t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs ]; simpl.
  - exact (zm_alg_unit x).
  - reflexivity.
  - refine (transitivity
              (zm_alg_step
                 (@fa_plus (fobj[FreeAbF] A)
                    (@fa_gen (fobj[FreeAbF] A) s)
                    (@fa_gen (fobj[FreeAbF] A) u))) _).
    exact (zm_alg_plus_respects _ _ IHs _ _ IHu).
  - refine (transitivity
              (zm_alg_step
                 (@fa_neg (fobj[FreeAbF] A) (@fa_gen (fobj[FreeAbF] A) s))) _).
    exact (zm_alg_neg_respects _ _ IHs).
Qed.

Lemma zm_alg_eval_respects@{+} (s t : FATerm A) :
  fa_eq s t → zm_alg_eval s ≈ zm_alg_eval t.
Proof.
  intro H.
  refine (transitivity (symmetry (zm_alg_fold s)) _).
  refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
  exact (zm_alg_fold t).
Qed.

(*
 Every algebra's carrier is propositional, with no hypothesis: x ≈ y
 iff ⟨x⟩ ≈ ⟨y⟩ in ℤ[A], a [Prop]. 

 --------
 每个代数的载体是命题的，没有假设：x ≈ y 当且仅当 ⟨x⟩ ≈ ⟨y⟩ 在 ℤ [A] 中，a  [Prop]。
*)
Definition zm_alg_prop@{+} : PropEquiv (is_setoid A).
Proof using A α.
  unshelve refine
    (@Build_PropEquiv _ (is_setoid A)
       (fun x y => @fa_eq A (fa_gen x) (fa_gen y)) _ _).
  - intros x y H.
    refine (transitivity (symmetry (zm_alg_unit x)) _).
    refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
    exact (zm_alg_unit y).
  - intros x y H. exact (fae_gen H).
Defined.

(*
 The abelian group of the algebra: each law is one instance of
 [zm_alg_eval_respects] at a constructor of [fa_eq], so that “the
 values assigned to the sums of sums (a1 + a2) + (a3) and (a1) +
 (a2 + a3) are equal” is associativity. 

 --------
 代数的阿贝尔群：每条定律都是 [fa_eq] 的构造函数中 [zm_alg_eval_respects] 的一个实例，因此“分配给 (a1 + a2) + (a3) 和 (a1) + (a2 + a3) 的和的值相等”就是结合律。
*)
Definition zm_alg_ab@{+} : AbObject := {|
  ab_cmon := {|
    cmon_setoid := A;
    cmon_zero := zm_alg_zero;
    cmon_plus := zm_alg_plus;
    cmon_plus_respects := zm_alg_plus_respects;
    cmon_plus_assoc := fun x y z =>
      zm_alg_eval_respects _ _ (fae_assoc (fa_gen x) (fa_gen y) (fa_gen z));
    cmon_plus_comm := fun x y =>
      zm_alg_eval_respects _ _ (fae_comm (fa_gen x) (fa_gen y));
    cmon_plus_zero_l := fun x =>
      zm_alg_eval_respects _ _ (fae_zero_l (fa_gen x));
    cmon_prop := zm_alg_prop
  |};
  ab_neg := zm_alg_neg;
  ab_neg_respects := zm_alg_neg_respects;
  ab_neg_left := fun x => zm_alg_eval_respects _ _ (fae_neg_l (fa_gen x))
|}.

End Algebra.

(* An algebra map is additive: Riehl's “a function f : A → B that preserves the evaluation of formal sums, i.e., a group homomorphism”. / 代数映射是可加的：Riehl 的“一个函数 f : A → B，保持形式和的运算，即，一个群同态”。 *)
Lemma zm_alg_hom_step@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y)
  (t : FATerm (projT1 x)) :
  t_alg_hom[f] (t_alg[projT2 x] t)
    ≈ t_alg[projT2 y] (fa_relabel t_alg_hom[f] t).
Proof.
  refine (transitivity (@t_alg_hom_commutes _ _ _ _ _ _ _ f t) _).
  apply (proper_morphism t_alg[projT2 y]).
  exact (ZM_map_equiv t_alg_hom[f] t).
Qed.

Definition zm_alg_hom_ab@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  zm_alg_ab (projT2 x) ~{Ab}~> zm_alg_ab (projT2 y).
Proof.
  refine (@Build_CMonHom (zm_alg_ab (projT2 x)) (zm_alg_ab (projT2 y))
            t_alg_hom[f] _ _).
  - exact (zm_alg_hom_step f fa_zero).
  - intros a b. exact (zm_alg_hom_step f (fa_plus (fa_gen a) (fa_gen b))).
Defined.

(* The functor Set^{ℤ[−]} → Ab. / 函子 Set^{ℤ [−] } → Ab。 *)
Definition EM_to_AbS@{+} : ZMAlg ⟶ Ab.
Proof.
  unshelve refine
    (@Build_Functor ZMAlg Ab (fun x => zm_alg_ab (projT2 x))
       (fun x y f => zm_alg_hom_ab f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(*
 The fold of the identity in the derived group IS [zm_alg_eval]
 (Leibniz, by induction). 

 --------
 在导出群中的恒等式的折叠是 [zm_alg_eval] （莱布尼茨，通过归纳法）。
*)
Lemma zm_fold_is_alg_eval@{+} {A : Sets@{c so}}
  (α : @TAlgebra Sets@{c so} FreeAbF FreeAbMonad A) (t : FATerm A) :
  fa_eval (A := zm_alg_ab α) (@id Sets@{c so} (Ab_Forget (zm_alg_ab α))) t
  = zm_alg_eval α t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs ]; simpl;
    try rewrite IHs; try rewrite IHu; reflexivity.
Qed.

(* The algebra round trip, with the identity as its component. / 代数往返，以恒等式作为其组成部分。 *)
Definition Ab_EM_counit_iso@{+} (x : ZMAlg) :
  @Isomorphism ZMAlg (fobj[Ab_K ◯ EM_to_AbS] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism ZMAlg (fobj[Ab_K ◯ EM_to_AbS] x) x
       (@Build_TAlgebraHom Sets@{c so} FreeAbF FreeAbMonad
          (projT1 x) (projT1 x)
          (projT2 (fobj[Ab_K ◯ EM_to_AbS] x)) (projT2 x)
          (@id Sets@{c so} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{c so} FreeAbF FreeAbMonad
          (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Ab_K ◯ EM_to_AbS] x))
          (@id Sets@{c so} (projT1 x)) _) _ _).
  - intro t.
    change (fa_eval (A := zm_alg_ab (projT2 x))
              (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x)))) t
            ≈ t_alg[projT2 x] (fmap[FreeAbF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (zm_fold_is_alg_eval (projT2 x) t).
    refine (transitivity (symmetry (zm_alg_fold (projT2 x) t)) _).
    apply (proper_morphism t_alg[projT2 x]).
    symmetry. exact (@fmap_id _ _ FreeAbF (projT1 x) t).
  - intro t.
    change (t_alg[projT2 x] t
            ≈ fa_eval (A := zm_alg_ab (projT2 x))
                (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x))))
                (fmap[FreeAbF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (zm_fold_is_alg_eval (projT2 x)).
    refine (transitivity (zm_alg_fold (projT2 x) t) _).
    apply zm_alg_eval_respects.
    exact (fae_sym (@fmap_id _ _ FreeAbF (projT1 x) t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(*
 The group round trip, with the identity as its component: on a group
 the derived operations ARE its own. 

 --------
 群的往返旅行，其分量是恒等元：在一个群上，导出运算就是它自身的运算。
*)
Definition Ab_EM_unit_iso@{+} (G : Ab) :
  @Isomorphism Ab (fobj[EM_to_AbS ◯ Ab_K] G) G.
Proof.
  unshelve refine
    (@Build_Isomorphism Ab (fobj[EM_to_AbS ◯ Ab_K] G) G
       (@Build_CMonHom (fobj[EM_to_AbS ◯ Ab_K] G) G
          (@id Sets@{c so} (Ab_Forget G)) _ _)
       (@Build_CMonHom G (fobj[EM_to_AbS ◯ Ab_K] G)
          (@id Sets@{c so} (Ab_Forget G)) _ _) _ _).
  all: simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. / K 是一个等价关系，两边都有恒等分量。 *)
Definition Ab_EM_equivalence@{+} :
  @EquivalenceOfCategories Ab ZMAlg Ab_K.
Proof.
  unshelve refine (@Build_EquivalenceOfCategories _ _ Ab_K EM_to_AbS _ _).
  - exists (fun x => Ab_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun G => iso_sym (Ab_EM_unit_iso G)). intros G H f a. reflexivity.
Defined.

(* Abelian groups are monadic over Set. / 阿贝尔群在集合上是单子的。 *)
Definition Ab_Forget_Monadic@{+} : Monadic Ab_Forget.
Proof.
  exists FreeAb. exists free_ab_adjunction_hom. exact Ab_EM_equivalence.
Defined.

(* Ab ≅ Set^{ℤ[−]} in Cat, from the two component isomorphisms. / Ab ≅ Set^{ℤ [−]} 在 Cat 中，由两个分量同构得到。 *)
Definition Ab_EM_iso@{k +} : @Isomorphism Cat@{k so so so c} Ab ZMAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{k so so so c} Ab ZMAlg Ab_K EM_to_AbS _ _).
  - exists (fun x => Ab_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun G => Ab_EM_unit_iso G). intros G H f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks / ** 回读 *)

(* K G is ⟨G, U ε_G⟩: the evaluation of a formal sum to its actual sum. / K G 是 ⟨G, U ε_G⟩：将形式和的评估得到其实际和。 *)
Example Ab_K_carrier@{+} (G : Ab) : projT1 (fobj[Ab_K] G) = Ab_Forget G
  := eq_refl.

Example Ab_K_map@{+} {G H : Ab} (f : G ~{Ab}~> H) :
  t_alg_hom[fmap[Ab_K] f] = fmap[Ab_Forget] f := eq_refl.

Example Ab_K_alg@{+} (G : Ab) :
  t_alg[projT2 (fobj[Ab_K] G)]
    = fmap[Ab_Forget] (@counit _ _ _ _ free_ab_adjunction_hom G) := eq_refl.

Example Ab_K_alg_fun@{+} (G : Ab) (t : FATerm (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] t = fa_eval (@id Sets@{c so} (Ab_Forget G)) t
  := eq_refl.

Example Ab_K_alg_gen@{+} (G : Ab) (x : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_gen x) = x := eq_refl.

Example Ab_K_alg_zero@{+} (G : Ab) :
  t_alg[projT2 (fobj[Ab_K] G)] fa_zero = cmon_zero G := eq_refl.

Example Ab_K_alg_plus@{+} (G : Ab) (x y : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_plus (fa_gen x) (fa_gen y))
    = cmon_plus G x y := eq_refl.

Example Ab_K_alg_neg@{+} (G : Ab) (x : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_neg (fa_gen x)) = ab_neg G x := eq_refl.

(* The legs of the isomorphism in Cat. / Cat 中同构的腿。 *)
Example Ab_EM_iso_to@{+} : to Ab_EM_iso = Ab_K := eq_refl.

Example Ab_EM_iso_from@{+} : from Ab_EM_iso = EM_to_AbS := eq_refl.

(* The group of an algebra: its carrier, its [Prop] equality and its operations. / 一个代数的群：它的载体、它的 [Prop] 等式及其运算。 *)
Example EM_to_AbS_prop@{+} (x : ZMAlg) (a b : carrier (projT1 x)) :
  @pequiv _ _ (cmon_prop (fobj[EM_to_AbS] x)) a b
    = @fa_eq (projT1 x) (fa_gen a) (fa_gen b) := eq_refl.

Example EM_to_AbS_carrier@{+} (x : ZMAlg) :
  cmon_setoid (fobj[EM_to_AbS] x) = projT1 x := eq_refl.

Example EM_to_AbS_zero@{+} (x : ZMAlg) :
  cmon_zero (fobj[EM_to_AbS] x) = t_alg[projT2 x] fa_zero := eq_refl.

Example EM_to_AbS_plus@{+} (x : ZMAlg) (a b : carrier (projT1 x)) :
  cmon_plus (fobj[EM_to_AbS] x) a b
    = t_alg[projT2 x] (fa_plus (fa_gen a) (fa_gen b)) := eq_refl.

Example EM_to_AbS_neg@{+} (x : ZMAlg) (a : carrier (projT1 x)) :
  ab_neg (fobj[EM_to_AbS] x) a = t_alg[projT2 x] (fa_neg (fa_gen a))
  := eq_refl.

Example EM_to_AbS_map@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  cmon_map (fmap[EM_to_AbS] f) = t_alg_hom[f] := eq_refl.

(* The round trips keep every operation on the nose ... / 往返保持每个操作都精准无误... *)
Example Ab_rt_carrier@{+} (G : Ab) :
  cmon_setoid (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_setoid G := eq_refl.

Example Ab_rt_zero@{+} (G : Ab) :
  cmon_zero (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_zero G := eq_refl.

Example Ab_rt_plus@{+} (G : Ab) :
  cmon_plus (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_plus G := eq_refl.

Example Ab_rt_neg@{+} (G : Ab) :
  ab_neg (fobj[EM_to_AbS ◯ Ab_K] G) = ab_neg G := eq_refl.

Example Ab_rt_hom@{+} {G H : Ab} (f : G ~{Ab}~> H) :
  cmon_map (fmap[EM_to_AbS ◯ Ab_K] f) = cmon_map f := eq_refl.

(* ... and so do the carrier and the maps of the algebra round trip. / ... 载体以及代数往返的映射也是如此。 *)
Example ZMAlg_rt_carrier@{+} (x : ZMAlg) :
  projT1 (fobj[Ab_K ◯ EM_to_AbS] x) = projT1 x := eq_refl.

Example ZMAlg_rt_alg_fun@{+} (x : ZMAlg) (t : FATerm (projT1 x)) :
  t_alg[projT2 (fobj[Ab_K ◯ EM_to_AbS] x)] t
    = fa_eval (A := zm_alg_ab (projT2 x))
        (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x)))) t
  := eq_refl.

Example ZMAlg_rt_alg_hom@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  t_alg_hom[fmap[Ab_K ◯ EM_to_AbS] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity. / 这两个自然同构的每一个组成部分都是恒等映射。 *)
Example Ab_EM_iso_to_from_component@{+} (x : ZMAlg) :
  (t_alg_hom[to (projT1 (iso_to_from Ab_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Ab_EM_iso) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example Ab_EM_iso_from_to_component@{+} (G : Ab) :
  (cmon_map (to (projT1 (iso_from_to Ab_EM_iso) G)),
   cmon_map (from (projT1 (iso_from_to Ab_EM_iso) G)))
    = (@id Sets@{c so} (Ab_Forget G), @id Sets@{c so} (Ab_Forget G))
  := eq_refl.

(* ...and so is every component of the equivalence's counit and unit. / ...并且等价的余单位和单位的每个组成部分也是如此。 *)
Example Ab_EM_counit_component@{+} (x : ZMAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Ab_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _ Ab_EM_equivalence) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example Ab_EM_unit_component@{+} (G : Ab) :
  (cmon_map (to (projT1 (@equivalence_unit _ _ _ Ab_EM_equivalence) G)),
   cmon_map (from (projT1 (@equivalence_unit _ _ _ Ab_EM_equivalence) G)))
    = (@id Sets@{c so} (Ab_Forget G), @id Sets@{c so} (Ab_Forget G))
  := eq_refl.

End FreeAbMonad.
