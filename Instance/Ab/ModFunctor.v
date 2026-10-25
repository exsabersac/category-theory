(* * * R-Mod as the additive functors out of B(R) / * * R-Mod 作为从 B(R) 出发的加法函子 *)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
 ed., §II.4, Exercise 1, printed p. 41 (PDF 51) —
 maclane:II.4:ex1
 Book:      Mac Lane, ibid., §I.8, printed pp. 28-29 —
 maclane:I.8:def4, maclane:I.8:def6
 nLab:      https://ncatlab.org/nlab/show/Ab-enriched+category
 nLab:      https://ncatlab.org/nlab/show/module
 Wikipedia: https://en.wikipedia.org/wiki/Module_(mathematics)

 Mac Lane's Exercise 1 of §II.4 has two clauses.  This file proves
 the second in full and the first in the direction the second
 consumes.  First: a ring R IS a one-object Ab-category — one
 object, the hom-group is R's additive group, composition is R's
 multiplication.  (The CONVERSE — reading a ring off an arbitrary
 one-object Ab-enriched category — is not built here: the rig-level
 biconditional [rig_iff_one_object_preadditive] with its [EndRig]
 half is in Theory/Algebra/Rig.v, and its ring-level negation-adding
 counterpart is left for whoever needs it; see WHAT IS NOT BUILT.)
 Second: an R-module is exactly an ADDITIVE functor from that
 one-object Ab-category into Ab, and a module homomorphism is exactly
 a natural transformation between two such; so R-Mod is the full
 subcategory of the functor category [B(R), Ab] spanned by the
 additive functors.

 WHAT IS REUSED, AND WHERE THE NEW STEP IS.  The rig-level half of the
 first clause is already in tree: Theory/Algebra/Rig.v's [DeloopRig]
 deloops the MULTIPLICATIVE monoid of a rig into a one-object category
 and [DeloopRig_Preadditive] equips it with the CMon-enrichment whose
 four clauses ARE the rig axioms, packaged there as
 [rig_iff_one_object_preadditive].  A ring is a rig with negatives, so
 the only step this file adds at that level is the NEGATION:
 [DeloopRing_AbEnriched] upgrades the preadditive structure on
 [DeloopRig (ring_rig R)] to Structure/AbCategory.v's [AbEnriched] by
 taking [abneg] to be [ring_neg] and reading [padd_abneg] off
 [ring_neg_l].  Nothing else about the delooping is rebuilt; the
 readings [padd = rig_add], [compose = rig_mul], [id = rig_one] and
 [abneg = ring_neg] are recorded as conversions ([eq_refl] Examples;
 [deloop_ring_hom] compares types, while the other four are stated
 at applied arguments and so compare MORPHISMS of the delooping by
 Leibniz equality — a deliberate convertibility strengthening of the
 house `≈` rule, labelled at the Examples themselves).

 WHERE ADDITIVITY IS SPENT.  This is the pivot of the exercise, and it
 is a single field on each side.  Of the four module laws in
 Instance/Mod.v's [RModObject], three come from the functor structure
 alone:

 - [rm_smul_distr_l] (r·(m+n) = r·m + r·n) is [cmon_map_plus] of the
 Ab-morphism [fmap[F] r] — every functor into Ab has it, for free;
 - [rm_smul_assoc] ((r·s)·m = r·(s·m)) is [fmap_comp], because
 composition in [DeloopRig] IS multiplication;
 - [rm_smul_one] (1·m = m) is [fmap_id], because the identity IS 1.

 The fourth, [rm_smul_distr_r] ((r+s)·m = r·m + s·m), is NOT available
 from functoriality: it is exactly [fmap_padd], the single field of
 Structure/AbCategory.v's [AdditiveFunctor].  So the additive
 hypothesis is neither decoration nor convenience — it is precisely the
 right-distributivity law of a module, and the correspondence is a
 biconditional at the level of that one law.  The witnesses below make
 the point concretely: [unit_act_functor R] and [square_functor] are
 genuine functors into Ab — multiplicative and unital, since that is
 all a functor out of a one-object category owes — and at R = ℤ each
 is provably NOT additive, so the subcategory is PROPER: the predicate
 genuinely cuts.

 THE COLLAPSE.  A natural transformation between two functors out of a
 ONE-OBJECT category is a single morphism of the target, and its
 naturality is a single square, one instance per arrow of the source
 — i.e. one equation per ring element.  That equation, read through
 the dictionary above, IS Instance/Mod.v's [rm_map_smul].  So the
 hom-level half of the exercise costs no argument at all:
 [AbFunAdd_to]'s action on morphisms is [transform[η] ttt] with
 [naturality_sym] as the module-map law, and [AbFunAdd_from]'s is the
 constant family with [rm_map_smul] as naturality.  This is the
 architecture of Instance/Rep.v (issue #279) and, before it,
 Instance/Fun/Action.v; it is followed rather than re-invented,
 including the transparent round-trip component family.

 RELATION TO Instance/Rep.v.  That file is the MULTIPLICATIVE story at
 the same one-object spine: representations of a GROUP are functors
 [Deloop G ⟶ RMod K], and nothing there is enriched — [Deloop]
 deloops a bare monoid and the target's additive structure plays no
 part.  This file adds the ADDITIVE enrichment on the source side, and
 that is the whole difference: [Deloop] becomes [DeloopRig], "functor"
 becomes "additive functor", and the resulting category is R-Mod
 rather than Rep_K(G).  Structure/AbCategory.v's [AbCat] is the
 ambient category in which [DeloopRig (ring_rig R)] and [Ab] both
 live as objects; it is not needed for the statement below and is not
 used, but it is what makes "one-object Ab-category" a term of art
 rather than a phrase.

 WHAT IS PROVED.  [RMod_AbFun_equiv R : AbFunAdd R ≅[Cat] RMod R],
 with the functor-category side on the left, matching Instance/Rep.v's
 [Rep_Fun_equiv] and Instance/Fun/Action.v's [MSet_Fun_equiv].  Read
 the strength precisely: [Cat]'s hom-setoid is [Functor_Setoid],
 i.e. natural isomorphism (Instance/Cat.v), so [≅[Cat]] is an
 EQUIVALENCE of categories, not an isomorphism — which is what
 "R-Mod IS the full subcategory" means here, and is why the exercise's
 word "is" is rendered by an equivalence.  Both comparison functors
 are, however, better than the statement requires: the module-side
 round trip is the IDENTITY module map (the carrier and the action are
 recovered definitionally, [module_round_smul]), and the functor-side
 round trip has identity components.

 WHAT IS NOT BUILT.  No right-module or bimodule reading (Mod.v's
 [ModR]/[Bimodule] stay where they are), no tensor product, no
 varying-R functoriality, no comparison with [AbCat] as a category,
 and no ring-level [EndRing] converse (reading a [RingObject] off a
 one-object [AbEnriched] category — the negation-adding counterpart
 of Rig.v's [EndRig]) — the exercise asks for the one identification
 and that is what is delivered. 

 --------
 书籍：      Mac Lane，《为工作中的数学家准备的范畴》，第2版，第II.4节，练习1，印刷页41（PDF 51）—— maclane:II.4:ex1
 书籍：      Mac Lane，同上，第I.8节，印刷页28-29 —— maclane:I.8:def4, maclane:I.8:def6
 nLab：       https://ncatlab.org/nlab/show/Ab-enriched+category
 nLab：       https://ncatlab.org/nlab/show/module
 维基百科：  https://en.wikipedia.org/wiki/Module_(mathematics)麦克莱恩在§II.4的练习1有两个条款。此文件完全证明了第二条款，并在第二条款所涉及的方向上证明了第一条款。首先：一个环R是一个单对象Ab-范畴——只有一个对象，同态群是R的加法群，复合是R的乘法。(（相反——从任意一对象 Ab-增强范畴读取一个环——在这里没有构建：带有其 [EndRig] 一半的环层双条件 [rig_iff_one_object_preadditive] 在 Theory/Algebra/Rig.v 中，其环层加否定的对应部分留给有需要的人；参见 WHAT IS NOT BUILT。）
 第二：一个 R-模恰好是从那个一对象 Ab-范畴到 Ab 的加性函子，而一个模同态恰好是两个这样的函子之间的自然变换；因此 R-Mod 是由加性函子生成的函子范畴 [B(R), Ab] 的满子范畴。)什么是重复使用的，以及新的步骤在哪里。第一个子句中涉及rig级别的部分已经在树中：Theory/Algebra/Rig.v 的 [DeloopRig] 将一个rig的乘法半群拆解为一个单对象范畴，而 [DeloopRig_Preadditive] 为其配备了CMon增强，其四个子句是rig公理，在 [rig_iff_one_object_preadditive] 中打包。环是带有负元的rig，所以该文件在该级别唯一添加的步骤是取负：[DeloopRing_AbEnriched] 将 [DeloopRig (ring_rig R)] 上的预加法结构升级为 Structure/AbCategory.v 的 [AbEnriched]，通过将 [abneg] 视为 [ring_neg] 并从 [ring_neg_l] 中读取 [padd_abneg]。关于解除环处理的其他内容没有重建；读取 [padd = rig_add]、[compose = rig_mul]、[id = rig_one] 和 [abneg = ring_neg] 被记录为转换（[eq_refl] 示例；[deloop_ring_hom] 比较类型，而其他四个在应用的参数上陈述，因此通过莱布尼茨等式比较解除环的态射——这是对 `≈` 规则的一种有意可转换性强化，在示例本身标注）。

 加法性耗尽的地方。这是练习的核心，并且在每一边都是单个字段。在 Instance/Mod.v 的 [RModObject] 中的四个模法则中，有三个仅来自函子结构：- [rm_smul_distr_l]（r·(m+n) = r·m + r·n）是 [cmon_map_plus] 的 Ab-同态 [fmap[F] r] —— 每个到 Ab 的函子都有它，免费提供；
 - [rm_smul_assoc]（(r·s)·m = r·(s·m)）是 [fmap_comp]，因为 [DeloopRig] 中的复合就是乘法；
 - [rm_smul_one]（1·m = m）是 [fmap_id]，因为恒等元就是 1。第四个，[rm_smul_distr_r] ((r+s)·m = r·m + s·m)，无法通过函子性获得：它正是[fmap_padd]，即Structure/AbCategory.v的[AdditiveFunctor]的单一字段。因此，加法假设既不是装饰也不是方便——它恰好是模的右分配律，并且这种对应在这一条律层面上是双向的。下面的例子具体说明了这一点：[unit_act_functor R]和[square_functor]是真正的到Ab的函子——是乘法的且有单位的，因为一个单对象范畴的函子只需要这些——并且在R = ℤ时，每个都可证明不是加法的，因此子范畴是严格的：谓词确实起到了切割作用。崩溃。来自单对象范畴的两个函子之间的自然变换是目标中的一个单一态射，其自然性是一个单一的方框，每个源箭头一个实例——即每个环元素一个方程。通过上面的词典读取，该方程就是 Instance/Mod.v 的 [rm_map_smul]。因此，练习的同态层面几乎不需要论证：[AbFunAdd_to] 对态射的作用是 [transform[η] ttt]，[naturality_sym] 作为模映射律，而 [AbFunAdd_from] 的作用是常值族，[rm_map_smul] 作为自然性。这就是 Instance/Rep.v（问题 #279）以及它之前的 Instance/Fun/Action.v 的架构；它是沿用而不是重新发明的，包括透明的往返组件族。与 Instance/Rep.v 的关系。该文件是相同单对象脊上的乘法故事：一个群的表示是函子 [Deloop G ⟶ RMod K]，而那里没有任何丰富结构——[Deloop] 将一个裸单子分层，并且目标的加法结构不起作用。该文件在源端增加了加法丰富结构，这就是全部区别：[Deloop] 变为 [DeloopRig]，"functor" 变为 "additive functor"，结果类是 R-Mod 而非 Rep_K(G)。Structure/AbCategory.v 中的 [AbCat] 是 [DeloopRig (ring_rig R)] 和 [Ab] 作为对象存在的环境类别；它对于下面的陈述不是必需的，也没有被使用，但它使得 "one-object Ab-category" 成为一个术语，而不仅仅是一个短语。已证明。[RMod_AbFun_equiv R : AbFunAdd R ≅[Cat] RMod R]，左侧为函子范畴一侧，对应 Instance/Rep.v 的 [Rep_Fun_equiv] 和 Instance/Fun/Action.v 的 [MSet_Fun_equiv]。精确理解其强度：[Cat] 的同态集合是 [Functor_Setoid]，即自然同构（Instance/Cat.v），所以 [≅[Cat] ] 是范畴的等价，而不是同构——这就是这里“R-Mod 是全子范畴”的含义，也是练习中“is”这个词被翻译为等价的原因。然而，这两个比较函子都比陈述要求的更强：模一侧的往返映射是恒等模映射（载体和作用可以按定义还原，[module_round_smul]），函子一侧的往返映射各分量为恒等映射。尚未构建的内容。没有右模或双模读取（Mod.v 的 [ModR] / [Bimodule] 保持不变），没有张量积，没有变化-R函子性，没有与 [AbCat] 作为范畴的比较，也没有环级 [EndRing] 的逆命题（从单对象 [AbEnriched] 范畴中读取 [RingObject]——Rig.v 的 [EndRig] 的加否定对应物）——练习要求一个识别，而这正是所提供的内容。
*)

(* * ** The Ab-enrichment of the delooping of a ring / * ** 环的去环化的Ab-增强 *)

(*
 [DeloopRig (ring_rig R)] is Mac Lane's one-object Ab-category B(R):
 one object, hom-group the additive group of R, composition the
 multiplication.  Theory/Algebra/Rig.v already supplies the category
 and the CMon-enrichment; a ring adds negatives, so the only new datum
 is [abneg], and its law is [ring_neg_l] after commuting the sum. 

 --------
 [DeloopRig (ring_rig R)] 是 Mac Lane 的单对象 Ab-范畴 B(R)：
 一个对象，Hom 群为 R 的加法群，复合为乘法。Theory/Algebra/Rig.v 已经提供了该范畴和 CMon-加强；一个环添加了负元，所以唯一的新数据是 [abneg]，其规律是 [ring_neg_l] 在交换和之后。
*)
Program Definition DeloopRing_AbEnriched (R : RingObject) :
  AbEnriched (DeloopRig (ring_rig R)) := {|
  abenriched_preadditive := DeloopRig_Preadditive (ring_rig R);
  abneg := fun _ _ => ring_neg R
|}.
Next Obligation.
  intros R x y f; simpl.
  rewrite (rig_add_comm (ring_rig R) f (ring_neg R f)).
  exact (ring_neg_l R f).
Qed.
(* [abneg_respects] needs no obligation: the field is a [Proper] class and Rig.v exports [ring_neg_respects] as an instance, so elaboration discharges it. / [abneg_respects] 不需要任何义务：该字段是 [Proper] 类，并且 Rig.v 导出 [ring_neg_respects] 作为一个实例，因此展开完成它。 *)

(*
 Mac Lane's first clause, as conversions: the hom-set of B(R) IS the
 carrier of R, composition IS multiplication, the identity IS 1, the
 enrichment's addition IS the ring's addition and its negation IS the
 ring's negation.  [deloop_ring_hom] is an equality of TYPES; the
 other four are stated at applied arguments and so compare MORPHISMS
 of the delooping by Leibniz [eq_refl] — deliberate, and sound
 exactly because both sides are convertible; the house `≈` rule
 governs morphism statements that are not. 

 --------
 Mac Lane 的第一个条款，作为转换：B(R) 的同态集就是 R 的载体，组合就是乘法，恒等式就是 1，增广的加法就是环的加法，它的取负就是环的取负。[deloop_ring_hom] 是类型的等式；其他四个在应用参数下陈述，因此比较 Leibniz 的 delooping 的 MORPHISMS [eq_refl] —— 故意的，并且完全可靠，因为双方都是可转换的；house `≈` 规则管理那些不是的态射声明。
*)
Example deloop_ring_hom (R : RingObject) :
  (ttt ~{DeloopRig (ring_rig R)}~> ttt)
    = carrier (rig_setoid (ring_rig R)) := eq_refl.

Example deloop_ring_compose (R : RingObject)
  (r s : ttt ~{DeloopRig (ring_rig R)}~> ttt) :
  r ∘ s = rig_mul (ring_rig R) r s := eq_refl.

Example deloop_ring_id (R : RingObject) :
  @id (DeloopRig (ring_rig R)) ttt = rig_one (ring_rig R) := eq_refl.

Example deloop_ring_padd (R : RingObject)
  (r s : ttt ~{DeloopRig (ring_rig R)}~> ttt) :
  @padd _ (DeloopRig_Preadditive (ring_rig R)) ttt ttt r s
    = rig_add (ring_rig R) r s := eq_refl.

Example deloop_ring_abneg (R : RingObject)
  (r : ttt ~{DeloopRig (ring_rig R)}~> ttt) :
  @abneg _ (DeloopRing_AbEnriched R) ttt ttt r = ring_neg R r := eq_refl.

(* * ** The full subcategory of additive functors / * ** 加法函子的完整子范畴 *)

(*
 The predicate is Structure/AbCategory.v's class itself, at the two
 enrichments — the honest reading of "spanned by the additive
 functors".  It is [Type]-valued, which is what [Subcategory]'s [sobj]
 asks for. 

 --------
 谓词是 Structure/AbCategory.v 的类本身，在两个扩展中 — 对“由加性函子张成”的诚实解读。它是 [Type] 值，这是 [Subcategory] 的 [sobj] 所要求的。
*)
Definition IsAdditiveFun (R : RingObject)
  (F : DeloopRig (ring_rig R) ⟶ Ab) : Type :=
  @AdditiveFunctor (DeloopRig (ring_rig R)) Ab
    (DeloopRing_AbEnriched R) Ab_AbEnriched F.

(*
 Full: every natural transformation between two additive functors is
 retained ([True]/[I]), the idiom of Theory/Sheaf/Category.v's
 [Sheaves_sub] and Instance/Rng.v's [CRng_Sub].  Parsing gotcha for
 sibling files: [ [C, D] ] is a level-90 notation and cannot appear
 as a bare application argument — [Subcategory [X, Y]] is a hard
 parse error, so every use below writes [([X, Y])] with explicit
 parentheses. 

 --------
 完整：两个加性函子之间的每个自然变换都被保留（[True] / [I]），这是 Theory/Sheaf/Category.v 的 [Sheaves_sub] 和 Instance/Rng.v 的 [CRng_Sub] 的惯用法。兄弟文件的解析注意事项：[ [C, D]] 是一个 90 级记号，不能作为裸应用参数出现——[Subcategory [X, Y]] 是一个严重的解析错误，因此下面的每次使用都写作 [([X, Y])]，并加上显式括号。
*)
Definition AbFunAdd_sub (R : RingObject) :
  Subcategory ([DeloopRig (ring_rig R), Ab]) :=
  @Build_Subcategory ([DeloopRig (ring_rig R), Ab])
    (fun F => IsAdditiveFun R F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition AbFunAdd (R : RingObject) : Category :=
  Sub ([DeloopRig (ring_rig R), Ab]) (AbFunAdd_sub R).

Lemma AbFunAdd_Full (R : RingObject) :
  Category.Construction.Subcategory.Full
    ([DeloopRig (ring_rig R), Ab]) (AbFunAdd_sub R).
Proof. intros F G HF HG η; exact I. Qed.

Definition AbFunAdd_Incl (R : RingObject) :
  AbFunAdd R ⟶ [DeloopRig (ring_rig R), Ab] :=
  Incl ([DeloopRig (ring_rig R), Ab]) (AbFunAdd_sub R).

(* * ** From an additive functor to a module / * ** 从加性函子到模 *)

(*
 The action of a ring element on the value of the functor at the single
 object: apply the Ab-morphism [fmap[F] r].  Every module law below is
 one functor law read through this definition. 

 --------
 环元素在单对象上函子值的作用：应用阿贝尔群态射 [fmap[F]  r]。以下每一个模律都是通过此定义理解的一个函子律。
*)
Definition fun_module_smul {R : RingObject}
  (F : DeloopRig (ring_rig R) ⟶ Ab)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (F ttt : AbObject))) :
  carrier (cmon_setoid (F ttt : AbObject)) :=
  cmon_map (@fmap _ _ F ttt ttt r) m.

(*
 THE PIVOT.  [rm_smul_distr_l] is [cmon_map_plus], [rm_smul_assoc] is
 [fmap_comp] (composition IS multiplication), [rm_smul_one] is
 [fmap_id] (the identity IS 1) — all three free from any functor into
 Ab.  Only [rm_smul_distr_r] needs [HF], and it is exactly
 [fmap_padd]. 

 --------
 支点。[rm_smul_distr_l] 是 [cmon_map_plus]，[rm_smul_assoc] 是 [fmap_comp]（组合即乘法），[rm_smul_one] 是 [fmap_id]（同一性是 1）——这三者都不依赖于映射到 Ab 的函子。只有 [rm_smul_distr_r] 需要 [HF]，并且它正好是 [fmap_padd]。
*)
Program Definition module_of_functor {R : RingObject}
  (F : DeloopRig (ring_rig R) ⟶ Ab) (HF : IsAdditiveFun R F) :
  RModObject R := {|
  rm_ab   := (F ttt : AbObject);
  rm_smul := fun_module_smul F
|}.
Next Obligation.
  intros R F HF r s Hrs m n Hmn; unfold fun_module_smul.
  transitivity (cmon_map (@fmap _ _ F ttt ttt r) n).
  - exact (proper_morphism (cmon_map (@fmap _ _ F ttt ttt r)) m n Hmn).
  - exact (@fmap_respects _ _ F ttt ttt r s Hrs n).
Qed.
Next Obligation.
  intros R F HF r m n; unfold fun_module_smul.
  exact (cmon_map_plus (@fmap _ _ F ttt ttt r) m n).
Qed.
Next Obligation.
  intros R F HF r s m; unfold fun_module_smul.
  exact (@fmap_padd _ _ (DeloopRing_AbEnriched R) Ab_AbEnriched F HF
           ttt ttt r s m).
Qed.
Next Obligation.
  intros R F HF r s m; unfold fun_module_smul.
  exact (@fmap_comp _ _ F ttt ttt ttt r s m).
Qed.
Next Obligation.
  intros R F HF m; unfold fun_module_smul.
  exact (@fmap_id _ _ F ttt m).
Qed.

(* * ** From a module to an additive functor / * ** 从模到加法函子 *)

(*
 Action by a fixed scalar, as a morphism of Ab: additivity of the map
 is [rm_smul_distr_l] and preservation of zero is [rm_smul_zero_r]. 

 --------
 由固定标量的作用，作为 Ab 的态射：映射的可加性是 [rm_smul_distr_l]，零的保持是 [rm_smul_zero_r]。
*)
Program Definition module_act {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) :
  (rm_ab M : Ab) ~{Ab}~> (rm_ab M : Ab) := {|
  cmon_map := {| morphism := fun m => rm_smul M r m |}
|}.
Next Obligation.
  intros R M r m n Hmn.
  exact (rm_smul_respects M r r (reflexivity r) m n Hmn).
Qed.
Next Obligation.
  intros R M r; simpl.
  exact (rm_smul_zero_r M r).
Qed.
Next Obligation.
  intros R M r m n; simpl.
  exact (rm_smul_distr_l M r m n).
Qed.

Program Definition functor_of_module {R : RingObject} (M : RModObject R) :
  DeloopRig (ring_rig R) ⟶ Ab := {|
  fobj := fun _ => (rm_ab M : Ab);
  fmap := fun _ _ r => module_act M r
|}.
Next Obligation.
  intros R M x y r s Hrs m; simpl.
  exact (rm_smul_respects M r s Hrs m m (reflexivity m)).
Qed.
Next Obligation.
  intros R M x m; simpl.
  exact (rm_smul_one M m).
Qed.
Next Obligation.
  intros R M x y z r s m; simpl.
  exact (rm_smul_assoc M r s m).
Qed.

(* ...and it is additive, that field being [rm_smul_distr_r] — the other half of the pivot. / ...并且它是可加的，该字段为 [rm_smul_distr_r] —— 枢轴的另一半。 *)
Definition functor_of_module_additive {R : RingObject} (M : RModObject R) :
  IsAdditiveFun R (functor_of_module M).
Proof.
  constructor; intros x y r s m; simpl.
  exact (rm_smul_distr_r M r s m).
Defined.

(*
 The action of the module is recovered by the functor, definitionally,
 and so is the underlying group. 

 --------
 模的作用由函子按定义恢复，底层群也是如此。
*)
Example module_round_carrier {R : RingObject} (M : RModObject R) :
  ((functor_of_module M) ttt : AbObject) = rm_ab M := eq_refl.

Example module_round_smul {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  fun_module_smul (functor_of_module M) r m = rm_smul M r m := eq_refl.

(** ** The comparison functors / ** 比较函数对象 *)

(*
 A transformation over the single object is one Ab-morphism, and its
 naturality at r IS [rm_map_smul] — the collapse. 

 --------
 对单个对象的一个变换就是一个 Ab-态射，它在 r 处的自然性是 [rm_map_smul] — 崩塌。
*)
Program Definition AbFunAdd_to (R : RingObject) :
  AbFunAdd R ⟶ RMod R := {|
  fobj := fun FH => module_of_functor (`1 FH) (`2 FH);
  fmap := fun FH GH η => {| rm_hom := transform[`1 η] ttt |}
|}.
Next Obligation.
  intros R FH GH η r m; simpl.
  exact (@naturality_sym _ _ (`1 FH) (`1 GH) (`1 η) ttt ttt r m).
Qed.
Next Obligation.
  intros R FH GH η θ Hηθ; exact (Hηθ ttt).
Qed.
(*
 [Fun]'s identity transformation has [fmap[F] id] for its component,
 so this is [fmap_id] rather than [reflexivity] — the same step
 Instance/Rep.v's [Rep_to] takes. 

 --------
 [Fun] 的身份转换对于其组件有 [fmap[F] id]，所以这是 [fmap_id] 而不是 [reflexivity] —— 与实例/Rep.v 的 [Rep_to] 所采取的相同步骤。
*)
Next Obligation.
  intros R FH m; simpl.
  exact (@fmap_id _ _ (`1 FH) ttt m).
Qed.
Next Obligation.
  intros R FH GH KH η θ m; simpl; reflexivity.
Qed.

(*
 Conversely a module map is the constant family, its naturality being
 [rm_map_smul] again — the same equation read the other way. 

 --------
 相反，模图是恒等族，它的自然性再次是 [rm_map_smul] —— 同一方程从另一种方式解读。
*)
Program Definition AbFunAdd_from (R : RingObject) :
  RMod R ⟶ AbFunAdd R := {|
  fobj := fun M =>
    ((functor_of_module M; functor_of_module_additive M) : AbFunAdd R);
  fmap := fun M N f => ({| transform := fun _ => rm_hom f |}; I)
|}.
Next Obligation.
  intros R M N f [] [] r m; simpl.
  symmetry; exact (rm_map_smul f r m).
Qed.
Next Obligation.
  intros R M N f [] [] r m; simpl.
  exact (rm_map_smul f r m).
Qed.
Next Obligation.
  intros R M N f g Hfg []; exact Hfg.
Qed.
(*
 The identity of [AbFunAdd R] has [fmap] of the source identity for
 its component, i.e. the action of 1, so this is [rm_smul_one] — the
 mirror of the [fmap_id] step in [AbFunAdd_to]. 

 --------
 [AbFunAdd R] 的身份具有其组件来源身份的 [fmap]，即操作 1 的动作，所以这是 [rm_smul_one] —— [AbFunAdd_to] 中 [fmap_id] 步骤的镜像。
*)
Next Obligation.
  intros R M [] m; simpl.
  rewrite (rm_smul_one M m); reflexivity.
Qed.
Next Obligation.
  intros R M N P f g [] m; simpl; reflexivity.
Qed.

(** ** The two round trips / ** 两次往返 *)

(*
 Module side: the recovered module has the SAME underlying group and
 the SAME action (both [eq_refl] above), so the identity group
 homomorphism is a module map in both directions. 

 --------
 模块方面：恢复的模块具有相同的底层群和相同的作用（上面的 [eq_refl]），因此恒等群同态在两个方向上都是模块映射。
*)
Program Definition AbFunAdd_module_round {R : RingObject}
  (M : RModObject R) :
  @Isomorphism (RMod R)
    (module_of_functor (functor_of_module M)
       (functor_of_module_additive M)) M := {|
  to   := {| rm_hom := @cmon_hom_id (rm_ab M) |};
  from := {| rm_hom := @cmon_hom_id (rm_ab M) |}
|}.
Next Obligation. intros R M r m; simpl; reflexivity. Qed.
Next Obligation. intros R M r m; simpl; reflexivity. Qed.
Next Obligation. intros R M m; simpl; reflexivity. Qed.
Next Obligation. intros R M m; simpl; reflexivity. Qed.

(*
 Functor side, with a transparent component family: the equivalence
 has to compute with the components, so the in-tree opaque
 [functor_round] cannot serve (Instance/Rep.v's [Rep_round_iso] and
 Instance/Fun/Action.v's [MSet_round_iso] make the same move).  The
 subcategory's objects are written as [`1]/[`2] of the given one
 rather than destructured, since [sigT] has no definitional eta.
 Unlike the module side, THIS round trip is not definitional:
 [module_act] rebuilds a [CMonHom] record, so
 [fmap[functor_of_module (module_of_functor F HF)] r] is only
 ≈-equal to [fmap[F] r], not convertible (their underlying maps DO
 agree by [eq_refl]; the records differ in their law fields), and
 every obligation below is discharged pointwise. 

 --------
 函子侧，具有透明组件族：等价必须与组件一起计算，因此树内的不透明 [functor_round] 无法使用（Instance/Rep.v 的 [Rep_round_iso] 和 Instance/Fun/Action.v 的 [MSet_round_iso] 做了相同的操作）。子类别的对象写作 [`1] / [`2]，而不是解构的形式，因为 [sigT] 没有定义性的 eta。与模块侧不同，这次往返不是定义性的：[module_act] 重建了一个 [CMonHom] 记录，所以 [fmap[functor_of_module (module_of_functor F HF)] r] 只是 ≈-等于 [fmap[F] r]，而不是可转换的（它们的底层映射确实通过 [eq_refl] 一致；记录在法则字段上不同），以下的每个要求都是逐点解决的。
*)
Program Definition AbFunAdd_functor_round {R : RingObject}
  (FH : AbFunAdd R) :
  @Isomorphism (AbFunAdd R)
    ((functor_of_module (module_of_functor (`1 FH) (`2 FH));
      functor_of_module_additive
        (module_of_functor (`1 FH) (`2 FH))) : AbFunAdd R) FH := {|
  to := ({| transform := fun x =>
    match x return
      (functor_of_module (module_of_functor (`1 FH) (`2 FH)) x
         ~{Ab}~> (`1 FH) x)
    with ttt => id end |}; I);
  from := ({| transform := fun x =>
    match x return
      ((`1 FH) x
         ~{Ab}~> functor_of_module (module_of_functor (`1 FH) (`2 FH)) x)
    with ttt => id end |}; I)
|}.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
(*
 Both identity components are [fmap] of the source identity, so both
 iso laws are [fmap_id] of the given functor. 

 --------
 两个身份组件都是源身份的 [fmap]，因此两个同构定律都是给定函子的 [fmap_id]。
*)
Next Obligation.
  intros R FH [] m; simpl.
  rewrite (@fmap_id _ _ (`1 FH) ttt m); reflexivity.
Qed.
Next Obligation.
  intros R FH [] m; simpl.
  rewrite (@fmap_id _ _ (`1 FH) ttt m); reflexivity.
Qed.

(** ** Mac Lane's Exercise 1 / ** 马克·莱恩练习 1 *)

(*
 R-Mod IS the full subcategory of [B(R), Ab] on the additive functors.
 [≅[Cat]] is EQUIVALENCE of categories ([Cat]'s hom-setoid is
 [Functor_Setoid]); the orientation is Instance/Rep.v's and
 Instance/Fun/Action.v's, with the functor category on the left. 

 --------
 R-Mod 是 [B(R), Ab] 上加性函子(full subcategory)的完整子范畴。[≅[Cat] 是范畴的等价（[Cat] 的同态集是 [Functor_Setoid]）；取向是 Instance/Rep.v 和 Instance/Fun/Action.v，函子范畴在左侧。
*)
Program Definition RMod_AbFun_equiv (R : RingObject) :
  AbFunAdd R ≅[Cat] RMod R := {|
  to   := AbFunAdd_to R;
  from := AbFunAdd_from R
|}.
Next Obligation.
  (* AbFunAdd_to ◯ AbFunAdd_from ≈ Id, on the module side / 在模块端，AbFunAdd_to ◯ AbFunAdd_from ≈ Id *)
  intros R.
  exists (fun M => AbFunAdd_module_round M).
  intros M N f m; simpl; reflexivity.
Qed.
Next Obligation.
  (* AbFunAdd_from ◯ AbFunAdd_to ≈ Id, on the functor side / 在函子端，AbFunAdd_from ◯ AbFunAdd_to ≈ Id *)
  intros R.
  exists (fun FH => AbFunAdd_functor_round FH).
  intros FH GH η [] m; simpl; reflexivity.
Qed.

(** ** Witnesses / ** 证人 *)

(*
 Every ring is a module over itself (Instance/Mod.v's [Ring_RMod]);
 read across the equivalence it is an object of the additive-functor
 category, and its action computes over ℤ. 

 --------
 每个环都是它自身的模（Instance/Mod.v 的 [Ring_RMod]）；
 通过等价性读取，它是加法函子范畴的一个对象，其作用在 ℤ 上计算。
*)
Definition Ring_AbFun (R : RingObject) : AbFunAdd R :=
  ((functor_of_module (Ring_RMod R);
    functor_of_module_additive (Ring_RMod R)) : AbFunAdd R).

Example int_abfun_act :
  cmon_map (@fmap _ _ (functor_of_module Int_RMod) ttt ttt 3%Z) 4%Z
    = 12%Z := eq_refl.

Example int_abfun_round :
  rm_smul (module_of_functor (functor_of_module Int_RMod)
             (functor_of_module_additive Int_RMod)) 3%Z 4%Z
    = 12%Z := eq_refl.

Example int_abfun_neg :
  cmon_map (@fmap _ _ (functor_of_module Int_RMod) ttt ttt
              (ring_neg Int_Ring 3%Z)) 4%Z = (-12)%Z := eq_refl.

(** ** The subcategory is proper / ** 子类别是正确的 *)

(*
 A functor out of B(R) must preserve MULTIPLICATION and the unit; it
 need not preserve addition.  The cheapest separation: send every ring
 element to the identity.  Multiplicativity is [id ≈ id ∘ id] and
 unitality is [reflexivity], but additivity would make the (constant)
 image of 1 + 1 the sum of two identities, forcing [m ≈ m + m] —
 refuted at [m = 1] in ℤ. 

 --------
 从 B(R) 出发的函子必须保持乘法和单位；它不需要保持加法。最简单的分离方法：将每个环元素映射到单位元。乘法性是 [id ≈ id ∘ id]，单位性是 [reflexivity]，但加法性会使 1 + 1 的（常数）像变成两个单位元的和，从而导致 [m ≈ m + m] —— 在 ℤ 中的 [m = 1] 被反驳。
*)
Program Definition unit_act_functor (R : RingObject) :
  DeloopRig (ring_rig R) ⟶ Ab := {|
  fobj := fun _ => (ring_ab R : Ab);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros R x y r s Hrs m; simpl; reflexivity. Qed.
Next Obligation. intros R x m; simpl; reflexivity. Qed.
Next Obligation. intros R x y z r s m; simpl; reflexivity. Qed.

Lemma unit_act_functor_not_additive :
  IsAdditiveFun Int_Ring (unit_act_functor Int_Ring) → False.
Proof.
  intro H.
  pose proof (@fmap_padd _ _ (DeloopRing_AbEnriched Int_Ring)
                Ab_AbEnriched (unit_act_functor Int_Ring) H
                ttt ttt 1%Z 1%Z 1%Z) as Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(*
 A less degenerate separation, and Mac Lane's own shape of counterpoint:
 over a COMMUTATIVE ring, squaring is multiplicative — (rs)² = r²s² —
 and unital, so [r ↦ (r·r)·(−)] is a genuine functor; but squaring is
 not additive, and at r = s = 1 in ℤ the two sides act as 4 and as 2. 

 --------
 一个不那么退化的分离，以及Mac Lane自己对对位法的形状：
 在交换环上，平方是乘法性的——(rs)² = r²s²——
 并且是幺元的，所以 [r ↦ (r·r)·(−)] 是一个真正的函子；但平方不是加法性的，在 ℤ 中当 r = s = 1 时，两边的结果分别是 4 和 2。
*)
Program Definition square_act (n : Z) :
  (ring_ab Int_Ring : Ab) ~{Ab}~> (ring_ab Int_Ring : Ab) := {|
  cmon_map := {| morphism := fun m => Z.mul (Z.mul n n) m |}
|}.
(*
 [proper_morphism] needs no obligation: ℤ's setoid equivalence is
 Leibniz equality ([Z_eqT]), so elaboration discharges it. 

 --------
 [proper_morphism] 不需要义务：ℤ 的集合等价是 Leibniz 等式（[Z_eqT]），因此阐述可以解决它。
*)
Next Obligation.
  intros n; simpl.
  exact (Z.mul_0_r (Z.mul n n)).
Qed.
Next Obligation.
  intros n a b; simpl.
  exact (Z.mul_add_distr_l (Z.mul n n) a b).
Qed.

Program Definition square_functor :
  DeloopRig (ring_rig Int_Ring) ⟶ Ab := {|
  fobj := fun _ => (ring_ab Int_Ring : Ab);
  fmap := fun _ _ n => square_act n
|}.
(* [fmap_respects] needs no obligation either, for the same reason: the source hom-setoid of [DeloopRig (ring_rig Int_Ring)] is ℤ under Leibniz equality. / [fmap_respects] 也不需要任何义务，原因相同：[DeloopRig (ring_rig Int_Ring)] 的源同态集是 ℤ，使用 Leibniz 等式。 *)
Next Obligation.
  intros x a; simpl.
  change (Z.mul (Z.mul 1 1) a = a).
  ring.
Qed.
Next Obligation.
  intros x y z n m a; simpl.
  change (Z.mul (Z.mul (Z.mul n m) (Z.mul n m)) a
            = Z.mul (Z.mul n n) (Z.mul (Z.mul m m) a)).
  ring.
Qed.

Lemma square_functor_not_additive :
  IsAdditiveFun Int_Ring square_functor → False.
Proof.
  intro H.
  pose proof (@fmap_padd _ _ (DeloopRing_AbEnriched Int_Ring)
                Ab_AbEnriched square_functor H ttt ttt 1%Z 1%Z 1%Z) as Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(*
 Both functors are objects of the ambient functor category and neither
 is an object of the subcategory: the additive predicate genuinely
 cuts, so [AbFunAdd Int_Ring] is a PROPER full subcategory of
 [[B(ℤ), Ab]]. 

 --------
 两个函子都是环境函子范畴的对象，并且都不是子范畴的对象：加法谓词确实进行划分，因此 [AbFunAdd Int_Ring] 是 [[B(ℤ), Ab] 的一个真全子范畴。
*)
Lemma AbFunAdd_proper :
  ((IsAdditiveFun Int_Ring (unit_act_functor Int_Ring) → False)
     * (IsAdditiveFun Int_Ring square_functor → False))%type.
Proof.
  split.
  - exact unit_act_functor_not_additive.
  - exact square_functor_not_additive.
Qed.
