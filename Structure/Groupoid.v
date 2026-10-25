Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.

Generalizable All Variables.

(* * * Groupoids: the property, and the vertex-group structure / * * 群类：性质与顶点群结构 *)

(*
 nLab:      https://ncatlab.org/nlab/show/groupoid
 nLab:      https://ncatlab.org/nlab/show/vertex+group
 Wikipedia: https://en.wikipedia.org/wiki/Groupoid
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §I.5, printed p. 20 (Definition 9 and the remark
 following it)
 Book:      Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
 September 2005), §7.7, printed p. 175
 Book:      Riehl, "Category Theory in Context", Definition 1.1.12 and
 Example 1.1.13(i), printed p. 8
 Book:      Fong, Spivak, "Seven Sketches in Compositionality", CUP 2019,
 §3.2.5 Exercise 3.32, printed pp. 88-89

 A groupoid is a category in which every morphism is invertible.  This file
 supplies the PREDICATE saying so — [IsGroupoid] — and the local structure
 theory that Mac Lane records immediately after the definition: each object
 x of a groupoid carries a vertex group hom(x, x), and any arrow f : x ~> x'
 conjugates hom(x, x) isomorphically onto hom(x', x').

 Until now the name [Groupoid] was bound in-tree to a CONSTRUCTION —
 Construction/Groupoid.v builds the core (maximal subgroupoid) of a
 category — with no property for it to satisfy.  [core_is_groupoid] below
 closes that gap.

 Contents:

 IsGroupoid C            every morphism of C is an isomorphism
 ginv G f                the chosen inverse of f, with its calculus
 core_is_groupoid        the core of any category is a groupoid
 IsGroupoid_op           C^op is a groupoid whenever C is
 MonInverses M           a two-sided inverse operation on a monoid
 deloop_groupoid_iff     M is a group  <->  B M is a groupoid
 vertex_group G x        hom(x, x) as a group
 MonHom, MonIso          monoid homomorphisms and isomorphisms
 conjugation_iso G f     hom(x, x) ≅ hom(x', x') by conjugation
 deloop_nat_not_groupoid B (ℕ, +) is NOT a groupoid
 deloop_bool_groupoid    B (Z/2) is
 Z3_Grp                  Z/3, the smallest group whose inversion map
 is not the identity function

 The connectedness predicate and the structure theorem it feeds — a
 connected groupoid is equivalent to the delooping of any one of its vertex
 groups — are in Structure/Groupoid/Connected.v; the inversion isomorphism
 C ≅ C^op is in Structure/Groupoid/Inversion.v. 

 --------
 nLab：       https://ncatlab.org/nlab/show/groupoid
 nLab：       https://ncatlab.org/nlab/show/vertex+group
 Wikipedia：  https://en.wikipedia.org/wiki/Groupoid
 书籍：      Mac Lane，《为工作数学家而写的范畴论》，第2版，GTM 5，第I.5节，印刷第20页（定义9及其后的备注）
 书籍：      Awodey，《范畴论》，第1版（卡内基梅隆预印本，2005年9月），第7.7节，印刷第175页
 书籍：      Riehl，《语境中的范畴论》，定义1.1.12及例子1.1.13(i)，印刷第8页
 书籍：      Fong, Spivak，《组合性中的七个草图》，CUP 2019，第3.2.5节练习3.32，印刷第88-89页群组是一种范畴，其中每个态射都是可逆的。 这个文件提供了说明这一点的谓词 — [IsGroupoid] — 以及 Mac Lane 在定义之后立即记录的局部结构理论：群组的每个对象 x 都具有一个顶点群 hom(x, x)，并且任何箭头 f : x ~> x' 都会将 hom(x, x) 同构地共轭到 hom(x', x')。

 直到现在，名称 [Groupoid] 在树中被绑定到一个构造 — Construction/Groupoid.v 构建了一个范畴的核心（最大子群组） — 并没有要求它满足任何性质。下面的 [core_is_groupoid] 弥补了这个空缺。

 目录:IsGroupoid C            C 的每个态射都是同构
 ginv G f                f 的选定逆元及其计算方法
 core_is_groupoid        任意范畴的核心是一个群族
 IsGroupoid_op           若 C 是群族，则 C^op 也是群族
 MonInverses M           幺半群上的双侧逆操作
 deloop_groupoid_iff     M 是群 <-> B M 是群族
 vertex_group G x        将 hom(x, x) 视为一个群
 MonHom, MonIso          幺半群同态与同构
 conjugation_iso G f     通过共轭将 hom(x, x) ≅ hom(x', x')
 deloop_nat_not_groupoid B (ℕ, +) 不是群族
 deloop_bool_groupoid    B (Z/2) 是群族
 Z3_Grp                  Z/3，是最小的逆映射不是恒等函数的群连通性谓词及其依赖的结构定理 — 连通群oid等价于其任意一个顶点群的去循环 — 在 Structure/Groupoid/Connected.v 中；反演同构 C ≅ C^op 在 Structure/Groupoid/Inversion.v 中。
*)

(*
 Why the vertex group, and what connectedness adds

 nLab:  https://ncatlab.org/nlab/show/groupoid
 nLab:  https://ncatlab.org/nlab/show/fundamental+groupoid
 Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of the
 London Mathematical Society 19, 1987
 Paper: Weinstein, "Groupoids: Unifying Internal and External Symmetry",
 Notices of the American Mathematical Society 43, 1996

 The history of groupoids — Brandt's 1926/27 paper, Ehresmann's
 differentiable groupoids, Brown's van Kampen theorem, the groupoid model
 of intensional type theory — is told in the essay heading
 Construction/Groupoid.v, and is not repeated here.  What this file adds is
 the ANATOMY: what a groupoid is made of once one knows every arrow
 inverts.

 Mac Lane's §I.5 gives the answer in two sentences.  The endomorphisms at a
 single object form a group, the vertex group (also written Aut(x), or
 π₁(X, x) when the groupoid is a fundamental groupoid); and an arrow
 f : x ~> x' does not merely connect two objects but identifies their vertex
 groups, by a ↦ f ∘ a ∘ f⁻¹.  Both halves are below: [vertex_group] and
 [conjugation_iso].  The conjugation is not canonical — a different arrow
 x ~> x' generally induces a different isomorphism, differing by an inner
 automorphism — which is exactly why the fundamental group of a
 path-connected space is well defined only up to inner automorphism unless
 a base point is chosen, and why Brown's base-point-free fundamental
 groupoid is the more robust invariant (Brown 1987).  The library records
 the dependence honestly: [conjugation_iso] takes the arrow f as an
 argument, and nothing claims the result is independent of it.

 The vertex group does not, by itself, determine the groupoid: a groupoid
 with two objects and no arrow between them has two vertex groups, and is
 not equivalent to the delooping of the one at either object.  That is
 [Two_Discrete_no_deloop_equivalence] in Structure/Groupoid/Connected.v,
 stated there at the object TwoDX; the argument it uses,
 [deloop_equiv_connected], quantifies over the object, so the other case
 costs nothing.  Connectedness is precisely the hypothesis that repairs
 this, and it is the subject of that file.

 Weinstein's survey supplies the reason the extra generality earns its keep:
 many objects display symmetry while having few or no nontrivial
 automorphisms, and the symmetry lives in the arrows BETWEEN objects rather
 than at any one of them (Weinstein 1996).  A group is the degenerate case
 in which there is only one object to move between — the reading this file
 makes precise as [deloop_groupoid_iff] and [vertex_group], the two halves
 of the dictionary between groups and one-object groupoids. 

 --------
 为什么是顶点群，以及连通性带来了什么

 nLab:   https://ncatlab.org/nlab/show/groupoid 
 nLab:   https://ncatlab.org/nlab/show/fundamental+groupoid 
 论文: Brown, 《从群到群范畴：简要综述》，伦敦数学学会公报 19, 1987
 论文: Weinstein, 《群范畴：统一内部和外部对称性》，美国数学学会通告 43, 1996

 群范畴的历史——Brandt 的 1926/27 年论文、Ehresmann 的可微群范畴、Brown 的 van Kampen 定理、强度类型理论的群范畴模型——在标题为 Construction/Groupoid.v 的文章中已有阐述，这里不再重复。该文件增加的是结构解析：一旦知道每条箭头都有逆，一个群范畴由什么组成。Mac Lane 的 §I.5 用两句话给出了答案。在单个对象处的自同态形成一个群，即顶点群（也写作 Aut(x)，或者当群oid是基本群oid时写作 π₁(X, x)）；而箭头 f : x ~> x' 不仅仅连接两个对象，它通过 a ↦ f ∘ a ∘ f⁻¹ 来识别它们的顶点群。两部分如下：[vertex_group] 和 [conjugation_iso]。共轭不是典范的——不同的箭头 x ~> x' 通常会引入不同的同构，这个同构相差一个内自同构——这正是为什么路径连通空间的基本群只有在选择基点时才能确定到内自同构的原因，也是为什么 Brown 的无基点基本群oid 是更稳健的不变量（Brown 1987）。图书馆如实记录了依赖关系：[conjugation_iso] 以箭头 f 作为参数，并且没有任何说明结果与它无关。

 顶点群本身并不能确定群体：一个有两个对象且它们之间没有箭头的群体有两个顶点群，并且它不等价于任一对象的单环化。这在 Structure/Groupoid/Connected.v 中的 [Two_Discrete_no_deloop_equivalence] 有说明，在对象 TwoDX 处陈述；它使用的参数 [deloop_equiv_connected] 对对象进行了量化，所以另一种情况不需要额外代价。连通性正是修正这一点的假设，并且它是该文件的主题。温斯坦的综述提供了额外一般性物有所值的原因：许多对象展示出对称性，但几乎没有或根本没有非平凡自同构，而这种对称性存在于对象之间的箭头中，而不是存在于某个特定对象上（Weinstein 1996）。群是一个退化情况，在这种情况下只有一个对象可供移动——读取此文件可精确表示为 [deloop_groupoid_iff] 和 [vertex_group]，它们是群与单对象群的字典的两个部分。
*)

(** ** The predicate / ** 谓语 *)

(*
 A groupoid is a category in which every morphism has a two-sided inverse.
 This is Mac Lane §I.5 Definition 9, Awodey §7.7, and Riehl Definition
 1.1.12, all three verbatim; the donor is Theory/Isomorphism.v's
 [IsIsomorphism], the single-morphism (predicate) reading of `≅`.

 [IsGroupoid] is a plain [Definition], deliberately NOT a [Class] and NOT
 registered for instance resolution: an inhabitant carries a CHOSEN inverse
 for each arrow, in the same way that Theory/Equivalence.v's
 [EquivalenceOfCategories] carries a chosen quasi-inverse, and the same rule
 applies — such a choice is passed explicitly at use sites rather than
 conjured by a proof search.  The choice is nevertheless immaterial:
 [ginv_choice_irrelevant] below shows any two inhabitants give the same
 inverse up to `≈`. 

 --------
 群范畴是一个范畴，其中每一个态射都有一个双边逆.
 这是 Mac Lane §I.5 定义 9，Awodey §7.7，以及 Riehl 定义 1.1.12，三者均逐字相同；来源是 Theory/Isomorphism.v 的 [IsIsomorphism]，即 `≅` 的单态射（谓词）读取方式。

 [IsGroupoid] 是一个普通的 [Definition]，故意不是 [Class]，也没有注册用于实例解析：每个元素携带每个箭头的一个选定逆，就像 Theory/Equivalence.v 的 [EquivalenceOfCategories] 携带一个选定的准逆一样，并且同样规则适用——这种选择在使用时显式传递，而不是通过证明搜索产生。然而，这种选择并不影响结果：下面的 [ginv_choice_irrelevant] 显示任何两个元素给出的逆都是相同的，至 `≈` 为止。
*)
Definition IsGroupoid (C : Category) : Type :=
  ∀ (x y : C) (f : x ~> y), IsIsomorphism f.

Section Groupoid.

Context {C : Category}.
Context (G : IsGroupoid C).

(* The inverse of f, extracted from the groupoid structure. / 从群元结构中提取的 f 的逆。 *)
Definition ginv {x y : C} (f : x ~> y) : y ~> x :=
  two_sided_inverse (IsIsomorphism := G x y f).

(* The two inverse laws, in the orientation [IsIsomorphism] states them. / 两个逆定律，在方向 [IsIsomorphism] 中陈述它们。 *)
Lemma ginv_right {x y : C} (f : x ~> y) : f ∘ ginv f ≈ id.
Proof. exact (is_right_inverse (IsIsomorphism := G x y f)). Qed.

Lemma ginv_left {x y : C} (f : x ~> y) : ginv f ∘ f ≈ id.
Proof. exact (is_left_inverse (IsIsomorphism := G x y f)). Qed.

(*
 Any right inverse of f is THE inverse of f, and likewise any left inverse:
 both are Theory/Isomorphism.v's [comp_inverse_unique] (its Eilenberg-Mac
 Lane Lemma 1.4) read at the chosen inverse.  These two lemmas are the
 workhorses of everything below — every identity about [ginv] is proved by
 exhibiting a one-sided inverse rather than by unfolding the choice. 

 --------
 f 的任何右逆都是 f 的逆，同样地，任何左逆也是如此：两者都是 Theory/Isomorphism.v 的 [comp_inverse_unique]（其 Eilenberg-Mac Lane 引理 1.4），在所选逆元处读取。这两个引理是下面所有内容的主力——关于 [ginv] 的每个恒等式都是通过展示一个单边逆元来证明的，而不是通过展开选择。
*)
Lemma ginv_unique_r {x y : C} (f : x ~> y) (g : y ~> x) :
  f ∘ g ≈ id → ginv f ≈ g.
Proof.
  intro H.
  symmetry.
  exact (comp_inverse_unique f g (ginv f) H (ginv_left f)).
Qed.

Lemma ginv_unique_l {x y : C} (f : x ~> y) (g : y ~> x) :
  g ∘ f ≈ id → ginv f ≈ g.
Proof.
  intro H.
  exact (comp_inverse_unique f (ginv f) g (ginv_right f) H).
Qed.

(*
 Inversion respects `≈`.  Like [grp_inv_respects] in Construction/Deloop.v
 this is derived from uniqueness of inverses, not required as data. 

 --------
 逆运算遵循 `≈`。就像 Construction/Deloop.v 中的 [grp_inv_respects] 一样，这源自逆元的唯一性，并非作为数据所必需。
*)
#[export] Instance ginv_respects {x y : C} :
  Proper (equiv ==> equiv) (@ginv x y).
Proof.
  intros f g Hfg.
  apply ginv_unique_r.
  rewrite Hfg.
  apply ginv_right.
Qed.

Lemma ginv_involutive {x y : C} (f : x ~> y) : ginv (ginv f) ≈ f.
Proof. apply ginv_unique_l, ginv_right. Qed.

Lemma ginv_id {x : C} : ginv (id[x]) ≈ id.
Proof. apply ginv_unique_r; cat. Qed.

(* Inverses of a composite compose in the opposite order. / 复合的逆按相反的顺序组合。 *)
Lemma ginv_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
  ginv (f ∘ g) ≈ ginv g ∘ ginv f.
Proof.
  apply ginv_unique_r.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g).
  rewrite ginv_right, id_left.
  apply ginv_right.
Qed.

(*
 An arrow of a groupoid, packaged as an object-level isomorphism.  This is
 the bridge from the predicate reading back to `≅`. 

 --------
 一个群元的箭头，被封装为对象级同构。这是从谓词阅读回到 `≅` 的桥梁。
*)
Definition giso {x y : C} (f : x ~> y) : x ≅ y := IsIsoToIso f (G x y f).

(*
 Moving an inverse across an equation, the two cancellation rules a
 groupoid computation needs: from g ∘ f ≈ h one reads off g ≈ h ∘ f⁻¹ and
 f ≈ g⁻¹ ∘ h.  Each is one rewrite by [ginv_right] or [ginv_left] after
 substituting h. 

 --------
 在方程中移动逆元素，需要一个群元计算的两个消去规则：从 g ∘ f ≈ h 可以得出 g ≈ h ∘ f⁻¹ 和 f ≈ g⁻¹ ∘ h。每一个都是在代入 h 后通过 [ginv_right] 或 [ginv_left] 的一次重写。
*)
Lemma ginv_move_r {x y z : C} (f : x ~> y) (g : y ~> z) (h : x ~> z) :
  g ∘ f ≈ h → g ≈ h ∘ ginv f.
Proof.
  intro H.
  rewrite <- H, <- comp_assoc, ginv_right.
  now rewrite id_right.
Qed.

Lemma ginv_move_l {x y z : C} (f : x ~> y) (g : y ~> z) (h : x ~> z) :
  g ∘ f ≈ h → f ≈ ginv g ∘ h.
Proof.
  intro H.
  rewrite <- H, comp_assoc, ginv_left.
  now rewrite id_left.
Qed.

End Groupoid.

Arguments ginv {C} G {x y} f.

(*
 The groupoid structure is a choice of inverses, but not a choice that
 matters: any two inhabitants of [IsGroupoid C] name the same inverse up to
 `≈`.  (This is why nothing downstream needs to fix one, and why it is safe
 for [conjugation_iso] and the structure theorem to take the structure as an
 argument.) 

 --------
 群oid结构是逆元的一个选择，但这并不是一个重要的选择：[IsGroupoid C] 的任意两个元素在 `≈` 意义下都表示相同的逆元。（这就是为什么下游不需要固定某个逆元，以及为什么 [conjugation_iso] 和结构定理可以将该结构作为一个参数是安全的。）
*)
Lemma ginv_choice_irrelevant {C : Category} (G G' : IsGroupoid C)
  {x y : C} (f : x ~> y) : ginv G f ≈ ginv G' f.
Proof. apply ginv_unique_r, ginv_right. Qed.

(* * ** The core of a category is a groupoid / * ** 一个范畴的核心是一个群族 *)

(*
 Awodey §7.7 asks for the lemma that every arrow of [Groupoid C] — the core
 construction of Construction/Groupoid.v, whose arrows ARE the
 isomorphisms of C — is invertible.  Its inverse is Theory/Isomorphism.v's
 [iso_sym], and the two laws are that file's [iso_sym_right_inverse] and
 [iso_sym_left_inverse].  Construction/Groupoid.v names [iso_sym] in its
 header as the source of the inverses that make its core "a groupoid rather
 than merely a category", but the file itself is 109 lines containing only
 that header and the [Program Definition], and states no invertibility
 lemma; this is that lemma.

 NOT VACUOUS: [Groupoid C] is inhabited for every C, and its arrows x ~> y
 are the isomorphisms of C, of which there is at least one (the identity)
 at every object; so this asserts something about a nonempty family of
 arrows even when C has no nonidentity isomorphism. 

 --------
 Awodey §7.7 要求的引理是每一个 [Groupoid C] 的箭头——Construction/Groupoid.v 的核心构造，其箭头是 C 的同构——都是可逆的。它的逆是 Theory/Isomorphism.v 的 [iso_sym]，而两个定律是该文件的 [iso_sym_right_inverse] 和 [iso_sym_left_inverse]。Construction/Groupoid.v 在其头部将 [iso_sym] 命名为产生其核心的逆元来源，使其成为“一个群而不仅仅是一个范畴”，但该文件本身有 109 行，只包含该头部和 [Program Definition]，并未陈述任何可逆性引理；这就是那个引理。非空洞：[Groupoid C] 对每个 C 都是有对象的，并且它的箭头 x ~> y 是 C 的同构，每个对象至少有一个同构（恒等同构）；因此，即使 C 没有非恒等同构，这也说明了一族非空的箭头。
*)
Definition core_is_groupoid (C : Category) : IsGroupoid (Groupoid C).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (Groupoid C) x y f (iso_sym f) _ _).
  - apply iso_sym_right_inverse.
  - apply iso_sym_left_inverse.
Defined.

(** ** Duality *)

(*
 The opposite of a groupoid is a groupoid: an arrow of C^op is an arrow of
 C read backwards, and its inverse is the same arrow of C read backwards,
 so the two inverse laws simply exchange places.  This is the fact
 Structure/Groupoid/Inversion.v needs to build the functor C^op ⟶ C. 

 --------
 群族的对偶是群族：C^op 的一个箭头是 C 的一个箭头倒着读，而它的逆就是 C 的同一个箭头倒着读，因此两个逆律只是交换了位置。这就是 Structure/Groupoid/Inversion.v 需要构建函子 C^op ⟶ C 的事实。
*)
Definition IsGroupoid_op {C : Category} (G : IsGroupoid C) : IsGroupoid (C^op).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (C^op) x y f (ginv G f) _ _).
  - exact (ginv_left G f).
  - exact (ginv_right G f).
Defined.

(*
 The chosen inverse in C^op is the chosen inverse in C, on the nose: the
 construction moves no data, exactly as [op]/[unop] move none
 (Construction/Opposite.v).  The [=] here is genuinely stronger than `≈` —
 it says the two terms are the same term, not merely equivalent arrows —
 and it holds by [eq_refl]. 

 --------
 在 C^op 中选定的逆元就是在 C 中选定的逆元，完全一致：这个构造不移动任何数据，就像 [op] / [unop] 一样不移动任何数据（Construction/Opposite.v）。这里的 [=] 确实比 `≈` 更强——它说两个项是同一个项，而不仅仅是等价的箭头——并且它由 [eq_refl] 成立。
*)
Example ginv_op_eq {C : Category} (G : IsGroupoid C) {x y : C}
  (f : y ~{C}~> x) : ginv (IsGroupoid_op G) f = ginv G f := eq_refl.

(* * ** Groups as one-object groupoids / * ** 作为单对象范畴的群 *)

(*
 Fong and Spivak's Exercise 3.32 asks the reader to decide, of two given
 monoids, whether the delooping is a groupoid.  Stating the exercise needs
 the notion "M is a group" separated from the bundling [GrpObject] of
 Construction/Deloop.v, since the question is about a MONOID that is given
 in advance.  [MonInverses M] is that separation: the inverse operation and
 its two laws, over a fixed monoid.

 As in [GrpObject] no [Proper] field is carried: respectfulness of [minv]
 follows from [mon_inverse_unique] (Construction/Deloop.v) exactly as
 [grp_inv_respects] does there, and is reachable through [GrpObject_of]
 below without restating the argument. 

 --------
 Fong 和 Spivak 的练习 3.32 要求读者判断，在给出的两个幺半群中，解环是否为一个群系。陈述该练习需要将“M 是一个群”的概念从 Construction/Deloop.v 的 [GrpObject] 捆绑中分离出来，因为问题是关于一个事先给定的幺半群。[MonInverses M] 就是这种分离：逆运算及其两个律，在一个固定的幺半群上。

 如同 [GrpObject] 中没有携带 [Proper] 域一样：[minv] 的尊重性来自 [mon_inverse_unique]（Construction/Deloop.v），完全像 [grp_inv_respects] 在那里一样，可以通过下面的 [GrpObject_of] 达成而无需重述论证。
*)
Record MonInverses (M : MonObject) := {
  minv : carrier M → carrier M;

  minv_l : ∀ a, mon_op (minv a) a ≈ mon_unit;
  minv_r : ∀ a, mon_op a (minv a) ≈ mon_unit
}.

Arguments minv {M} _ _.
Arguments minv_l {M} _ _.
Arguments minv_r {M} _ _.

(*
 [MonInverses M] and "M is the underlying monoid of a [GrpObject]" are the
 same data, repackaged; both round trips hold. 

 --------
 [MonInverses M] 和 “M 是 [GrpObject] 的基础幺半群” 是相同的数据，只是重新打包；两个往返转换都成立。
*)
Definition GrpObject_of {M : MonObject} (I : MonInverses M) : GrpObject := {|
  grp_monoid := M;
  grp_inv    := minv I;
  grp_inv_l  := minv_l I;
  grp_inv_r  := minv_r I
|}.

Definition MonInverses_of (G : GrpObject) : MonInverses (grp_monoid G) := {|
  minv   := grp_inv (g:=G);
  minv_l := grp_inv_l (g:=G);
  minv_r := grp_inv_r (g:=G)
|}.

(*
 Both round trips hold on the nose, by [eq_refl]: no field is rebuilt, only
 moved.  These [=]s are stronger than any `≈` statement — they are
 equalities of whole records — and they are what justifies treating the two
 packagings as the same data rather than as two notions. 

 --------
 两个往返都保持在鼻子上，由 [eq_refl]：没有字段被重建，只是被移动。这些 [=] 比任何 `≈` 语句都更强——它们是整个记录的等式——它们正是将这两种打包方式视为相同数据而不是两种概念的依据。
*)
Example GrpObject_of_MonInverses_of (G : GrpObject) :
  GrpObject_of (MonInverses_of G) = G := eq_refl.

Example MonInverses_of_GrpObject_of (M : MonObject) (I : MonInverses M) :
  MonInverses_of (GrpObject_of I) = I := eq_refl.

(*
 One direction of Exercise 3.32, which is Mac Lane's §I.2 construction 4:
 the delooping of a group is a groupoid.  Construction/Deloop.v already
 proves every arrow of [Deloop G] invertible; this is that instance read as
 the predicate. 

 --------
 练习 3.32 的一个方向，即 Mac Lane §I.2 构造 4：一个群的解环是一个群oids。Construction/Deloop.v 已经证明了 [Deloop G] 的每个箭头都是可逆的；这是作为谓词读取的那个实例。
*)
Definition Deloop_IsGroupoid (G : GrpObject) : IsGroupoid (Deloop G) :=
  fun x y f => Deloop_group_invertible G x y f.

(*
 The converse, which is what makes Exercise 3.32 a CHARACTERISATION rather
 than one implication: if every arrow of B M is invertible then M has
 inverses.  There is only one object, so an [IsIsomorphism] at it is
 literally an inverse element, and the two laws of [IsIsomorphism] are the
 two group laws with composition read as multiplication. 

 --------
 相反的情况，正是使练习 3.32 成为一个特征描述而不仅仅是一个蕴含的原因：如果 B M 的每一条箭头都是可逆的，那么 M 就有逆。这里只有一个对象，所以它的一个 [IsIsomorphism] 字面上就是一个逆元，而 [IsIsomorphism] 的两个定律就是两个群定律，其中复合操作被视为乘法。
*)
Definition Deloop_MonInverses (M : MonObject) (H : IsGroupoid (Deloop M)) :
  MonInverses M := {|
  minv   := fun a => two_sided_inverse (IsIsomorphism := H ttt ttt a);
  minv_l := fun a => is_left_inverse  (IsIsomorphism := H ttt ttt a);
  minv_r := fun a => is_right_inverse (IsIsomorphism := H ttt ttt a)
|}.

(*
 Fong and Spivak, §3.2.5 Exercise 3.32, as a biconditional: a monoid is a
 group exactly when its delooping is a groupoid.  Both directions are data
 (an inverse operation one way, a family of inverse arrows the other), so
 the statement uses Lib/Foundation.v's Type-valued `↔` ([iffT]) rather than
 propositional [iff]. 

 --------
 Fong 和 Spivak，§3.2.5 练习 3.32，作为一个双条件语句：当且仅当它的去环是一个群族时，一个幺半群是一个群。两个方向都是数据（一个方向是逆运算，另一个方向是一族逆箭头），所以该声明使用 Lib/Foundation.v 的类型值 `↔`（[iffT]），而不是命题性 [iff]。
*)
Theorem deloop_groupoid_iff (M : MonObject) :
  MonInverses M ↔ IsGroupoid (Deloop M).
Proof.
  split.
  - intro I.
    exact (Deloop_IsGroupoid (GrpObject_of I)).
  - intro H.
    exact (Deloop_MonInverses M H).
Defined.

(*
 The delooping really does have exactly one object: [poly_unit], whose sole
 inhabitant is [ttt].  Together with [deloop_groupoid_iff] this is one half
 of "groups are one-object groupoids" — a group gives a groupoid with one
 object, and a one-object category is a groupoid exactly when its monoid is
 a group.  The other half is [vertex_group] below, which reads a group off
 any object of any groupoid.  (The [=] is an equality of TYPES, stronger
 than any statement about morphisms, and holds by [eq_refl].) 

 --------
 去环化确实只有一个对象：[poly_unit]，其唯一的元素是[ttt]。与[deloop_groupoid_iff]一起，这构成了“群是一类单对象群范畴”的一半——一个群给出一个具有一个对象的群范畴，而一个单对象范畴只有当它的幺半群是群时才是群范畴。另一半是下面的[vertex_group]，它从任意群范畴的任意对象中读取一个群。（[=]是类型的等式，比关于态射的任何陈述都强，并且由[eq_refl]成立。）
*)
Example Deloop_one_object (M : MonObject) : obj[Deloop M] = poly_unit := eq_refl.

(** ** The vertex group / ** 顶点组 *)

(*
 Mac Lane §I.5: in a groupoid the endomorphism monoid at an object is a
 group.  Construction/Deloop.v's [hom_monoid C x] already exhibits
 hom(x, x) as a monoid in ANY category; a groupoid structure supplies the
 inverses, and the two group laws are [ginv_left] and [ginv_right]
 verbatim.

 This is the converse half of the group/one-object-groupoid dictionary
 asked for by Awodey §7.7 and by Riehl's footnote to Example 1.1.13(i):
 [Deloop_IsGroupoid] turns a group into a one-object groupoid, and
 [vertex_group] reads a group off any object of any groupoid. 

 --------
 Mac Lane §I.5：在一个群范畴中，一个对象的自同态单元是一个群。Construction/Deloop.v 的 [hom_monoid C x] 已经将 hom(x, x) 展示为任意范畴中的一个单元；群范畴结构提供了逆元素，而两个群定律分别是 [ginv_left] 和 [ginv_right] 原样适用。

 这是 Awodey §7.7 和 Riehl 对示例 1.1.13(i) 的脚注所要求的群/单对象群范畴字典的逆半部分：[Deloop_IsGroupoid] 将一个群变为一个单对象群范畴，而 [vertex_group] 可以从任何群范畴的任意对象读出一个群。
*)
Definition vertex_group {C : Category} (G : IsGroupoid C) (x : C) : GrpObject := {|
  grp_monoid := hom_monoid C x;
  grp_inv    := fun f => ginv G f;
  grp_inv_l  := fun f => ginv_left G f;
  grp_inv_r  := fun f => ginv_right G f
|}.

(*
 The two constructions are mutually inverse on data, in the direction where
 that can be said as an equation.  Construction/Deloop.v's
 [hom_monoid_Deloop] already gives the monoid half by [eq_refl]; the
 inverse operation matches on the nose as well, because
 [Deloop_group_invertible] takes [grp_inv] for its [two_sided_inverse]
 field.  The whole records are NOT equal: the law fields of
 [vertex_group ... ] are the opaque obligation proofs of
 [Deloop_group_invertible], not the law fields of G, and [GrpObject] carries
 no proof irrelevance — the same distinction Construction/Deloop/Opposite.v draws for
 [MonObject_op].  Each [=] below is therefore an equality of a DATA field,
 which is strictly stronger than `≈` on that field and is what [eq_refl]
 can supply. 

 --------
 这两个构造在数据上是互逆的，在可以用等式表示的方向上。Construction/Deloop.v 的 [hom_monoid_Deloop] 已经通过 [eq_refl] 给出了单子的一半；逆操作也完全匹配，因为 [Deloop_group_invertible] 将 [grp_inv] 作为其 [two_sided_inverse] 字段。整个记录并不相等：[vertex_group ... ] 的定律字段是 [Deloop_group_invertible] 的不透明义务证明，而不是 G 的定律字段，并且 [GrpObject] 不包含任何证明无关性——Construction/Deloop/Opposite.v 对 [MonObject_op] 也做了同样的区分。因此，下述每个 [=] 都是对数据字段的等式，这比该字段上的 `≈` 更严格，也是 [eq_refl] 可以提供的。
*)
Example vertex_group_Deloop_monoid (G : GrpObject) :
  grp_monoid (vertex_group (Deloop_IsGroupoid G) ttt) = grp_monoid G := eq_refl.

Example vertex_group_Deloop_inv (G : GrpObject) :
  @grp_inv (vertex_group (Deloop_IsGroupoid G) ttt) = @grp_inv G := eq_refl.

(* * ** Monoid homomorphisms, and conjugation / * ** 幺半群同态与共轭 *)

(*
 To say that conjugation is a group ISOMORPHISM one needs homomorphisms of
 the [MonObject]s of Construction/Deloop.v, which that file does not define
 (its stated scope stops before the functor-level dictionary).  The two
 records below are the minimum needed.  A homomorphism of GROUPS is not a
 separate notion: [MonHom_grp_inv] shows a monoid homomorphism between
 groups automatically preserves inverses, so [MonIso] between the
 underlying monoids of two groups is exactly a group isomorphism. 

 --------
 要说共轭是一个群同构，需要 Construction/Deloop.v 中的 [MonObject] 的同态，但该文件没有定义它（其声明的范围停在函子级字典之前）。下面的两个记录是最少需要的。群的同态并不是一个独立的概念：[MonHom_grp_inv] 显示群之间的幺半群同态自动保持逆元，因此 [MonIso] 在两个群的底层幺半群之间正好就是群同构。
*)
Record MonHom (M N : MonObject) := {
  mon_map :> carrier M → carrier N;

  mon_map_respects : Proper (equiv ==> equiv) mon_map;

  mon_map_unit : mon_map mon_unit ≈ mon_unit;
  mon_map_op : ∀ a b, mon_map (mon_op a b) ≈ mon_op (mon_map a) (mon_map b)
}.

Arguments mon_map {M N} _ _.
Arguments mon_map_respects {M N} _.
Arguments mon_map_unit {M N} _.
Arguments mon_map_op {M N} _ _ _.

#[export] Existing Instance mon_map_respects.

Record MonIso (M N : MonObject) := {
  moniso_to : MonHom M N;
  moniso_from : MonHom N M;

  moniso_to_from : ∀ b, moniso_to (moniso_from b) ≈ b;
  moniso_from_to : ∀ a, moniso_from (moniso_to a) ≈ a
}.

Arguments moniso_to {M N} _.
Arguments moniso_from {M N} _.
Arguments moniso_to_from {M N} _ _.
Arguments moniso_from_to {M N} _ _.

(*
 A monoid homomorphism between groups preserves inverses: φ(a⁻¹) is a left
 inverse of φ(a), and [mon_inverse_unique] identifies it with φ(a)⁻¹.  This
 is the classical argument, and it is the reason the file defines no
 separate class of group homomorphisms. 

 --------
 群之间的幺半群同态保持逆元：φ(a⁻¹) 是 φ(a) 的左逆元，而 [mon_inverse_unique] 将其与 φ(a)⁻¹ 认同。这是经典的论证，也是该文件没有定义单独的群同态类的原因。
*)
Lemma MonHom_grp_inv (G H : GrpObject) (φ : MonHom G H) (a : carrier G) :
  φ (grp_inv a) ≈ grp_inv (φ a).
Proof.
  apply (mon_inverse_unique H (φ a) (φ (grp_inv a)) (grp_inv (φ a))).
  - rewrite <- mon_map_op.
    rewrite grp_inv_l.
    apply mon_map_unit.
  - apply grp_inv_r.
Qed.

Section Conjugation.

Context {C : Category}.
Context (G : IsGroupoid C).
Context {x x' : C}.
Context (f : x ~> x').

(* Conjugation by f, as a map hom(x, x) → hom(x', x'). / 通过 f 的共轭，作为一个映射 hom(x, x) → hom(x', x')。 *)
Definition conjugate (a : x ~> x) : x' ~> x' := f ∘ a ∘ ginv G f.

#[local] Instance conjugate_respects : Proper (equiv ==> equiv) conjugate.
Proof. proper; unfold conjugate; now rewrites. Qed.

Lemma conjugate_id : conjugate id ≈ id.
Proof.
  unfold conjugate.
  rewrite id_right.
  apply ginv_right.
Qed.

Lemma conjugate_comp (a b : x ~> x) :
  conjugate (a ∘ b) ≈ conjugate a ∘ conjugate b.
Proof.
  unfold conjugate.
  rewrite <- !comp_assoc.
  (* on the right-hand side the inner f⁻¹ ∘ f cancels / 在右侧，内层 f⁻¹ ∘ f 抵消了 *)
  rewrite (comp_assoc (ginv G f) f).
  rewrite ginv_left, id_left.
  reflexivity.
Qed.

(*
 Built with the constructor applied to explicit monoid arguments rather than
 through record syntax: the field type [carrier (mon_setoid ?M)] does not
 determine ?M from [conjugate]'s type by unification alone. 

 --------
 使用构造函数作用于显式的幺半群参数构建，而不是通过记录语法：字段类型 [carrier (mon_setoid ?M)] 并不能仅通过统一来从 [conjugate] 的类型确定 ?M。
*)
Definition conjugation : MonHom (vertex_group G x) (vertex_group G x') :=
  @Build_MonHom (grp_monoid (vertex_group G x)) (grp_monoid (vertex_group G x'))
    conjugate conjugate_respects conjugate_id conjugate_comp.

End Conjugation.

Arguments conjugate {C} G {x x'} f a.
Arguments conjugation {C} G {x x'} f.

(*
 Mac Lane §I.5: conjugation by an arrow f : x ~> x' is an ISOMORPHISM of
 vertex groups, inverted by conjugation by f⁻¹.  Both round trips are the
 same three-line cancellation.

 The isomorphism depends on f: a different arrow x ~> x' gives a
 conjugation differing by an inner automorphism, and nothing here claims
 otherwise.  That dependence is the categorical form of the base-point
 dependence of the fundamental group.

 VACUITY, stated correctly at the second attempt.  With f := id the
 statement degenerates to the identity automorphism of hom(x, x).  The
 first version of this note then claimed the content lies in the case of
 two DISTINCT objects, and pointed at [Bool_Wide_conjugation] as the
 witness.  An audit refuted both halves.

 The dividing line is ABELIAN versus NONABELIAN, not same-object versus
 distinct-object: conjugation by a non-central endomorphism f : x ~> x is
 already a nontrivial inner automorphism, while conjugation in an abelian
 vertex group is the identity however distinct the objects are.  And
 [Bool_Wide_conjugation] is exactly that degenerate case — its vertex
 group is Z/2, so its underlying map is provably the identity; it
 witnesses the two-object TYPING and nothing more.

 The honest witness is [S3_conjugation_not_identity] at the end of this
 file, over the symmetric group on three letters, which this work adds
 because the tree previously contained no nonabelian group at all — so no
 non-identity conjugation was expressible anywhere. 

 --------
 Mac Lane §I.5：由箭头 f : x ~> x' 引起的共轭是顶点群的同构，其逆是由 f⁻¹ 的共轭。两个往返的过程都是相同的三行消去。

 该同构依赖于 f：不同的箭头 x ~> x' 会产生不同的共轭，只相差一个内自同构，这里没有声明其他情况。该依赖就是基本群基点依赖的范畴形式。

 空性，在第二次尝试时正确表述。取 f := id，该陈述退化为 hom(x, x) 的恒等自同构。该注释的第一个版本声称内容在于两个不同对象的情况，并指向 [Bool_Wide_conjugation] 作为证明。审计否定了这两个部分。分界线是阿贝尔（ABELIAN）与非阿贝尔（NONABELIAN），而不是相同对象与不同对象：通过非中心自同态 f : x ~> x 的共轭已经是一个非平凡的内自同构，而在阿贝尔顶点群中的共轭则是恒等映射，无论对象多么不同。而 [Bool_Wide_conjugation] 正是那个退化的例子——它的顶点群是 Z/2，所以其底层映射可证明是恒等映射；它只见证了双对象类型（TYPING），没有其他。  

 真正的见证是本文件末尾的 [S3_conjugation_not_identity]，它作用在三元对称群上，本工作加入了它，因为之前的树中根本没有非阿贝尔群——因此在任何地方都无法表达非恒等共轭。
*)
Definition conjugation_iso {C : Category} (G : IsGroupoid C) {x x' : C}
  (f : x ~> x') : MonIso (vertex_group G x) (vertex_group G x').
Proof.
  refine {| moniso_to   := conjugation G f
          ; moniso_from := conjugation G (ginv G f) |}.
  - (* conjugation by f, after conjugation by f⁻¹ / 先由 f 共轭，再由 f⁻¹ 共轭 *)
    intro b.
    unfold conjugation, conjugate; simpl.
    rewrite ginv_involutive.
    rewrite <- !comp_assoc.
    rewrite ginv_right, id_right.
    rewrite comp_assoc, ginv_right.
    apply id_left.
  - (* and the other way round / 反过来也一样 *)
    intro a.
    unfold conjugation, conjugate; simpl.
    rewrite ginv_involutive.
    rewrite <- !comp_assoc.
    rewrite ginv_left, id_right.
    rewrite comp_assoc, ginv_left.
    apply id_left.
Defined.

(* * ** The two witnesses of Exercise 3.32 / * ** 练习 3.32 的两个见证者 *)

(*
 Fong and Spivak ask the reader to decide the exercise for two concrete
 monoids.  Both answers are proved here rather than asserted, and they are
 what keeps [deloop_groupoid_iff] from being an empty biconditional: one
 monoid satisfies it on the left and the right, the other on neither side.

 The hom-setoid of [Deloop Nat_Plus] is Lib/Datatypes.v's [nat_setoid],
 whose [equiv] field IS [eq]; so in the three statements about
 [Deloop Nat_Plus] below, `≈` and `=` are the same relation, and `=` is
 used where the argument is arithmetic.  The same holds of [Z3_Mon] at the
 end of the file, whose carrier setoid is likewise Leibniz equality.

 This remark is scoped to those two carriers, and is not a claim about the
 file as a whole.  Every other [=] here is flagged individually where it
 occurs: [ginv_op_eq] relates two MORPHISMS of an arbitrary category and is
 deliberately stronger than `≈`; the remaining ones equate records, types
 or functions rather than morphisms. 

 --------
 Fong 和 Spivak 要求读者为两个具体的幺半群决定练习。这里证明了两个答案，而不是直接断言，它们正是让 [deloop_groupoid_iff] 不成为空双条件的原因：一个幺半群在左侧和右侧都满足它，另一个在两边都不满足。

 [Deloop Nat_Plus] 的同态集合是 Lib/Datatypes.v 中的 [nat_setoid]，其 [equiv] 字段是 [eq]；因此在下面关于 [Deloop Nat_Plus] 的三个陈述中，`≈` 和 `=` 是相同的关系，而当参数是算术时使用 `=`。文件末尾的 [Z3_Mon] 也是如此，其载体集合同样是赖布尼茨等式。该评论仅限于这两个载体，并不是对整个文件的声明。这里的每个其他 [=] 都会在出现的地方单独标记：[ginv_op_eq] 关联任意范畴的两个态射，并且故意比 `≈` 更严格；其余的则是将记录、类型或函数进行等同，而不是态射。
*)

(*
 The only invertible arrow of B (ℕ, +) is the identity: if n + g = 0 then
 n = 0.  (ℕ, +) is the free monoid on one generator, and this is the first
 of the two cases Exercise 3.32 asks the reader to decide. 

 --------
 B (ℕ, +) 唯一可逆的箭头是恒等箭头：如果 n + g = 0 则 n = 0。 (ℕ, +) 是一个单生成元的自由幺半群，这是练习 3.32 要求读者判断的两个情况中的第一个。
*)
Lemma deloop_nat_iso_is_zero (n : carrier Nat_Plus)
  (H : @IsIsomorphism (Deloop Nat_Plus) ttt ttt n) : n = 0%nat.
Proof.
  pose proof (is_right_inverse (IsIsomorphism := H)) as Hr.
  simpl in Hr.                          (* Hr : (n + two_sided_inverse)%nat = 0%nat / Hr : (n + two_sided_inverse)%nat = 0%nat *)
  now destruct n.
Qed.

(*
 Hence B (ℕ, +) is NOT a groupoid.  The witness is the arrow 1, which has
 no inverse: exhibiting a specific non-invertible arrow is the content, an
 appeal to "ℕ is not a group" being a statement about the monoid rather
 than about the category. 

 --------
 因此 B (ℕ, +) 不是一个范畴。证明者是箭头 1，它没有逆：展示一个具体的不可逆箭头就是内容，而提到“ℕ 不是群”是关于幺半群的陈述，而不是关于该范畴的陈述。
*)
Theorem deloop_nat_one_not_invertible :
  @IsIsomorphism (Deloop Nat_Plus) ttt ttt 1%nat → False.
Proof.
  intro H.
  pose proof (deloop_nat_iso_is_zero 1%nat H) as Heq.
  discriminate Heq.
Qed.

Theorem deloop_nat_not_groupoid : IsGroupoid (Deloop Nat_Plus) → False.
Proof.
  intro H.
  exact (deloop_nat_one_not_invertible (H ttt ttt 1%nat)).
Qed.

(* Equivalently, through the biconditional: (ℕ, +) has no inverse operation. / 等价地，通过双条件句：(ℕ, +) 没有逆运算。 *)
Corollary nat_plus_no_inverses : MonInverses Nat_Plus → False.
Proof.
  intro I.
  exact (deloop_nat_not_groupoid (fst (deloop_groupoid_iff Nat_Plus) I)).
Qed.

(* The other witness: the delooping of Z/2 IS a groupoid, because Z/2 is a group. Construction/Deloop.v's [Bool_Xor_Grp] is that group. / 另一个证人：Z/2 的去环化确实是一个群层，因为 Z/2 是一个群。Construction/Deloop.v 中的 [Bool_Xor_Grp] 就是那个群。 *)
Definition deloop_bool_groupoid : IsGroupoid (Deloop Bool_Xor_Grp) :=
  Deloop_IsGroupoid Bool_Xor_Grp.

(* And its vertex group is Z/2 back again, on the nose in both data fields — the round trip of [vertex_group_Deloop_monoid]/[vertex_group_Deloop_inv] at a concrete group. / 它的顶点群再次是 Z/2，恰好在两个数据域中—— [vertex_group_Deloop_monoid] / [vertex_group_Deloop_inv] 在一个具体群上的往返。 *)
Example vertex_group_bool_inv :
  @grp_inv (vertex_group deloop_bool_groupoid ttt) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(* * ** A group whose inversion is not the identity / * ** 其逆不是单位元的群 *)

(*
 In Z/2 every element is its own inverse, so any statement about inversion
 degenerates there: the inverse map is the identity function.  Z/3 is the
 smallest group for which it is not, and it is supplied so that the
 inversion functor of Structure/Groupoid/Inversion.v has a witness where it
 genuinely moves an arrow ([Z3_inversion_nontrivial] there).

 The carrier setoid takes Coq's own equality for `≈`, as [Bool_Xor] does,
 so the [mon_op_respects] field is discharged by instance resolution and
 every law below is a finite case check.

 As in Construction/Deloop.v, the global obligation tactic is switched off
 for the rest of the file: every obligation here is a case split, and the
 wide searches [cat_simpl] would run buy nothing. 

 --------
 在 Z/2 中，每个元素都是它自身的逆，因此关于逆的任何陈述在那里都会退化：逆映射就是恒等函数。Z/3 是最小的非这种情况的群，并且它被提供以便 Structure/Groupoid/Inversion.v 的逆函子有一个证据，能够真实地移动箭头（那里是 [Z3_inversion_nontrivial]）。

 承载的集合类型对 `≈` 采用 Coq 自身的等式，就像 [Bool_Xor] 一样，因此 [mon_op_respects] 字段通过实例解析被解决，并且下面的每条定律都是有限情况检查。

 如同在 Construction/Deloop.v 中，全局义务策略在本文件的其余部分被关闭：这里的每个义务都是一个情况分裂，而广泛搜索 [cat_simpl] 不会买到任何东西。
*)
#[local] Obligation Tactic := idtac.

Inductive Z3 : Set := Z3_0 | Z3_1 | Z3_2.

Definition Z3_add (a b : Z3) : Z3 :=
  match a, b with
  | Z3_0, b    => b
  | a,    Z3_0 => a
  | Z3_1, Z3_1 => Z3_2
  | Z3_1, Z3_2 => Z3_0
  | Z3_2, Z3_1 => Z3_0
  | Z3_2, Z3_2 => Z3_1
  end.

Definition Z3_neg (a : Z3) : Z3 :=
  match a with
  | Z3_0 => Z3_0
  | Z3_1 => Z3_2
  | Z3_2 => Z3_1
  end.

Program Definition Z3_Mon : MonObject := {|
  mon_setoid := {| carrier := Z3
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := Z3_0;
  mon_op     := Z3_add
|}.
Next Obligation.
  intros a b c; now destruct a, b, c.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

Program Definition Z3_Grp : GrpObject := {|
  grp_monoid := Z3_Mon;
  grp_inv    := Z3_neg
|}.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

Definition deloop_Z3_groupoid : IsGroupoid (Deloop Z3_Grp) :=
  Deloop_IsGroupoid Z3_Grp.

(* Inversion in Z/3 really does move an element. The [=] is Leibniz equality on [Z3], which is exactly the `≈` of [Z3_Mon]'s carrier setoid, so nothing weaker is being claimed. / 在 Z/3 中取逆确实会移动一个元素。[=] 是 [Z3] 上的莱布尼茨等式，它正好是 [Z3_Mon] 的载体集合的 `≈`，因此并没有提出更弱的说法。 *)
Example Z3_inv_1 : grp_inv (g:=Z3_Grp) Z3_1 = Z3_2 := eq_refl.

Lemma Z3_inv_moves : grp_inv (g:=Z3_Grp) Z3_1 <> Z3_1.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A nonabelian group, and a conjugation that genuinely moves an element / * ** 一个非阿贝尔群，以及能真正移动一个元素的共轭作用 *)

(*
 The vacuity note on [conjugation_iso] above originally pointed at
 [Bool_Wide_conjugation] as the witness escaping the degenerate case.  An
 audit refuted that: Z/2 is abelian, so conjugation there is the identity
 map, and the witness supplied only the two-distinct-object TYPING.  Worse,
 the whole tree contained no nonabelian group, so no non-identity
 conjugation could be exhibited at all.

 The audit also identified the real dividing line, which the original note
 got wrong: it is abelian versus nonabelian, NOT same-object versus
 distinct-object.  Conjugation by a non-central endomorphism is already a
 nontrivial inner automorphism.

 So this section builds the tree's first nonabelian group — the symmetric
 group on three letters, as a six-element enumeration with an explicit
 multiplication table — and exhibits conjugation moving an element. 

 --------
 上述关于 [conjugation_iso] 的空虚注解最初指出 [Bool_Wide_conjugation] 是逃脱退化情况的见证。审计反驳了这一点：Z/2 是交换群，因此在那里共轭是恒等映射，并且该见证仅提供了两个不同对象的类型化（TYPING）。更糟的是，整个树中没有非交换群，因此根本无法展示非恒等共轭。

 审计还确定了真正的分界线，而原注解搞错了：分界线是交换群与非交换群，而不是相同对象与不同对象。由非中心自同态引导的共轭已经是非平凡的内自同构。因此，本节构建了树的第一个非阿贝尔群——三个字母的对称群，作为一个六元素的枚举，并附有明确的乘法表——并展示了共轭操作如何移动一个元素。
*)

Inductive S3 : Set :=
  | S3_e | S3_r | S3_rr | S3_a | S3_b | S3_c.

(* r is a 3-cycle, rr its square; a, b, c are the three transpositions. / r 是一个 3-循环，rr 是它的平方；a、b、c 是三个换位。 *)
Definition S3_mul (x y : S3) : S3 :=
  match x, y with
  | S3_e,  y    => y
  | x,     S3_e => x
  | S3_r,  S3_r  => S3_rr | S3_r,  S3_rr => S3_e
  | S3_rr, S3_r  => S3_e  | S3_rr, S3_rr => S3_r
  | S3_r,  S3_a  => S3_b  | S3_r,  S3_b  => S3_c  | S3_r,  S3_c  => S3_a
  | S3_rr, S3_a  => S3_c  | S3_rr, S3_b  => S3_a  | S3_rr, S3_c  => S3_b
  | S3_a,  S3_r  => S3_c  | S3_b,  S3_r  => S3_a  | S3_c,  S3_r  => S3_b
  | S3_a,  S3_rr => S3_b  | S3_b,  S3_rr => S3_c  | S3_c,  S3_rr => S3_a
  | S3_a,  S3_a  => S3_e  | S3_b,  S3_b  => S3_e  | S3_c,  S3_c  => S3_e
  | S3_a,  S3_b  => S3_rr | S3_b,  S3_c  => S3_rr | S3_c,  S3_a  => S3_rr
  | S3_a,  S3_c  => S3_r  | S3_b,  S3_a  => S3_r  | S3_c,  S3_b  => S3_r
  end.

Definition S3_inv (x : S3) : S3 :=
  match x with
  | S3_e => S3_e | S3_r => S3_rr | S3_rr => S3_r
  | S3_a => S3_a | S3_b => S3_b  | S3_c  => S3_c
  end.

Program Definition S3_Mon : MonObject := {|
  mon_setoid := {| carrier := S3
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := S3_e;
  mon_op     := S3_mul
|}.
Next Obligation. intros a b c; now destruct a, b, c. Qed.
Next Obligation. intros a; now destruct a. Qed.
Next Obligation. intros a; now destruct a. Qed.

Program Definition S3_Grp : GrpObject := {|
  grp_monoid := S3_Mon;
  grp_inv    := S3_inv
|}.
Next Obligation. intros a; now destruct a. Qed.
Next Obligation. intros a; now destruct a. Qed.

(* It is genuinely nonabelian — the two three-cycles conjugate the transpositions around, which is exactly what Z/2 and Z/3 cannot do. / 它确实是非阿贝尔的——两个三循环会将换位进行共轭，这正是 Z/2 和 Z/3 所不能做到的。 *)
Theorem S3_not_abelian : S3_mul S3_r S3_a = S3_mul S3_a S3_r → False.
Proof. simpl; discriminate. Qed.

Definition deloop_S3_groupoid : IsGroupoid (Deloop S3_Grp) :=
  Deloop_IsGroupoid S3_Grp.

(*
 THE WITNESS THE VACUITY NOTE NEEDED.  Conjugating the transposition [a]
 by the three-cycle [r] inside the delooping of S3 moves it to [c]: the
 automorphism is not the identity, so [conjugation_iso] has content that
 no abelian witness can display. 

 --------
 证人空白笔记是必要的。通过S3的解环内的三循环 [r] 共轭换位 [a]，将其移至 [c]：这个自同构不是恒等的，因此 [conjugation_iso] 具有任何阿贝尔证人都无法显示的内容。
*)
Example S3_conjugation_not_identity :
  conjugate deloop_S3_groupoid (x:=ttt) (x':=ttt) S3_r S3_a = S3_a → False.
Proof. simpl; discriminate. Qed.
