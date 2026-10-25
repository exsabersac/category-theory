Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.

Generalizable All Variables.

(* * * Pushouts in Top: the quotient topology, and adjunction spaces / * * 拓扑中的推挤：商拓扑与黏附空间 *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
 §III.3, book p. 66 / PDF p. 75 (maclane:III.3:remark3)
 nLab:      https://ncatlab.org/nlab/show/pushout
 Wikipedia: https://en.wikipedia.org/wiki/Adjunction_space

 Mac Lane's remark that the Set gluing construction, carried out with
 the quotient topology, gives pushouts in Top -- adjunction spaces being
 the motivating case.

 TWO ERRATA IN THE ISSUE AND ITS SCOPING (#325).  First, its "Current
 state" paragraph says "The Top clause and the entire Grp clause are
 absent -- no Top or Grp category in-tree"; Instance/Top.v and
 Instance/Grp.v both exist now, and what was genuinely absent is the
 pushouts.  Second, and more usefully: it is NOT the case that the tree
 had no quotient-topology donor.  A grep for "quotient" under
 Instance/Top* finds only the homotopy quotient CATEGORY (Toph), but the
 construction is there twice under other names -- Instance/Top.v's
 [CP_open] (the cokernel-pair space) and Instance/Top/Wedge.v's
 [wedge_open], whose surrounding section is literally headed "The
 quotient topology".  Both are quotient topologies on a sum, and
 this file is that same shape with the relation generalized.

 THE CONSTRUCTION, AND THE ONE PLACE IT DIFFERS FROM ITS DONORS.  The
 points are the coproduct's points -- [Top_pushout_carrier] records by
 [eq_refl] that the carrier IS Instance/Top/Coproduct.v's [sum_carrier].
 The relation is where the difference sits: [CP_rel] and [wedge_rel] are
 already transitive and are written as a [match], whereas an arbitrary
 span has no closed form, so [tp_rel] is an INDUCTIVE equivalence
 closure in the SHAPE of Instance/Sets/Pushout.v's [pushout_eq] --
 the same five constructors in the same order -- RESTATED here for
 spaces.  Read that precisely: this file does NOT [Require]
 Instance/Sets/Pushout.v, so it is a structural copy and not reuse,
 which matters in a tree that elsewhere distinguishes the two.
 The topology is then the [CP_open] / [wedge_open] triple: a
 respect-the-gluing clause plus the two restrictions.  That triple IS
 the quotient topology of [B + C -> (B + C)/~] -- a predicate downstairs
 is open when its preimage is, and a saturated predicate's preimage is
 open exactly when both restrictions are -- and it is what makes
 continuity of the mediator ([tp_med_continuous]) a three-line argument
 with no quotient-topology lemma required.

 NO UNIVERSE WALL IS MET.  Instance/Top/Coproduct.v and
 Instance/Top/Homotopy.v both record that opens of a space live one
 level above its points, which is why a product-of-spaces or a cylinder
 is not formable at the space's own level.  Nothing here quantifies over
 opens: [tp_open] only APPLIES [IsOpen] to restricted predicates, and
 the gluing clause is a Pi over the point type into [Type@{o}], so the
 whole construction stays at the space's own level.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  [Top_HasPushouts] is the
 deliverable.  The chosen pushout's apex and both injections are the
 hand-built ones at LEIBNIZ EQUALITY ([Top_pushout_apex_is_Pushout_Top]
 and siblings, [eq_refl]).  [pushout_med] is NOT [Top_po_med] on the
 nose -- Structure/Pushout.v states [pushout_ump] as a [Qed] lemma, so
 [unique_obj] is applied to an opaque constant; the negative is pinned
 in Test/ProbePushoutGrpTop.v alongside the IDENTICAL negative on the
 Grp side, which is what shows the cause is the donor's opacity and not
 either substrate.  [AdjunctionSpace] names the motivating case and
 [adjunction_glues] is the identification it exists for; nothing
 requires the attaching map to be an inclusion, so the name follows
 classical usage while the general pushout is what is built.

 NON-VACUITY, BOTH WAYS, AND NEITHER BY ASSERTION.  A non-identification
 cannot be read off [tp_rel] by induction, since [tpr_trans] passes
 through arbitrary intermediates; [tp_side] is the invariant that makes
 it reachable, and [empty_span_keeps_summands_apart] uses it to show
 that over the EMPTY span nothing is glued (the glue constructor's
 argument being a point of the empty space).  THE CONTRAST is
 [point_span_merges]: over the ONE-POINT span the two injections agree
 at the very pair Instance/Top/Coproduct.v's
 [point_sum_injections_differ] proves distinct in the coproduct.  So the
 pushout genuinely glues and is not the coproduct read twice -- the same
 shape of argument Instance/Top/Wedge.v's [wedge_is_not_sum] makes for
 the wedge.

 THE EMPTY SPAN IS THE COPRODUCT, AD HOC.  [Top_pushout_empty_iso] is an
 isomorphism in Top between the empty-span pushout and [Sum_Top], both
 legs having [fun u => u] as their underlying function.  CROSS-REFERENCE
 precisely: the GENERAL bridge "a pushout over the initial object is the
 binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and is NOT
 built here or in Instance/Grp/Pushout.v, which carries the
 corresponding ad-hoc Grp instance.  That the isomorphism is not an
 identity is measured rather than asserted: two conversion negatives
 reject the equality of the two [SetoidObject]s (the apex compares
 points by the inductive [tp_rel], the coproduct by [sum_setoid]'s
 [match]) and of the two topologies ([tp_open] carries a gluing clause
 that [sum_open] does not, redundant over the empty span but not
 definitionally absent).

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS, WITH THE CAUSE PROBED.
 [Pushout_Top@{u u0 u1 u2}] displays three separate space levels in its
 binder while its constraint block carries [u = u0] and [u = u1]: the
 three spaces sit at ONE level, an identification and not a bound, the
 same one Instance/Top/Coproduct.v measures for [Sum_Top].  The cause is
 probed and is NOT this construction: the bare definition
 [fun (A B : TopSpace) (f : @hom Top A B) => B] already elaborates with
 both spaces at [TopSpace@{u0}].  Naming a single Top hom is what
 identifies them.  [Top_HasPushouts@{u u0}] carries [u < u0] -- Top's
 own points-below-opens stratification -- and NO [Set] appears in any
 constraint block in this file, AS ON THE GRP SIDE, whose constant-leg
 free-product layer is likewise [Set]-free (measured: zero [Set]
 occurrences across [grp_const], [Grp_free_product], [Grp_fp_inl/inr],
 [Grp_fp_merge], [Grp_fp_inl_Section] and [Grp_Cocartesian]).  The one
 [Set]-pinned constant over there is [Grp_zero_hom_Section], which is
 the route NOT taken.  (CORRECTION, #450: it is pinned no longer; #450
 wrote out the universes of its donor [Grp_zero_hom] in Instance/Grp.v,
 and [About] reads [Grp_zero_hom_Section@{u u0}] over
 [GrpObject@{u0 u0 u0}].)  (An earlier draft of this header claimed the Grp
 free-product layer inherits a [Set] pin; that was false, contradicted
 Instance/Grp/Pushout.v's own measured statement, and was a leftover
 from the refuted first construction.)

 ENGINEERING FINDING, recorded because it cost time.  In
 [tp_rel_to_sum], writing [induction H; simpl] unfolds the sum setoid's
 [match] into its raw [eq_refl]-scaffolded eliminator form, after which
 [symmetry] and [transitivity] fail with an "Illegal application" of
 [@eq_refl] rather than with a missing-instance message.  Dropping the
 [simpl] and closing the two base cases with [inl_respects] /
 [inr_respects] keeps the goal at [≈] and the tactics work.  The related
 trap is that the binders must be written [u v : sum_carrier B C] rather
 than [u v : tp_point] even though the two types are convertible: only
 the [SetoidObject] spelling lets [≈] resolve, and with the [tp_point]
 spelling the statement silently elaborates at Leibniz equality.

 WHAT IS NOT DELIVERED.  No separation or compactness properties of the
 glued space, and in particular nothing about when an adjunction space
 is Hausdorff; no CW-complex or cell-attachment machinery; no mapping
 cylinder or mapping cone; no van Kampen theorem, and so no connection
 to Instance/Top/FundamentalGroupoid.v or to Instance/Grp/Pushout.v's
 amalgamated products; no subspace or general quotient topology as
 free-standing constructions (only the one this pushout needs); no
 indexed pushouts and no colimits of Top in general; no pointed variant,
 so Instance/Top/Wedge.v's [Top_pointed] is untouched; and no monic-legs
 refinement on this side -- Structure/Pushout/Split.v's generic
 statements apply to Top verbatim but no Top span is exhibited whose
 legs split.  CORRECTION (#457): the "no subspace or general quotient
 topology as free-standing constructions" item holds of this file only.
 Instance/Top/Presheaf.v's [OpenSub], the subspace on an OPEN subset,
 predates #457; #457 adds both in general, Instance/Top/Subspace.v's
 [PSub] and [PQuot]
 over Instance/Top/Prop.v's Prop-valued spaces, and the general
 quotient over [Top] as Instance/Top/Subspace/TypeValued.v's [TQuot];
 this pushout is not rebuilt on them. 

 --------
 书籍：Mac Lane，《为工作中的数学家准备的范畴论》（第2版），
 §III.3，第66页 / PDF第75页（maclane:III.3:remark3）
 nLab:       https://ncatlab.org/nlab/show/pushout 
 维基百科:  https://en.wikipedia.org/wiki/Adjunction_space 

 Mac Lane的备注指出，使用商拓扑进行的集合拼接构造在拓扑空间（Top）中给出了推挤（pushouts）——驱动动机的案例是附接空间（adjunction spaces）。该问题及其范围说明中的两个勘误 (#325)。首先，它的“当前状态”段落中说“Top 子句和整个 Grp 子句都不存在 —— 树中没有 Top 或 Grp 类别”；然而 Instance/Top.v 和 Instance/Grp.v 都已经存在，真正缺失的是推送图。其次，更有用的是：树中并非没有商拓扑的供体。在 Instance/Top* 下 grep “quotient” 只会找到同伦商 CATEGORY (Toph)，但该构造以其他名字出现了两次 —— Instance/Top.v 中的 [CP_open]（余核对空间）和 Instance/Top/Wedge.v 中的 [wedge_open]，其所在的章节标题字面上是“商拓扑”。两者都是对一个和的商拓扑，并且该文件是相同的形状，只是关系被泛化了。构造，以及它与其来源不同的唯一地方。 这些点是余积的点 —— 由[Top_pushout_carrier]记录，通过[eq_refl]表示载体是Instance/Top/Coproduct.v的[sum_carrier]。不同之处就在于这个关系：[CP_rel]和[wedge_rel]已经是传递的，并写成[match]，而任意的跨度没有封闭形式，因此[tp_rel]是Instance/Sets/Pushout.v的[pushout_eq]形式中的归纳等价闭包 —— 相同的五个构造器按相同顺序 —— 在这里为空间重述。 精确理解：该文件没有[Require] Instance/Sets/Pushout.v，所以它是一个结构副本，而不是重用，在树结构中这很重要，因为其他地方区分了两者。拓扑就是 [CP_open] / [wedge_open] 三元组：一个遵守粘合的条款加上两个限制。这个三元组就是 [B + C -> (B + C)/~] 的商拓扑——当一个下层谓词的原像是开集时，它就是开集，而一个饱和谓词的原像恰好在两个限制都满足时是开集——它使得中介者（[tp_med_continuous]）的连续性只需三行论证，而不需要商拓扑引理。没有满足宇宙壁垒。Instance/Top/Coproduct.v 和 Instance/Top/Homotopy.v 都记录了空间的开集位于其点的上一层，这就是为什么空间的乘积或圆柱不能在空间自身层级形成的原因。这里没有对开集进行量化：[tp_open] 仅将 [IsOpen] 应用于受限谓词，并且粘合条款是对点类型的 Pi 映射到 [Type@{o}]，因此整个构造保持在空间自身的层级。已经证明的内容，以及在什么强度下。[Top_HasPushouts] 是可交付的。所选的推挤顶点及两个注射都是在 LEIBNIZ 相等下手工构建的（[Top_pushout_apex_is_Pushout_Top] 及其相关的 [eq_refl]）。[pushout_med] 并不是完全等于 [Top_po_med] —— Structure/Pushout.v 将 [pushout_ump] 陈述为一个 [Qed] 引理，因此 [unique_obj] 被应用于一个不透明常数；负例被固定在 Test/ProbePushoutGrpTop.v 中，与群（Grp）侧的完全相同的负例一起，这显示了原因是捐赠者的不透明性，而不是任何基体。[AdjunctionSpace] 表示激励案例，[adjunction_glues] 是它存在的标识；没有要求附加映射必须是包含映射，所以这个名称遵循经典用法，而构建的是一般的推挤结构。非空性，双向，并且非通过断言。一个非同一性不能通过归纳从 [tp_rel] 中读取，因为 [tpr_trans] 会经过任意中间步骤；[tp_side] 是使其可达的不变式，[empty_span_keeps_summands_apart] 使用它来显示在 EMPTY 范围上没有任何东西被粘合（粘合构造函数的参数是空空间的一个点）。对比是 [point_span_merges]：在 ONE-POINT 范围上，这两个注入在 Instance/Top/Coproduct.v 的那个特定对上是一致的，[point_sum_injections_differ] 在直和中证明它们是不同的。因此，推挤真正地进行了粘合，而不是把直和读两次——Instance/Top/Wedge.v 的 [wedge_is_not_sum] 使用了同样的论证方式来处理楔形。空跨不是伴随积，而是特殊构造。[Top_pushout_empty_iso] 是 Top 中空跨推出的推拉积与 [Sum_Top] 之间的同构，两个分支的底层函数都是 [fun u => u]。交叉引用具体如下：泛桥“初始对象上的推拉积是二元伴随积”是开放问题 #862（Seven Sketches 6.2.3），在此处或 Instance/Grp/Pushout.v 中均未构建，该文件只包含相应的特设 Grp 实例。同构不是一个恒等关系，这是通过测量而不是断言得出的：两个转换负态拒绝两个 [SetoidObject] 的相等性（顶点通过归纳 [tp_rel] 比较点，余积通过 [sum_setoid] 的 [match] 进行比较）以及两个拓扑的相等性（[tp_open] 具有 [sum_open] 没有的粘合子句，在空跨度上是多余的，但在定义上并不缺失）。宇宙，在约束块中测量，并探测原因。[Pushout_Top@{u u0 u1 u2}] 在其绑定器中显示三个独立的空间层级，而其约束块承载了 [u = u0] 和 [u = u1]：这三个空间位于同一层级，是一种识别而非约束，同一个 Instance/Top/Coproduct.v 对 [Sum_Top] 进行测量。原因已被探测，并不是这个结构：裸定义 [fun (A B : TopSpace) (f : @hom Top A B) => B] 已经在 [TopSpace@{u0}] 上扩展了两个空间。命名单个 Top hom 才能识别它们。[Top_HasPushouts@{u u0}] 包含 [u < u0] —— 顶层自身的点-下开-分层 —— 并且在此文件中的任何约束块中都没有 [Set]，就像在 GRP 端一样，其常数腿自由产品层同样是 [Set]-自由的（测量：在 [grp_const]、[Grp_free_product]、[Grp_fp_inl/inr]、[Grp_fp_merge]、[Grp_fp_inl_Section] 和 [Grp_Cocartesian] 中 [Set] 出现次数为零）。那边唯一的 [Set] 锁定常数是 [Grp_zero_hom_Section]，这条路线是未选择的。(更正，#450：它不再被固定；#450 在 Instance/Grp.v 中写出了其捐赠者 [Grp_zero_hom] 的宇宙，而 [About] 读取 [Grp_zero_hom_Section@{u u0}] 覆盖 [GrpObject@{u0 u0 u0}]。)（该标题的早期草稿声称 Grp 自由积层继承了 [Set] 固定；那是错误的，与 Instance/Grp/Pushout.v 自身的测量声明相矛盾，并且是被推翻的第一次构造的残留。）工程发现，记录下来是因为它耗费了时间。在 [tp_rel_to_sum] 中，编写 [induction H; simpl] 会将合集算子 [match] 展开为其原始的 [eq_refl] 脚手架化消除器形式，此后 [symmetry] 和 [transitivity] 会因为 [@eq_refl] 的“非法应用”而失败，而不是因缺少实例消息而失败。去掉 [simpl] 并用 [inl_respects] / [inr_respects] 关闭两个基本情况，目标保持在 [≈]，并且策略可行。相关陷阱是绑定器必须写作 [u v : sum_carrier B C] 而不是 [u v : tp_point]，尽管这两种类型是可转换的：只有 [SetoidObject] 的拼写才能让 [≈] 解析，而使用 [tp_point] 拼写时，语句会在莱布尼茨等式下默默地展开。未提供的内容。关于粘合空间的分离性或紧凑性性质，以及特别是关于附加空间何时是豪斯多夫空间的内容均未涉及；没有 CW 复形或胞附加的工具；没有映射圆柱或映射锥；没有范·坎彭定理，因此也没有与 Instance/Top/FundamentalGroupoid.v 或 Instance/Grp/Pushout.v 的合并积有关的内容；没有作为独立构造的子空间或一般商拓扑（仅限此推出来需要的）；没有索引的推挤以及一般意义上拓扑类的余极限；没有指向的变体，因此 Instance/Top/Wedge.v 的 [Top_pointed] 未被触及；在这边没有单态腿的细化——Structure/Pushout/Split.v 的一般性陈述可以照搬到拓扑中，但没有展示拓扑跨度及其腿可拆分的情况。更正 (#457)："不作为独立构造的子空间或一般商拓扑" 这一条目仅适用于此文件。Instance/Top/Presheaf.v 中的 [OpenSub]，即在开子集上的子空间，早于 #457；#457 在一般情况下添加了 Instance/Top/Subspace.v 的 [PSub] 和 [PQuot] 以及在 Instance/Top/Prop.v 的 Prop 值空间上的一般商拓扑，以及 Instance/Top/Subspace/TypeValued.v 的 [TQuot] 对应 [Top] 的一般商拓扑；这个推挤范畴在它们上面没有重建。
*)

(** ** The glued point set / ** 粘合点集 *)

Section TopPushout.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).

Definition tp_point : Type :=
  (carrier (top_carrier B) + carrier (top_carrier C))%type.

(*
 The identification generated by the span.  Unlike [Instance/Top.v]'s
 cokernel-pair relation and [Instance/Top/Wedge.v]'s basepoint
 relation -- both of which are already transitive and can be written as
 a [match] -- an arbitrary span has no closed form, so the relation is
 the inductive equivalence closure of Instance/Sets/Pushout.v. 

 --------
 由跨度生成的同一性。与 [Instance/Top.v] 的余核对关系和 [Instance/Top/Wedge.v] 的基点关系不同——它们都已经是传递的，并且可以写成 [match] ——任意的跨度没有封闭形式，因此该关系是 Instance/Sets/Pushout.v 的归纳等价闭包。
*)
Inductive tp_rel : tp_point → tp_point → Type :=
  | tpr_inl : ∀ b b' : carrier (top_carrier B),
      b ≈ b' → tp_rel (Datatypes.inl b) (Datatypes.inl b')
  | tpr_inr : ∀ c c' : carrier (top_carrier C),
      c ≈ c' → tp_rel (Datatypes.inr c) (Datatypes.inr c')
  | tpr_glue : ∀ a : carrier (top_carrier A),
      tp_rel (Datatypes.inl (f a)) (Datatypes.inr (g a))
  | tpr_sym : ∀ u v, tp_rel u v → tp_rel v u
  | tpr_trans : ∀ u v w, tp_rel u v → tp_rel v w → tp_rel u w.

Lemma tp_rel_refl : Reflexive tp_rel.
Proof using All.
  intros [b | c].
  - apply tpr_inl; reflexivity.
  - apply tpr_inr; reflexivity.
Qed.

Definition tp_setoid : Setoid tp_point := {|
  equiv := tp_rel;
  setoid_equiv :=
    Build_Equivalence tp_rel tp_rel_refl tpr_sym tpr_trans
|}.

Definition tp_carrier : SetoidObject := {|
  carrier := tp_point;
  is_setoid := tp_setoid
|}.

(** ** The quotient topology / ** 商拓扑 *)

(*
 The [CP_open] / [wedge_open] shape: a respect-the-gluing clause plus
 the two restrictions.  This IS the quotient topology of the surjection
 [B + C -> (B + C)/~]: a set downstairs is open exactly when its
 preimage upstairs is, and a saturated predicate's preimage is open
 exactly when both restrictions are. 

 --------
 [CP_open] / [wedge_open] 形状：一个尊重粘合条款加上两个限制。这是 [B + C -> (B + C)/~] 的商拓扑：一个底层集合是开集，当且仅当它在上层的原像是开集，并且一个饱和谓词的原像是开集，当且仅当两个限制都成立。
*)
Definition tp_open (W : tp_carrier → Type) : Type :=
  ((∀ u v : tp_carrier, tp_rel u v → W u → W v)
     ∧ IsOpen B (fun b => W (Datatypes.inl b))
     ∧ IsOpen C (fun c => W (Datatypes.inr c)))%type.

Lemma tp_respects (U V : tp_carrier → Type) :
  (∀ u, U u ↔ V u) → tp_open U → tp_open V.
Proof using All.
  intros H [HR [HB HC]].
  split; [| split ].
  - intros u v Huv Vu.
    exact (fst (H v) (HR u v Huv (snd (H u) Vu))).
  - exact (open_respects B _ _ (fun b => H (Datatypes.inl b)) HB).
  - exact (open_respects C _ _ (fun c => H (Datatypes.inr c)) HC).
Qed.

Lemma tp_proper (W : tp_carrier → Type) :
  tp_open W → ∀ u v : tp_carrier, u ≈ v → W u → W v.
Proof using All. intros [HR _] u v Huv Wu; exact (HR u v Huv Wu). Qed.

Lemma tp_union (I : Type) (U : I → (tp_carrier → Type)) :
  (∀ i, tp_open (U i)) → tp_open (fun u => { i : I & U i u }).
Proof using All.
  intro H.
  split; [| split ].
  - intros u v Huv [i Hi].
    exact (i; fst (H i) u v Huv Hi).
  - exact (open_union B I (fun i b => U i (Datatypes.inl b))
             (fun i => fst (snd (H i)))).
  - exact (open_union C I (fun i c => U i (Datatypes.inr c))
             (fun i => snd (snd (H i)))).
Qed.

Lemma tp_whole : tp_open (fun _ => poly_unit).
Proof using All.
  split; [| split ].
  - intros u v _ _; exact ttt.
  - exact (open_whole B).
  - exact (open_whole C).
Qed.

Lemma tp_inter (U V : tp_carrier → Type) :
  tp_open U → tp_open V → tp_open (fun u => U u ∧ V u).
Proof using All.
  intros [HRU [HBU HCU]] [HRV [HBV HCV]].
  split; [| split ].
  - intros u v Huv [Uu Vu].
    exact (HRU u v Huv Uu, HRV u v Huv Vu).
  - exact (open_inter B _ _ HBU HBV).
  - exact (open_inter C _ _ HCU HCV).
Qed.

Definition Pushout_Top : TopSpace := {|
  top_carrier   := tp_carrier;
  IsOpen        := tp_open;
  open_respects := tp_respects;
  open_proper   := tp_proper;
  open_union    := tp_union;
  open_whole    := tp_whole;
  open_inter    := tp_inter
|}.

(** ** The injections / ** 注射 *)

Definition tp_inl_map : SetoidMorphism (top_carrier B) tp_carrier.
Proof using All.
  unshelve notypeclasses refine {| morphism := Datatypes.inl |}.
  intros b b' Hb; exact (tpr_inl b b' Hb).
Defined.

Definition tp_inr_map : SetoidMorphism (top_carrier C) tp_carrier.
Proof using All.
  unshelve notypeclasses refine {| morphism := Datatypes.inr |}.
  intros c c' Hc; exact (tpr_inr c c' Hc).
Defined.

Definition Top_po_in1 : B ~{Top}~> Pushout_Top :=
  Build_ContinuousMorphism B Pushout_Top tp_inl_map
    (fun W HW => fst (snd HW)).

Definition Top_po_in2 : C ~{Top}~> Pushout_Top :=
  Build_ContinuousMorphism C Pushout_Top tp_inr_map
    (fun W HW => snd (snd HW)).

(* The square commutes: this IS the [tpr_glue] constructor. / 这个方框是可交换的：这就是 [tpr_glue] 构造函数。 *)
Lemma Top_po_square : Top_po_in1 ∘[Top] f ≈ Top_po_in2 ∘[Top] g.
Proof using All. intro a; exact (tpr_glue a). Qed.

End TopPushout.

Arguments tp_point {B C}.
Arguments tp_rel {A B C} f g u v.
Arguments tp_open {A B C} f g W.
Arguments Pushout_Top {A B C} f g.
Arguments Top_po_in1 {A B C} f g.
Arguments Top_po_in2 {A B C} f g.

(** ** The mediating continuous map / ** 中介连续映射 *)

Section TopPushoutMediator.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).
Context {Q : TopSpace}.
Context (q1 : B ~{Top}~> Q) (q2 : C ~{Top}~> Q).

Definition tp_med_fun (u : @tp_point B C) : carrier (top_carrier Q) :=
  match u with
  | Datatypes.inl b => q1 b
  | Datatypes.inr c => q2 c
  end.

Context (Hcomm : q1 ∘[Top] f ≈ q2 ∘[Top] g).

(*
 Well-definedness on the quotient, by induction on the derivation.  The
 glue case is the ONLY one that consumes [Hcomm]. 

 --------
 通过对推导进行归纳，在商上定义良好性。粘合情况是唯一消耗 [Hcomm] 的情况。
*)
Lemma tp_med_respects (u v : @tp_point B C) (H : tp_rel f g u v) :
  tp_med_fun u ≈ tp_med_fun v.
Proof using All.
  induction H; simpl.
  - now apply proper_morphism.
  - now apply proper_morphism.
  - exact (Hcomm a).
  - now symmetry.
  - now transitivity (tp_med_fun v).
Qed.

Definition tp_med_map
  : SetoidMorphism (top_carrier (Pushout_Top f g)) (top_carrier Q).
Proof using All.
  unshelve notypeclasses refine {| morphism := tp_med_fun |}.
  intros u v Huv; exact (tp_med_respects u v Huv).
Defined.

(*
 Continuity.  The preimage of an open [W] is open in the glued space for
 three reasons, one per clause: it respects the gluing because the
 mediator does and [W] is [open_proper]; and its two restrictions are
 the preimages of [W] under [q1] and [q2], open by their continuity.
 NO quotient-topology lemma is needed -- the topology was DEFINED as the
 conjunction that makes this argument go through. 

 --------
 连续性。开集 [W] 的原像在粘合空间中是开集，有三个原因，每个分句对应一个原因：它尊重粘合，因为媒介者也尊重，而且 [W] 就是 [open_proper]；它的两个限制是 [W] 在 [q1] 和 [q2] 下的原像，根据它们的连续性是开的。不需要任何商拓扑引理——拓扑是被定义为使这个论证成立的合取。
*)
Lemma tp_med_continuous : Continuous (Pushout_Top f g) Q tp_med_map.
Proof using All.
  intros W HW.
  split; [| split ].
  - intros u v Huv Wu.
    exact (open_proper Q W HW (tp_med_fun u) (tp_med_fun v)
             (tp_med_respects u v Huv) Wu).
  - exact (continuity q1 W HW).
  - exact (continuity q2 W HW).
Qed.

Definition Top_po_med : Pushout_Top f g ~{Top}~> Q :=
  Build_ContinuousMorphism (Pushout_Top f g) Q tp_med_map tp_med_continuous.

Lemma Top_po_med_in1 : Top_po_med ∘[Top] Top_po_in1 f g ≈ q1.
Proof using All. intro b; reflexivity. Qed.

Lemma Top_po_med_in2 : Top_po_med ∘[Top] Top_po_in2 f g ≈ q2.
Proof using All. intro c; reflexivity. Qed.

Lemma Top_po_med_unique (v : Pushout_Top f g ~{Top}~> Q)
      (H1 : v ∘[Top] Top_po_in1 f g ≈ q1)
      (H2 : v ∘[Top] Top_po_in2 f g ≈ q2) :
  Top_po_med ≈ v.
Proof using All.
  intros [b | c]; simpl.
  - symmetry; exact (H1 b).
  - symmetry; exact (H2 c).
Qed.

End TopPushoutMediator.

Arguments Top_po_med {A B C} f g {Q} q1 q2 Hcomm.

(* * ** The universal property, packaged / * ** 通用属性，打包 *)

Local Obligation Tactic := idtac.

#[export] Program Instance Top_HasPushouts : HasPushouts Top := {|
  pushout := fun A B C f g =>
    {| Pull         := Pushout_Top f g;
       pullback_fst := Top_po_in1 f g;
       pullback_snd := Top_po_in2 f g
    |}
|}.
Next Obligation.
  intros A B C f g.
  exact (Top_po_square f g).
Defined.
Next Obligation.
  intros A B C f g Q q1 q2 Hcomm.
  unshelve refine {| unique_obj := Top_po_med f g q1 q2 Hcomm |}.
  - split.
    + exact (Top_po_med_in1 f g q1 q2 Hcomm).
    + exact (Top_po_med_in2 f g q1 q2 Hcomm).
  - intros v [Hv1 Hv2].
    exact (Top_po_med_unique f g q1 q2 Hcomm v Hv1 Hv2).
Defined.

(* * ** The chosen pushout, and what reduces / * ** 所选的推送，以及什么会被减少 *)

Definition Top_pushout {A B C : TopSpace}
           (f : A ~{Top}~> B) (g : A ~{Top}~> C) : IsPushout f g :=
  @pushout Top Top_HasPushouts A B C f g.

Example Top_pushout_apex_is_Pushout_Top {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_apex (Top_pushout f g) = Pushout_Top f g := eq_refl.

Example Top_pushout_in1_is_Top_po_in1 {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_in1 (Top_pushout f g) = Top_po_in1 f g := eq_refl.

Example Top_pushout_in2_is_Top_po_in2 {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_in2 (Top_pushout f g) = Top_po_in2 f g := eq_refl.

(* The glued point set is the coproduct's point set on the nose: the pushout topology differs from the coproduct topology only in the respect-the-gluing clause, not in its points. / 粘合点集正是余积的点集：挤出拓扑与余积拓扑的区别仅在于遵循粘合的条款，而不在其点上。 *)
Example Top_pushout_carrier {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  carrier (top_carrier (Pushout_Top f g))
    = carrier (sum_carrier B C) := eq_refl.

(*
   * ** Adjunction spaces

   The motivating case of Mac Lane's remark: [X] with [Y] attached along
   [f : A -> Y], for a subspace inclusion [i : A -> X].  Nothing here
   requires [i] to be an inclusion; the name follows the classical usage,
   and the general pushout is what is built. 

   --------
   * ** 附加空间

   Mac Lane 评论的动机案例：[X] 与 [Y] 沿着 [f : A -> Y] 相连，针对子空间包含 [i : A -> X]。这里没有任何要求 [i] 是一个包含；这个名称沿用了经典用法，而一般的推挤图则就是构造的对象。
*)

Definition AdjunctionSpace {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y) : TopSpace :=
  Pushout_Top i f.

Definition adjunction_in_base {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y)
  : X ~{Top}~> AdjunctionSpace i f := Top_po_in1 i f.

Definition adjunction_in_attached {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y)
  : Y ~{Top}~> AdjunctionSpace i f := Top_po_in2 i f.

(* The attaching identification, which is what the construction exists for: a point of [A] and its image under [f] become the same point. / 附着的标识，这就是该构造存在的原因：[A] 的一点及其在 [f] 下的像变成同一点。 *)
Lemma adjunction_glues {A X Y : TopSpace}
      (i : A ~{Top}~> X) (f : A ~{Top}~> Y) (a : carrier (top_carrier A)) :
  adjunction_in_base i f (i a) ≈ adjunction_in_attached i f (f a).
Proof. exact (@tpr_glue A X Y i f a). Qed.

(* * ** Non-vacuity: the gluing is real, and it is confined to the span / * ** 非虚无性：粘合是真实的，并且它仅限于跨度内 *)

(*
 Which summand a glued point came from.  This is the invariant that
 makes a NEGATIVE statement about [tp_rel] reachable: no induction on a
 generated equivalence yields a non-identification directly, because
 [tpr_trans] passes through arbitrary intermediates. 

 --------
 哪个加数是由一个粘合点产生的。这是不变量，它对可达的 [tp_rel] 做出一个否定的陈述：没有对生成的等价关系进行归纳会直接产生非同一性，因为 [tpr_trans] 会经过任意中间步骤。
*)
Definition tp_side {B C : TopSpace} (u : @tp_point B C) : bool :=
  match u with
  | Datatypes.inl _ => true
  | Datatypes.inr _ => false
  end.

Lemma tp_side_invariant {B C : TopSpace}
      (f : Empty_Top ~{Top}~> B) (g : Empty_Top ~{Top}~> C)
      (u v : @tp_point B C) (H : tp_rel f g u v) :
  tp_side u = tp_side v.
Proof.
  induction H; simpl; try reflexivity.
  - contradiction.
  - now symmetry.
  - now transitivity (tp_side v).
Qed.

(*
 Over the EMPTY span the two summands stay apart: the glue constructor
 is unusable, its argument being a point of the empty space. 

 --------
 在空跨度上，两个加数保持分离：粘合构造器无法使用，因为它的参数是空空间的一个点。
*)
Theorem empty_span_keeps_summands_apart {B C : TopSpace}
        (f : Empty_Top ~{Top}~> B) (g : Empty_Top ~{Top}~> C)
        (b : carrier (top_carrier B)) (c : carrier (top_carrier C)) :
  tp_rel f g (Datatypes.inl b) (Datatypes.inr c) → False.
Proof.
  intro H.
  pose proof (tp_side_invariant f g _ _ H) as Hs.
  simpl in Hs.
  discriminate Hs.
Qed.

(*
 THE CONTRAST.  Over the ONE-POINT span the two injections agree at the
 very pair that Instance/Top/Coproduct.v's [point_sum_injections_differ]
 proves distinct in the coproduct.  So the pushout genuinely glues, and
 is not the coproduct read twice -- the same shape of argument
 Instance/Top/Wedge.v's [wedge_is_not_sum] makes for the wedge. 

 --------
 对比。在这个单点区间上，这两个注入在 Instance/Top/Coproduct.v 的 [point_sum_injections_differ] 证明在积上是不同的一对处是一致的。因此，推进真正地粘合在一起，而不是将积读两次——Instance/Top/Wedge.v 的 [wedge_is_not_sum] 的同样论证方式适用于楔形。
*)
Theorem point_span_merges :
  @tp_rel Point_Top Point_Top Point_Top
    (@id Top Point_Top) (@id Top Point_Top)
    (Datatypes.inl ttt) (Datatypes.inr ttt).
Proof.
  exact (@tpr_glue Point_Top Point_Top Point_Top
           (@id Top Point_Top) (@id Top Point_Top) ttt).
Qed.

(*
   * ** The pushout over the empty space IS the coproduct

   Cross-reference: the GENERAL bridge "a pushout over the initial object
   is the binary coproduct" is open issue #862 (Seven Sketches 6.2.3) and
   is NOT built here.  What follows is the ad-hoc Top instance, the
   counterpart of Instance/Grp/Pushout.v's [Grp_Cocartesian].  Both
   comparison maps are the IDENTITY on points; all the content is in the
   two topologies and the two setoids agreeing. 

   --------
   * ** 在空集上的推出就是余积

   交叉引用：一般桥“在初始对象上的推出是二元余积”是未解决的问题 #862（Seven Sketches 6.2.3），这里并未构建。接下来的是临时的 Top 实例，对应于 Instance/Grp/Pushout.v 的 [Grp_Cocartesian]。两个比较映射在点上都是恒等映射；所有内容都在两个拓扑和两个集合类的对应上。
*)

Section EmptySpanIsCoproduct.

Context (B C : TopSpace).

Notation Ef := (top_zero B).
Notation Eg := (top_zero C).

(*
 Stated over [sum_carrier B C] rather than over [tp_point], although
 the two types are convertible: writing the binder as the SetoidObject
 is what lets [≈], [symmetry] and [transitivity] resolve the sum setoid
 -- with a [tp_point] binder they default to Leibniz equality and the
 proof does not elaborate. 

 --------
 声明在 [sum_carrier B C] 上而不是 [tp_point] 上，尽管这两种类型是可转换的：将绑定器写为 SetoidObject 是让 [≈]、[symmetry] 和 [transitivity] 解析和集的原因——使用 [tp_point] 绑定器时，它们默认使用莱布尼茨等式，且证明不会详细展开。
*)
Lemma tp_rel_to_sum (u v : sum_carrier B C) (H : tp_rel Ef Eg u v) :
  u ≈ v.
Proof using All.
  induction H.
  - now apply inl_respects.
  - now apply inr_respects.
  - contradiction.
  - now symmetry.
  - now transitivity v.
Qed.

Lemma sum_rel_to_tp (u v : sum_carrier B C) (H : u ≈ v) :
  tp_rel Ef Eg u v.
Proof using All.
  destruct u as [b | c], v as [b' | c']; simpl in H.
  - exact (@tpr_inl Empty_Top B C Ef Eg b b' H).
  - contradiction.
  - contradiction.
  - exact (@tpr_inr Empty_Top B C Ef Eg c c' H).
Qed.

Definition tp_to_sum_map
  : SetoidMorphism (top_carrier (Pushout_Top Ef Eg)) (sum_carrier B C).
Proof using All.
  unshelve notypeclasses refine {| morphism := fun u => u |}.
  intros u v Huv; exact (tp_rel_to_sum u v Huv).
Defined.

Definition tp_from_sum_map
  : SetoidMorphism (sum_carrier B C) (top_carrier (Pushout_Top Ef Eg)).
Proof using All.
  unshelve notypeclasses refine {| morphism := fun u => u |}.
  intros u v Huv; exact (sum_rel_to_tp u v Huv).
Defined.

Definition tp_to_sum : Pushout_Top Ef Eg ~{Top}~> Sum_Top B C.
Proof using All.
  unshelve refine (Build_ContinuousMorphism
                     (Pushout_Top Ef Eg) (Sum_Top B C) tp_to_sum_map _).
  intros W HW.
  split; [| split ]; [| exact (fst HW) | exact (snd HW) ].
  intros u v Huv Wu.
  exact (sum_proper B C W HW u v (tp_rel_to_sum u v Huv) Wu).
Defined.

Definition tp_from_sum : Sum_Top B C ~{Top}~> Pushout_Top Ef Eg.
Proof using All.
  unshelve refine (Build_ContinuousMorphism
                     (Sum_Top B C) (Pushout_Top Ef Eg) tp_from_sum_map _).
  intros W HW.
  exact (fst (snd HW), snd (snd HW)).
Defined.

(*
 An isomorphism in Top.  Both legs have [fun u => u] as their underlying
 function, so each composite is the identity function and the two
 coherence obligations close by reflexivity of the target setoid. 

 --------
 在拓扑学中的同构。两条箭头的底层函数都是 [fun u => u]，因此每个复合都是恒等函数，并且两个相干性义务通过目标集合的自反性而成立。
*)
Definition Top_pushout_empty_iso : Pushout_Top Ef Eg ≅[Top] Sum_Top B C.
Proof using All.
  unshelve refine {| to := tp_to_sum; from := tp_from_sum |}.
  - intro u; apply Equivalence_Reflexive.
  - intro u; apply Equivalence_Reflexive.
Defined.

End EmptySpanIsCoproduct.
