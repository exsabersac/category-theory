Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Displayed categories / * 显示的范畴 *)

(*
nLab:      https://ncatlab.org/nlab/show/displayed+category
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, "Displayed
              Categories", Logical Methods in Computer Science 15(1), 2019.
              https://arxiv.org/abs/1705.04296

   A displayed category [D] over a base category [C] assigns to each object
   [x : C] a type [dobj x] of objects lying over [x], and to each base
   morphism [f : x ~> y] and displayed objects [dx : dobj x], [dy : dobj y] a
   setoid [dhom dx dy f] of morphisms lying over [f], together with displayed
   identities lying over [id] and displayed composition lying over [∘]. This
   is the Coq-friendly primitive presentation of fibred/indexed category
   theory: the total category [∫ D] (Construction/Displayed/Total.v) has
   pairs [(x; dx)] as objects and pairs [(f; ff)] as morphisms, and a
   displayed category is exactly the data making that total assembly a
   category, packaged without ever comparing objects of [C] for equality.

   Because homs in this library are setoids, the family [dhom dx dy] is
   indexed by base morphisms that are only ever compared up to [≈], so the
   family must itself cohere across [≈]. That coherence is [dtransport]:
   along every proof [e : f ≈ g] a map
   [dtransport e : dhom dx dy f → dhom dx dy g] which respects [≈]
   ([dtransport_respects]), is functorial ([dtransport_trans]), and is
   proof-irrelevant ([dtransport_id]: transport along any proof of [f ≈ f]
   is the identity up to [≈]; combined with functoriality this yields
   irrelevance along arbitrary parallel proofs, [dtransport_proof_irrel]
   below). The displayed unit and associativity laws are then stated over
   the corresponding base laws by transporting one side along them.

   Interface note (a disclosed strengthening of the Phase 10 skeleton). The
   interchange of transport with displayed composition,

     dcomp (dtransport e ff) gg ≈ dtransport e' (dcomp ff gg)
     dcomp ff (dtransport e gg) ≈ dtransport e' (dcomp ff gg),

   is not derivable from the other fields, so it is part of the interface as
   [dtransport_comp_l]/[dtransport_comp_r]. Underivability: take the base to
   be the one-object category with hom-monoid (ℤ, +, 0) and with [f ≈ g]
   meaning congruence modulo 2; display over it the constant family
   [dhom _ _ f := ℤ] under [eq], with [dtransport e] the identity map,
   [did := 0], and with displayed composition over outer base [f] and inner
   base [g] given by [(k, l) ↦ k + l + f·g]. Since [f·g] is bilinear (a
   2-cocycle on ℤ vanishing when either argument is 0), every other field
   below holds in this model; yet with outer bases [e : 0 ≈ 2] and inner
   base [1], the left-hand side of the interchange computes over (2, 1) to
   [0 + 0 + 2·1 = 2] while the right-hand side computes over (0, 1) to
   [0 + 0 + 0·1 = 0], and [2 ≠ 0] in the strict fibre (ℤ, eq). These two
   fields are load-bearing, not mere convenience: without them the derived
   [dtransport_dcomp] (below), and hence the total category's [compose_respects]
   (Construction/Displayed/Total.v), cannot be proved — in the same model the
   [∫D]-morphisms [(base 0; 0)] and [(base 2; 0)] are equal, yet post-composing
   each with [(base 1; 0)] gives [(base 1; 0)] and [(base 3; 2)], which are
   unequal (bases agree mod 2 but the displayed parts [0] and [2] differ under
   [eq]), so total composition would not respect [≈] and [∫D] would not be a
   category; the interface must not be trimmed back to the bare skeleton. The
   composite-side proof [e'] is universally quantified rather than pinned to
   the canonical [compose_respects] witness: by proof-irrelevance of
   [dtransport] the two phrasings are interderivable, and the quantified
   form spares consumers from massaging proof terms.

--------
nLab:      https://ncatlab.org/nlab/show/displayed+category
   Wikipedia: https://en.wikipedia.org/wiki/Displayed_category
   Reference: Ahrens–Lumsdaine, "Displayed Categories", LMCS 15(1), 2019
              https://arxiv.org/abs/1705.04296

   展示范畴 (displayed category) D 在基范畴 C 上：对每个对象 x : C 给出展示对象类型
   [dobj x]，对每个态射 f : x ~> y 与展示对象 dx、dy 给出展示态射类型
   [dhom dx dy f]，配备展示恒等与展示复合，服从单位与结合律（相对基态射的相应定律，
   经 setoid 等价）。总范畴 [Total D] 的对象是对 (x; dx)，态射是对 (f; ff)；投影
   [Total_Proj D : Total D ⟶ C] 忘掉展示数据。纤维化语言见 Theory/Fibration.v。
   本文件提供原语与总范畴构造；历史与用途见下一块注释（若仍为英文，属后续波次）。
*)

(*
Where displayed categories come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/displayed+category
   Paper: Benedikt Ahrens, Peter LeFanu Lumsdaine, "Displayed
          Categories", Logical Methods in Computer Science 15(1), 2019
          (arXiv:1705.04296)

   The construction is due to Ahrens and Lumsdaine, who introduced it to
   give a type-theoretic account of a pervasive habit: building a new
   category by attaching data and properties to one that already exists
   (Ahrens, Lumsdaine 2019).  A displayed category over [C] carries the
   same information as a category [D] equipped with a functor into [C],
   only reorganized — the objects and morphisms of [D] are presented as
   families indexed over the objects and morphisms of [C], rather than as
   one collection with a projection down.  The header records the slogan
   that results, that the total category is assembled without ever
   comparing objects of [C] for equality; why that clause carries weight
   is the subject of what follows.

   Equality of objects is the obstruction the notion is designed to route
   around.  In intensional type theory, and in this setoid library, asking
   whether two objects of a category are equal is ill-behaved: it violates
   the principle of equivalence and supports no usable reasoning.  Yet the
   classical definitions of fibration, isofibration, and creation of limits
   each quantify over objects lying over a common base object, and phrased
   naively each such definition conceals an object-equality.  Displayed
   categories dissolve the difficulty at the level of typing: the fibre
   over [x] is the type [dobj x], indexed by [x] itself, so "two displayed
   objects over the same base object" is the statement that both inhabit
   [dobj x] — a typing fact, not an equation (Ahrens, Lumsdaine 2019;
   nLab).  The decisive case in the paper is the fibration, which invokes
   equality on objects when read as a functor with a lifting property but
   not when read as a displayed category with a cleaving, and almost every
   fibration arising in practice is of the second form.

   The reorganization repays itself in modularity.  Monoids internal to a
   category, algebras over their carriers, pointed objects over objects,
   bundles over a base space — each is an extra layer stacked on a base,
   and a displayed category is precisely that layer, with the total
   category recovering base-plus-layer.  One proves the layer a displayed
   category once, and the total category together with its forgetful
   projection follows.  The library uses this directly.  Theory/Fibration.v
   states fibrations in the displayed presentation ([DCartesian],
   [Cleaving], [ClovenFibration], [SplitCleaving]) beside the classical
   functorial one and bridges the two; Construction/Grothendieck.v builds
   [Grothendieck_Displayed] from the reindexing data of
   Construction/Indexed.v ([IndexedCat]) and sets [Grothendieck := Total
   Grothendieck_Displayed]; and Construction/Displayed/Codomain.v gives the
   codomain displayed category, where cartesian lifts coincide with
   pullbacks ([codomain_cleaving_pullbacks]).  The transport-groupoid
   discipline worked out here for [dtransport] is reused at the square level
   of Theory/DoubleCategory.v ([dsq_coerce]) and at the boundary casts of
   Theory/Multicategory.v ([mcast]).

   Read computationally, a displayed category is dependent data over a
   base.  An object [dx : dobj x] is a payload attached to each base object,
   a displayed morphism [dhom dx dy f] is that payload's behaviour along the
   base map [f], and the total category is the dependent sum: its objects
   are pairs [(x; dx)], its morphisms pairs [(f; ff)], and the projection to
   [C] forgets the payload.  Adding a displayed layer is thus adding fields
   to a record whose base already exists, the categorical form of a Σ-type
   with its first projection, which is why Ahrens and Lumsdaine frame the
   notion as how categories are built in practice.  The setoid coherence
   [dtransport] is the analogue of coercing a dependent value along a proof
   that two indices agree — here a proof [f ≈ g] of base morphisms — with
   proof-irrelevance rendering the coercion canonical (nLab).  Abstractly
   the same data is a normal lax functor from [C] into the bicategory of
   profunctors (Theory/Profunctor.v), whose factorizations recover discrete
   and Grothendieck (op)fibrations and Conduché functors (nLab).

   The originating material was itself formalized in Coq over the UniMath
   library (Ahrens, Lumsdaine 2019), where displayed categories have become
   the standard instrument for fibrations and univalent constructions, and
   where later work building on Ahrens and Lumsdaine extended the notion one
   dimension up, to displayed bicategories.

--------
显示的范畴来自何处以及它们的用途

nLab：https://ncatlab.org/nlab/show/displayed+category
 论文：Benedikt Ahrens、Peter LeFanu Lumsdaine，“显示
 范畴”，计算机科学中的逻辑方法 15(1)，2019
 （arXiv：1705.04296）

该建筑由 Ahrens 和 Lumsdaine 完成，他们将其介绍给
 给出一个普遍习惯的类型理论解释：建立一个新的
 通过将数据和属性附加到已存在的范畴
 （阿伦斯，拉姆斯丹，2019）。 [C] 上显示的范畴带有
 与配备函子的 [D] 范畴相同的信息进入 [C]，
 仅重新组织 - [D] 的对象和态射表示为
 系列根据 [C] 的对象和态射进行索引，而不是像
 一个投影向下的集合。 标题记录口号
 结果，整个范畴的组装无需
 比较 [C] 的对象是否相等； 为什么该条款有分量
 是下面的主题。

对象的平等是这个概念旨在路由的障碍
 周围。 在内涵类型理论中，在这个 setoid 库中，要求
 一个范畴的两个对象是否相等是不道德的：它违反了
 等价原则并且不支持任何可用的推理。 然而
 纤维化、等纤维化和极限创建的经典定义
 每个量化位于公共基础对象上的对象，并表述为
 每个这样的定义天真地隐藏了对象平等。 显示
 范畴解决了打字层面的困难：纤维
 [x] 上的类型是 [dobj x]，由 [x] 本身索引，因此“两个显示
 同一基础对象上的对象”是两者都居住的陈述
 [dobj x] — 一个打字事实，而不是一个方程式（Ahrens，Lumsdaine 2019；
 实验室）。 论文中的决定性案例是纤维化，它调用了
 当被读作具有提升属性的函子时，对象上的相等性但是
 不是当阅读为带有分裂的显示范畴时，几乎每个
 实践中出现的纤维化是第二种形式。

重组在模块化方面得到了回报。 a 内部的幺半群
 范畴、代数及其载体、指向对象的对象、
 捆绑在基础空间上——每个都是堆叠在基础上的额外层，
 显示的范畴正是该层，总计
 范畴恢复基础加层。 证明a层显示
 范畴一次，总范畴连同其健忘
 投影如下。 图书馆直接使用它。
理论/纤维化.v
 说明显示的演示文稿中的纤维振动（[DCartesian]，
 [Cleaving]、[ClovenFibration]、[SplitCleaving]）除了经典的
 功能一和桥梁两者； 构建/Grothendieck.v 构建
 [Grothendieck_Displayed] 来自重新索引数据
 Construction/Indexed.v ([IndexedCat]) 和集 [Grothendieck := Total
 格洛腾迪克_显示]； Construction/Displayed/Codomain.v 给出
 共域显示范畴，其中笛卡尔升力与
 回调（[codomain_cleaving_pullbacks]）。 运输类群
 此处为 [dtransport] 制定的规则在方形级别上重复使用
 Theory/DoubleCategory.v ([dsq_coerce]) 的边界转换
 理论/多范畴.v ([mcast])。

从计算角度来看，显示的范畴是依赖于
 基地。 对象 [dx : dobj x] 是附加到每个基础对象的有效负载，
 显示的态射 [dhom dx dy f] 是有效负载沿
 底图 [f]，总范畴是依赖和：其对象
 是 [(x; dx)] 对，其态射对 [(f; ff)]，以及投影
 [C] 忘记了有效负载。 添加显示层也就是添加字段
 对于基已经存在的记录，Σ 类型的分类形式
 与它的第一个投影，这就是为什么阿伦斯和卢姆斯丹框架
 范畴在实践中如何构建的概念。 集合相干性
 [dtransport] 类似于沿着证明强制依赖值
 两个索引一致——这里是基本态射的 [f ≈ g] 证明——
 证明无关性使强制强制成为规范（nLab）。 抽象地
 相同的数据是从 [C] 到二范畴的正常宽松函子
 profunctors (Theory/Profunctor.v)，其分解恢复离散
 和 Grothendieck (op) 纤维化和 Conduché 函子 (nLab)。

原始材料本身在 Coq 中通过 UniMath 形式化
 图书馆（Ahrens，Lumsdaine 2019），其中显示的范畴已成为
 纤维化和单价结构的标准仪器，以及
 后来在 Ahrens 和 Lumsdaine 的基础上进行的工作扩展了这一概念
 向上维度，以显示二类。
*)

Class Displayed (C : Category) := {
  dobj : C → Type;

  dhom {x y} : dobj x → dobj y → (x ~> y) → Type;

  dhomset {x y} (dx : dobj x) (dy : dobj y) (f : x ~> y) :
    Setoid (dhom dx dy f);

  dtransport {x y} {dx dy} {f g : x ~> y} (e : f ≈ g) :
    dhom dx dy f → dhom dx dy g;

  dtransport_respects {x y dx dy} {f g : x ~> y} (e : f ≈ g) :
    Proper (equiv ==> equiv) (@dtransport x y dx dy f g e);

  (* Proof irrelevance: transport along a loop is the identity. / 证明无关性：沿环上的传输是恒等映射。 *)
  dtransport_id {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
    (e : f ≈ f) (ff : dhom dx dy f) :
    dtransport e ff ≈ ff;

  dtransport_trans {x y} {dx : dobj x} {dy : dobj y} {f g h : x ~> y}
    (e1 : f ≈ g) (e2 : g ≈ h) (ff : dhom dx dy f) :
    dtransport e2 (dtransport e1 ff)
      ≈ dtransport (Equivalence_Transitive _ _ _ e1 e2) ff;

  did {x} (dx : dobj x) : dhom dx dx id;

  dcomp {x y z} {dx dy dz} {f : y ~> z} {g : x ~> y} :
    dhom dy dz f → dhom dx dy g → dhom dx dz (f ∘ g);

  dcomp_respects {x y z} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f : y ~> z} {g : x ~> y} :
    Proper (equiv ==> equiv ==> equiv) (@dcomp x y z dx dy dz f g);

  (*
Interchange of transport with displayed composition, on either side
     (see the interface note above for why these are structure, not
     consequences).

--------
对可 我听说你提供资源的 我们会在
ح发扬光心, 怎么是 在这里为推动人类的幸福 真的吗 我们现在
后果)。 这个定义。
*)
  dtransport_comp_l {x y z} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f f' : y ~> z} {g : x ~> y} (e : f ≈ f') (e' : f ∘ g ≈ f' ∘ g)
    (ff : dhom dy dz f) (gg : dhom dx dy g) :
    dcomp (dtransport e ff) gg ≈ dtransport e' (dcomp ff gg);

  dtransport_comp_r {x y z} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f : y ~> z} {g g' : x ~> y} (e : g ≈ g') (e' : f ∘ g ≈ f ∘ g')
    (ff : dhom dy dz f) (gg : dhom dx dy g) :
    dcomp ff (dtransport e gg) ≈ dtransport e' (dcomp ff gg);

  did_left {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
    (ff : dhom dx dy f) :
    dcomp (did dy) ff ≈ dtransport (symmetry (id_left f)) ff;

  did_right {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
    (ff : dhom dx dy f) :
    dcomp ff (did dx) ≈ dtransport (symmetry (id_right f)) ff;

  dcomp_assoc {w x y z}
    {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
    {f : y ~> z} {g : x ~> y} {h : w ~> x}
    (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
    dcomp ff (dcomp gg hh)
      ≈ dtransport (symmetry (comp_assoc f g h)) (dcomp (dcomp ff gg) hh)
}.
#[export] Existing Instance dhomset.   (* mirrors homset's registration / 镜像 homset 的注册 *)
#[export] Existing Instance dtransport_respects.  (* mirrors compose_respects / 镜子 组成_尊重 *)
#[export] Existing Instance dcomp_respects.

(**
** The derived transport lemma pack

    Everything below is a consequence of the class fields. These lemmas are
    budgeted here deliberately: the associativity and unit proofs for the
    total category (Construction/Displayed/Total.v) spend all of their time
    reorienting and cancelling transports, and each step is one of the
    lemmas in this pack.

--------
** 派生传输引理包

以下所有内容都是类字段的结果。这些引理故意在这里列出：总范畴（Construction/Displayed/Total.v）的结合性和单位性证明几乎全部时间都用于重新定向和消去传输，而每一步都是这个引理包中的一个引理。
*)

Section DisplayedTransport.

Context {C : Category}.
Context {D : Displayed C}.

(* Transporting there and back again cancels (left orientation). / 往返运输会取消（左侧方向）。 *)
Lemma dtransport_symm_l {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e : f ≈ g) (ff : dhom dx dy f) :
  dtransport (symmetry e) (dtransport e ff) ≈ ff.
Proof.
  rewrite dtransport_trans; apply dtransport_id.
Qed.

(* Transporting back and there again cancels (right orientation). / 来回运输会取消（正确方向）。 *)
Lemma dtransport_symm_r {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e : f ≈ g) (gg : dhom dx dy g) :
  dtransport e (dtransport (symmetry e) gg) ≈ gg.
Proof.
  rewrite dtransport_trans; apply dtransport_id.
Qed.

(*
Reorienting a transport equation: a transport may be moved to the other
   side of [≈] by inverting the proof it rides on.

--------
重新定向传输方程：可以通过反转其依托的证明，将传输移动到 [≈] 的另一侧。
*)
Lemma dtransport_flip {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e : f ≈ g) (ff : dhom dx dy f) (gg : dhom dx dy g) :
  dtransport e ff ≈ gg ↔ ff ≈ dtransport (symmetry e) gg.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply dtransport_symm_l.
  - rewrite H.
    apply dtransport_symm_r.
Qed.

(*
Transport does not depend on the proof transported along: the groupoid
   laws [dtransport_id]/[dtransport_trans] force any two parallel proofs to
   transport identically.

--------
运输并不依赖于随之运输的证明：群族定律 [dtransport_id]/[dtransport_trans] 强制任何两个平行的证明以相同的方式进行运输。
*)
Lemma dtransport_proof_irrel {x y : C} {dx : dobj x} {dy : dobj y}
  {f g : x ~> y} (e e' : f ≈ g) (ff : dhom dx dy f) :
  dtransport e ff ≈ dtransport e' ff.
Proof.
  apply (snd (dtransport_flip e ff (dtransport e' ff))).
  symmetry; rewrite dtransport_trans; apply dtransport_id.
Qed.

(*
[dtransport_trans] with the composite proof replaced by any proof of the
   endpoints' relation.

--------
[dtransport_trans]，复合证明被任何关于端点关系的证明所替代。
*)
Lemma dtransport_trans_any {x y : C} {dx : dobj x} {dy : dobj y}
  {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h) (e3 : f ≈ h)
  (ff : dhom dx dy f) :
  dtransport e2 (dtransport e1 ff) ≈ dtransport e3 ff.
Proof.
  rewrite dtransport_trans; apply dtransport_proof_irrel.
Qed.

(*
Congruence of displayed composition under transport in both arguments at
   once; the two interchange fields, fused.

--------
在两个参数中同时运输时显示的组合的一致性；两个交换场融合在一起。
*)
Lemma dtransport_dcomp {x y z : C} {dx : dobj x} {dy : dobj y} {dz : dobj z}
  {f f' : y ~> z} {g g' : x ~> y} (e1 : f ≈ f') (e2 : g ≈ g')
  (e' : f ∘ g ≈ f' ∘ g') (ff : dhom dy dz f) (gg : dhom dx dy g) :
  dcomp (dtransport e1 ff) (dtransport e2 gg) ≈ dtransport e' (dcomp ff gg).
Proof.
  rewrite (dtransport_comp_l e1
             (compose_respects f f' e1 g' g' (Equivalence_Reflexive g'))).
  rewrite (dtransport_comp_r e2
             (compose_respects f f (Equivalence_Reflexive f) g g' e2)).
  apply dtransport_trans_any.
Qed.

(*
The unit laws in transported orientation, along any proof of the base
   law: exactly the shape of the total category's unit obligations.

--------
在运输方向上的单位律，沿着基律的任何证明：完全是总范畴的单位义务的形状。
*)
Lemma dtransport_did_left {x y : C} {dx : dobj x} {dy : dobj y}
  {f : x ~> y} (e : id ∘ f ≈ f) (ff : dhom dx dy f) :
  dtransport e (dcomp (did dy) ff) ≈ ff.
Proof.
  rewrite did_left, dtransport_trans; apply dtransport_id.
Qed.

Lemma dtransport_did_right {x y : C} {dx : dobj x} {dy : dobj y}
  {f : x ~> y} (e : f ∘ id ≈ f) (ff : dhom dx dy f) :
  dtransport e (dcomp ff (did dx)) ≈ ff.
Proof.
  rewrite did_right, dtransport_trans; apply dtransport_id.
Qed.

(*
Associativity in transported orientation, along any proof of the base
   law, in both directions (matching [comp_assoc]/[comp_assoc_sym]).

--------
在传递的方向上，在基律的任意证明过程中，两种方向上（匹配 [comp_assoc]/[comp_assoc_sym]）的结合性。
*)
Lemma dtransport_dcomp_assoc {w x y z : C}
  {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h)
  (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
  dtransport e (dcomp ff (dcomp gg hh)) ≈ dcomp (dcomp ff gg) hh.
Proof.
  rewrite dcomp_assoc, dtransport_trans; apply dtransport_id.
Qed.

Lemma dtransport_dcomp_assoc_sym {w x y z : C}
  {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
  {f : y ~> z} {g : x ~> y} {h : w ~> x}
  (e : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h))
  (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
  dtransport e (dcomp (dcomp ff gg) hh) ≈ dcomp ff (dcomp gg hh).
Proof.
  rewrite dcomp_assoc; apply dtransport_proof_irrel.
Qed.

End DisplayedTransport.
