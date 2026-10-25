Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * The category of pointed sets / * 指向集合的类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/pointed+set
 nLab:      https://ncatlab.org/nlab/show/pointed+object
 Wikipedia: https://en.wikipedia.org/wiki/Pointed_set
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer 1998, §I.7 (printed p. 26)
 Book:      Awodey, "Category Theory", 2nd ed., OUP 2010, §1.6 Example 1.8
 (printed p. 19)
 Book:      Awodey, "Category Theory", 1st ed., OUP 2006, §7.9 Example 7.26

 This is Set_*, Mac Lane's category of pointed sets, built over the setoids
 of Instance/Sets.v.  An object is a Bishop set with a distinguished element
 and an arrow is a map carrying the distinguished element to the
 distinguished element:

 objects: pointed setoids       (carrier + `≈` + a basepoint [pt])
 arrows: pointed setoid maps   (setoid maps with f (pt X) ≈ pt Y)
 hom-setoid: f ≈ g  :=  ∀ x, f x ≈ g x   (as in [Sets]: pointwise, up to `≈`)
 identity: the identity setoid map
 composition: composition of setoid maps — the basepoint travels through both

 Mac Lane introduces Set_* in §I.7 alongside the observation that makes it
 worth having: the one-point set is at once initial and terminal in it, so
 Set_* has a null object, whereas Set itself does not (Mac Lane 1998, §I.7).
 [PointedSets_Zero] is that remark, in the [ZeroObject] form of
 Structure/ZeroObject.v; the zero morphism it induces is the constant map at
 the basepoint, [pointed_const] here.  A zero object is exactly what the
 additive-structure vocabulary of Structure/Preadditive.v and
 Structure/Kernel.v presupposes — kernels and cokernels are stated relative
 to zero morphisms — and Set_* supplies one with no addition on the homsets
 whatsoever, in contrast with the commutative monoids of Instance/CMon.v.
 More generally a pointed object in a category with a terminal object is an
 object under 1 (nLab, "pointed object"), and Set_* is the case C = Set.
 Awodey uses the same category as a first example of a category of
 structured sets and structure-preserving maps (Awodey 2010, §1.6 Example
 1.8), and returns to it for the coslice reading recorded in
 Instance/Sets/Pointed/Coslice.v (Awodey 2006, §7.9 Example 7.26).

 Structurally, pointed sets sit at three crossings the library already
 touches.  They are the coslice of Set under the one-point set, the theorem
 of Instance/Sets/Pointed/Coslice.v turning the prose of
 Construction/Slice.v's header into a [≅[Cat]].  They are the algebras of
 the maybe monad: an algebra structure option A → A is forced to be the
 identity on [Some], so it amounts to nothing more than a choice of point,
 while Instance/Sets/Par.v's [Part] is the Kleisli category of the same
 monad.  Instance/Sets/Pointed/Part.v builds the comparison between the two
 directly and proves it an equivalence over a decidability hypothesis —
 whose content is that in the decidable case every algebra is free — which
 upgrades the claim made in the header of Instance/Coq/Par.v.  (The
 identification of that concrete functor with the Eilenberg–Moore comparison
 of Monad/Comparison.v is not formalized here.)  And, in the classical
 setting, pointed sets carry the smash product, making Set_* the prototype
 of a monoidal-but-not-cartesian category of "sets with a zero" (nLab,
 "pointed set"); the smash product is not developed here. 

 --------
 nLab：       https://ncatlab.org/nlab/show/pointed+set
 nLab：       https://ncatlab.org/nlab/show/pointed+object
 维基百科：  https://en.wikipedia.org/wiki/Pointed_set
 书籍：      Mac Lane，《工作数学家的范畴论》，第2版，斯普林格 1998，第I.7节（印刷页26）
 书籍：      Awodey，《范畴论》，第2版，牛津大学出版社 2010，第1.6节 示例1.8（印刷页19）
 书籍：      Awodey，《范畴论》，第1版，牛津大学出版社 2006，第7.9节 示例7.26

 这是Set_*，Mac Lane的指点集范畴，建立在Instance/Sets.v的集合类上。一个对象是带有特定元素的Bishop集合，箭头是将特定元素映射到特定元素的映射：对象：有基点的集类（载体 + `≈` + 基点 [pt]）
 箭头：有基点的集类映射（集类映射，满足 f(pt X) ≈ pt Y）
 同集类：f ≈ g := ∀ x, f x ≈ g x（如 [Sets] 所示：逐点比较，直到 `≈`）
 恒等映射：恒等集类映射
 复合：集类映射的复合 — 基点会通过两者传递Mac Lane 在 §I.7 中引入了 Set_*，同时指出了它值得拥有的原因：单元素集在其中既是初始的又是终端的，因此 Set_* 有一个零对象，而 Set 本身没有（Mac Lane 1998, §I.7）。[PointedSets_Zero] 是这一注释，在 Structure/ZeroObject.v 的 [ZeroObject] 形式中；它所诱导的零态射是基点处的恒等映射，[pointed_const] 在此。零对象正是 Structure/Preadditive.v 和 Structure/Kernel.v 的加法结构词汇所预设的——核和余核都是相对于零态射来说明的——而 Set_* 提供了一个零对象，但在 Hom 集上完全没有加法，这与 Instance/CMon.v 的交换幺半群形成对比。更一般地说，一个具有终对象的范畴中的带点对象是一个 1 下的对象（nLab，“带点对象”），而 Set_* 是 C = Set 的情况。Awodey 使用相同的范畴作为结构化集合及结构保持映射范畴的第一个例子（Awodey 2010，第1.6节 例1.8），并在 Instance/Sets/Pointed/Coslice.v 中返回它以进行余切读（Awodey 2006，第7.9节 例7.26）。从结构上看，尖点集合位于库已经涉及到的三个交叉点。它们是单点集合下的集合余切片，Instance/Sets/Pointed/Coslice.v 的定理将 Construction/Slice.v 头部的文字转换为 [≅[Cat] ]。它们是 maybe monad 的代数：一个代数结构 option A → A 必然在 [Some] 上是恒等的，因此它无非就是选择一个点，而 Instance/Sets/Par.v 的 [Part] 是同一个 monad 的 Kleisli 范畴。Instance/Sets/Pointed/Part.v 直接建立了两者之间的比较，并在可判定性假设下证明它是等价的——其内容是，在可判定的情况下，每个代数都是自由的——这提升了 Instance/Coq/Par.v 头部所作的声明。（在这里并未形式化将该具体函子与 Monad/Comparison.v 的 Eilenberg–Moore 比较相识别。）而在经典语境中，有基点的集合具有压扁积，使得 Set_* 成为“带零集合”的单体范畴但非笛卡尔范畴的原型（nLab，“有基点的集合”）；这里未展开压扁积的内容。
*)

(*
 The constructive ledger of this development

 nLab:      https://ncatlab.org/nlab/show/axiom+of+choice
 nLab:      https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

 Mac Lane's §I.7 discussion of Set_* is not only about the null object; the
 accompanying proposition is the standard dictionary between the elementary
 and the arrow-theoretic descriptions of injections and surjections, and in
 Set it reads: monic ⟺ injective, epic ⟺ surjective, every monic with
 non-empty domain splits, every epic splits.  Formalizing it constructively
 separates the four claims sharply, and the separation is the mathematical
 content of this file rather than a formalization artefact.  What holds
 here, and at what price:

 - [pointed_monic_iff] : monic ⟺ injective.  UNCONDITIONAL.  The hard
 direction probes with the two-point pointed set [PointedTwo]; the
 singleton, which is Set's probe, is here the zero object and detects
 nothing, so the smallest useful probe has exactly one free point.

 - [pointed_epic_iff] : epic ⟺ surjective.  UNCONDITIONAL — no
 decidability, no choice.  The witness is the pointed cokernel pair
 [PointedCP]: two copies of the codomain glued along the image, with the
 gluing relation given in CLOSED FORM rather than as the transitive
 closure of a generating relation, so no quotient machinery is required.
 The two basepoints are identified because [preserves_pt] puts the
 basepoint in the image ([InImage_pt]), which is exactly what makes both
 legs pointed.  Since `≈` is [Type]-valued, the surjectivity extracted
 from an epimorphism carries preimages as DATA, which is what lets the
 inverse below be assembled without choice.

 - [pointed_monic_split] : monic ⟹ split monic, under the explicit
 hypothesis [ImageDecidable] that membership in the image is decidable.
 The retraction sends a point of the image to its preimage — unique, by
 injectivity — and everything else to the basepoint.  Note that Mac Lane's
 side condition "non-empty domain" is automatic in Set_*: every object has
 a basepoint.

 - [pointed_epic_split] : epic ⟹ split epi, under an enumeration of the
 domain together with decidable `≈` on the codomain.  This is the honest
 price.  In Set the unrestricted statement "every epimorphism splits" IS
 the axiom of choice (nLab, "axiom of choice"; Wikipedia, "Axiom of
 choice"), so no hypothesis-free proof can exist.  The obstruction is
 visible at exactly one point: a section must be RESPECTFUL, and when [f]
 is not injective two `≈`-related points of the codomain can have entirely
 unrelated preimages.  The closing section of this file makes the price
 precise in-tree rather than by citation: dropping either splitting
 hypothesis yields informative excluded middle
 ([unconditional_monic_split_gives_IEM],
 [unconditional_epic_split_gives_IEM]).  A first-preimage search over a fixed enumeration
 removes it, because the index it selects depends on the argument only
 through its `≈`-class — [pointed_search_respects] proves this up to
 Leibniz equality, not merely up to `≈`.  The basepoint is special-cased,
 without which the section need not be a morphism of Set_* at all.

 - [pointed_balanced] : invertible ⟺ monic ∧ epic.  UNCONDITIONAL in both
 directions, and the pleasant surprise of the file: although neither
 splitting result is available without hypotheses, their combination is.
 Injectivity from [pointed_monic_iff] makes the candidate inverse
 respectful and basepoint-preserving; surjectivity from
 [pointed_epic_iff], being data, supplies the function itself.  So Set_*
 is a balanced category constructively.

 Instance/Sets/Pointed/Finite.v discharges every hypothesis above at once
 for finite pointed sets with decidable equality, and exercises the results
 by computing a retraction and a section of concrete maps; it also exhibits
 a monic that is not epic and an epic that is not monic, so that
 [pointed_balanced] is not vacuous.  The satellite files are
 Instance/Sets/Pointed/Part.v (the equivalence with partial maps) and
 Instance/Sets/Pointed/Coslice.v (the coslice presentation). 

 --------
 这个发展的建设性账本

 nLab:       https://ncatlab.org/nlab/show/axiom+of+choice 
 nLab:       https://ncatlab.org/nlab/show/split+epimorphism 
 维基百科:   https://en.wikipedia.org/wiki/Axiom_of_choice 

 Mac Lane 的 §I.7 关于 Set_* 的讨论不仅仅是关于空对象；
 附带的命题是关于初等描述和箭头理论描述的单射与满射的标准词典，在 Set 中它表示：monic ⟺ 注射的，epic ⟺ 满射的，每个有非空定义域的 monic 可拆分，每个 epic 可拆分。将其以构造方式形式化明确地分开了这四个命题，这种分离是本文件的数学内容，而不是形式化的人工产物。这里成立的内容，以及其代价是：-  [pointed_monic_iff] ：单射 ⟺ 单射。无条件的。困难的方向通过两点标记集合 [PointedTwo] 探测；单元素集，作为 Set 的探针，在这里是零对象且无法探测任何东西，因此最小的有用探针恰好有一个自由点。-  [pointed_epic_iff] ：史诗性 ⟺ 满射。无条件 — 没有可判定性，没有选择。见证是指向余核对 [PointedCP] ：两个值域的副本沿着像粘合，粘合关系以闭合形式给出，而不是作为生成关系的传递闭包，因此不需要商构造。两个基点被识别，因为 [preserves_pt] 将基点放在像中（[InImage_pt]），这正是使两条腿都是指向的原因。由于 `≈` 是 [Type] 值的，从一个上同态中提取的满射性将前像作为数据携带，这正是使下面的逆映射能够在没有选择的情况下被组装的原因。- [pointed_monic_split]：单射 ⟹ 分裂单射，在明确的假设 [ImageDecidable] 下，即像中的元素的隶属关系是可判定的。  
 收缩映射将像中的点映射回它的原像——由单射性保证唯一——其他所有点映射到基点。  
 注意，Mac Lane 的附加条件“非空域”在 Set_* 中是自动满足的：每个对象都有一个基点。- [pointed_epic_split]：史诗 ⟹ 在定义域的枚举下分裂 epi，同时在值域上有可判定的 `≈`。这是真正的代价。在集合论中，无限制的陈述“每个上射都是可分裂的”就是选择公理（nLab，“选择公理”；维基百科，“选择公理”），所以不存在无假设的证明。障碍恰好在一个点上可见：一个截面必须是尊重的，而当 [f] 不是单射时，值域中两个 `≈` 相关的点可能有完全无关的原像。此文件的结尾部分以树内的方式而非引用的方式明确了代价：放弃任一分裂假设都会导致有信息的排中律（[unconditional_monic_split_gives_IEM]，[unconditional_epic_split_gives_IEM]）。在固定枚举上的一次原像搜索会将其移除，因为它选择的索引仅通过其 `≈` 类依赖于参数 — [pointed_search_respects] 将其证明到莱布尼茨相等，而不仅仅是到 `≈`。基点是特殊处理的，否则该截面根本不需要是 Set_* 的态射。

 - [pointed_balanced]：可逆 ⟺ 单射且满射。双向无条件，并且文件中令人愉快的惊喜是：尽管在没有假设的情况下无法得到任何分裂结果，但它们的组合却可以。从 [pointed_monic_iff] 得到的单射性使候选逆映射是尊重的并保持基点；从 [pointed_epic_iff] 得到的满射性，由于它是数据，提供了函数本身。因此，Set_* 是一个结构上平衡的范畴。Instance/Sets/Pointed/Finite.v 一次性解除上述所有假设，适用于具有可判定等式的有限指向集合，并通过计算具体映射的重traction和截面来练习结果；它还展示了一个单态但非满态的映射和一个满态但非单态的映射，因此 [pointed_balanced] 并非空置。卫星文件包括 Instance/Sets/Pointed/Part.v（与部分映射的等价性）和 Instance/Sets/Pointed/Coslice.v（余片表示法）。
*)

(* A pointed setoid: a Bishop set together with a distinguished element. / 一个有尖点的集：一个Bishop集合以及一个指定的元素。 *)
Record PointedSetoid := {
  pointed_setoid :> SetoidObject;
  pt : carrier pointed_setoid
}.

(* A pointed map: a setoid map that carries the basepoint to the basepoint. / 有尖点的映射：一种把基点映射到基点的等价集映射。 *)
Record PointedMorphism (X Y : PointedSetoid) := {
  pointed_map :> SetoidMorphism (pointed_setoid X) (pointed_setoid Y);
  preserves_pt : pointed_map (pt X) ≈ pt Y
}.

Arguments pointed_map {X Y} _.
Arguments preserves_pt {X Y} _.

#[local] Obligation Tactic := idtac.

(*
 The hom-setoid: two pointed maps agree when their underlying setoid maps
 agree pointwise, exactly as in [Sets]. 

 --------
 同态集合：当它们的基础集合等价映射在每个点上都一致时，两个有基点的映射就被认为是一致的，正如在 [Sets] 中所示。
*)
#[export]
Program Instance PointedMorphism_Setoid {X Y : PointedSetoid} :
  Setoid (PointedMorphism X Y) := {|
  equiv := fun f g => ∀ x, pointed_map f x ≈ pointed_map g x
|}.
Next Obligation.
  intros X Y.
  constructor.
  - intros f x.
    reflexivity.
  - intros f g Hfg x.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh x.
    transitivity (pointed_map g x).
    + apply Hfg.
    + apply Hgh.
Qed.

(* The identity pointed map. / 恒等映射。 *)
Program Definition pointed_id {X : PointedSetoid} : PointedMorphism X X := {|
  pointed_map := setoid_morphism_id
|}.
Next Obligation.
  intros X; simpl.
  reflexivity.
Qed.

(* Composition of pointed maps: the basepoint travels through both. / 尖点映射的组合：基点同时通过两个映射。 *)
Program Definition pointed_compose {X Y Z : PointedSetoid}
        (f : PointedMorphism Y Z) (g : PointedMorphism X Y) :
  PointedMorphism X Z := {|
  pointed_map := setoid_morphism_compose (pointed_map f) (pointed_map g)
|}.
Next Obligation.
  intros X Y Z f g; simpl.
  unfold Basics.compose.
  rewrite (preserves_pt g).
  apply (preserves_pt f).
Qed.

Lemma pointed_compose_respects {X Y Z : PointedSetoid} :
  Proper (equiv ==> equiv ==> equiv) (@pointed_compose X Y Z).
Proof.
  intros f f' Hf g g' Hg x; simpl.
  unfold Basics.compose.
  rewrite (Hg x).
  apply Hf.
Qed.

(*
 The category of pointed sets, Mac Lane's Set_*.

 objects: pointed setoids            (a Bishop set with a basepoint)
 arrows: basepoint-preserving maps  (f (pt X) ≈ pt Y)
 identity: the identity setoid map
 composition: composition of setoid maps 

 --------
 尖点集合的范畴，Mac Lane 的 Set_*。

 对象：尖点集合类（带基点的Bishop集合）
 箭头：保持基点的映射（f (pt X) ≈ pt Y）
 恒等映射：恒等集合类映射
 复合：集合类映射的复合
*)
Program Definition PointedSets : Category := {|
  obj     := PointedSetoid;
  hom     := PointedMorphism;
  homset  := @PointedMorphism_Setoid;
  id      := @pointed_id;
  compose := @pointed_compose;

  compose_respects := @pointed_compose_respects
|}.
Next Obligation. intros X Y f x; simpl; reflexivity. Qed.
Next Obligation. intros X Y f x; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z W f g h x; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z W f g h x; simpl; reflexivity. Qed.

(* * ** The zero object: a single point, both initial and terminal / * ** 零对象：一个点，同时是初对象和终对象 *)

(*
 The one-point pointed set: [poly_unit] under `=`, pointed at its only
 element.  It plays both universal roles below. 

 --------
 单点指集合：[poly_unit] 在 `=` 下，指向它的唯一元素。它在下面扮演两个普遍角色。
*)
Definition PointedOne : PointedSetoid := {|
  pointed_setoid := {| carrier := poly_unit |};
  pt := ttt
|}.

(*
 The constant map at the codomain's basepoint.  It is pointed for the most
 trivial of reasons, and it is the zero morphism of [PointedSets]: it is
 simultaneously the unique map into the one-point set and the unique map out
 of it, which is what makes that object a null object. 

 --------
 在值域基点处的常量映射。它被称为指向映射是最平凡的原因，并且它是 [PointedSets] 的零态射：它同时是唯一进入单点集的映射以及唯一从单点集出的映射，这正是使该对象成为零对象的原因。
*)
Program Definition const_pt_map (X Y : PointedSetoid) :
  SetoidMorphism (pointed_setoid X) (pointed_setoid Y) := {|
  morphism := fun _ => pt Y
|}.
Next Obligation. intros X Y; proper. Qed.

Definition pointed_const {X Y : PointedSetoid} : PointedMorphism X Y.
Proof.
  refine (Build_PointedMorphism X Y (const_pt_map X Y) _).
  simpl.
  reflexivity.
Defined.

(*
 Into the one-point set there is exactly one map: everything goes to the
 only element, which is that object's basepoint. 

 --------
 到单点集只有一个映射：所有元素都映射到唯一元素，即该对象的基点。
*)
Definition pointed_one {X : PointedSetoid} : PointedMorphism X PointedOne :=
  @pointed_const X PointedOne.

Lemma pointed_one_unique {X : PointedSetoid}
  (f g : PointedMorphism X PointedOne) : f ≈ g.
Proof.
  intro x.
  (* [simpl] first: it keeps the goal's universes from being minimized to [Set] when the [poly_unit] elimination below is elaborated. / [simpl] 首先：它防止目标的宇宙在下面的 [poly_unit] 消除展开时被最小化为 [Set]。 *)
  simpl.
  destruct (pointed_map f x), (pointed_map g x).
  reflexivity.
Qed.

Definition PointedSets_Terminal : @Terminal PointedSets :=
  @Build_Terminal PointedSets PointedOne
    (fun X => @pointed_one X) (fun X => @pointed_one_unique X).

(*
 Out of the one-point set there is also exactly one map, and this is where
 pointedness bites: the single element IS the basepoint, so its image is
 forced to be the codomain's basepoint.  In [Sets] the singleton is only
 terminal; in [PointedSets] it is initial as well. 

 --------
 在单点集合中，也恰好有一个映射，这正是指向性起作用的地方：这个单一元素就是基点，因此它的像被迫成为陪域的基点。在 [Sets] 中，单集只是终端对象；在 [PointedSets] 中，它也是初始对象。
*)
Definition pointed_zero {X : PointedSetoid} : PointedMorphism PointedOne X :=
  @pointed_const PointedOne X.

Lemma pointed_zero_unique {X : PointedSetoid}
  (f g : PointedMorphism PointedOne X) : f ≈ g.
Proof.
  intro u.
  simpl.
  destruct u.
  transitivity (pt X).
  - exact (preserves_pt f).
  - symmetry.
    exact (preserves_pt g).
Qed.

Definition PointedSets_Initial : @Initial PointedSets :=
  @Build_Terminal (PointedSets^op) PointedOne
    (fun X => @pointed_zero X) (fun X => @pointed_zero_unique X).

(*
 Mac Lane's null object (CWM §I.7): the same one-point set is initial and
 terminal, so the coincidence isomorphism is the identity.  Consequently
 every hom-setoid of [PointedSets] has a distinguished zero morphism, the
 constant map at the basepoint (Structure/ZeroObject.v's [zero_mor]). 

 --------
 麦克·莱恩的零对象 (CWM §I.7)：同一个单点集既是初始的又是终端的，因此重合同构是恒等的。因此，[PointedSets] 的每个 Hom-集合都具有一个特殊的零态射，即基点处的常值映射（Structure/ZeroObject.v 的 [zero_mor]）。
*)
#[export] Instance PointedSets_Zero : ZeroObject PointedSets :=
  @Build_ZeroObject PointedSets PointedSets_Terminal PointedSets_Initial iso_id.

(* * ** Images, injections and surjections / * ** 图像、单射和满射 *)

(* [f] is injective when it separates points up to `≈`. / 当 [f] 将点分开到 `≈` 时，它是单射的。 *)
Definition PointedInjective {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ a b : carrier X, f a ≈ f b → a ≈ b.

(* Membership of [y] in the image of [f]. Because `≈` is [Type]-valued, this is a [sigT] and therefore carries the preimage as data: no choice principle is needed to extract it later. / [y] 在 [f] 的像中的成员。因为 `≈` 是 [Type] 值的，因此这是一个 [sigT]，因此携带原像作为数据：以后提取它不需要选择原则。 *)
Definition InImage {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (y : carrier Y) : Type :=
  ∃ x : carrier X, f x ≈ y.

(* [f] is surjective when every point of the codomain is in its image. / 当陪域中的每个点都在其像中时，[f] 是满射的。 *)
Definition PointedSurjective {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ b : carrier Y, InImage f b.

(* Image membership is a property of the `≈`-class, not of the representative: the same preimage witnesses membership of any equivalent point. / 图像成员资格是 `≈` 类的一个属性，而不是代表元的属性：相同的原像证明了任何等价点的成员资格。 *)
Lemma InImage_respects {X Y : PointedSetoid} (f : PointedMorphism X Y)
  {y y' : carrier Y} : y ≈ y' → InImage f y → InImage f y'.
Proof.
  intros Hyy [x Hx].
  exists x.
  now rewrite Hx.
Qed.

(*
 The basepoint is always in the image: [preserves_pt] IS a preimage
 witness.  This one line is what makes the cokernel-pair argument below
 respect basepoints, and what pins the retraction of a monic at the
 basepoint. 

 --------
 基点总是在像中：[preserves_pt] 是一个前像见证。 这一行正是使下面的余核对论证尊重基点的原因，也是固定单射在基点处的重traction的原因。
*)
Lemma InImage_pt {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  InImage f (pt Y).
Proof.
  exists (pt X).
  apply preserves_pt.
Qed.

(* * ** Monomorphisms are exactly the injections / * ** 单射正好是注入映射 *)

(*
 The two-point pointed set: [option poly_unit] pointed at [None].  It is the
 probe object for monomorphisms — a map out of it is precisely a choice of
 one free point of the target, the basepoint being forced.  (In [Sets] the
 singleton suffices; here the singleton is the zero object, so it detects
 nothing, and the smallest useful probe has one point to spare.) 

 --------
 两点指集合：[option poly_unit] 指向 [None]。它是单态的探针对象——从它出的映射恰好是选取目标的一个自由点，基点是固定的。（在 [Sets] 中，单点就足够了；而这里单点是零对象，因此无法探测任何东西，最小有用的探针必须多一个点。）
*)
Definition PointedTwo : PointedSetoid := {|
  pointed_setoid := {| carrier := option poly_unit |};
  pt := Datatypes.None
|}.

Program Definition probe_map {X : PointedSetoid} (x : carrier X) :
  SetoidMorphism (pointed_setoid PointedTwo) (pointed_setoid X) := {|
  morphism := fun o => match o with
                       | Datatypes.Some _ => x
                       | Datatypes.None => pt X
                       end
|}.
Next Obligation.
  intros X x; simpl; intros a b Hab.
  destruct a, b; simpl in *; try contradiction; reflexivity.
Qed.

(* The probe at [x]: basepoint to basepoint, free point to [x]. / 在 [x] 的探针：从基点到基点，自由点到 [x]。 *)
Definition pointed_probe {X : PointedSetoid} (x : carrier X) :
  PointedMorphism PointedTwo X.
Proof.
  refine (Build_PointedMorphism PointedTwo X (probe_map x) _).
  simpl.
  reflexivity.
Defined.

(*
 Mac Lane CWM §I.7: in Set_* the monomorphisms are exactly the injective
 maps.  Both directions are unconditional.  The hard direction feeds [f] the
 two probes at [a] and at [b]: they agree after [f], hence agree, hence
 a ≈ b at the free point. 

 --------
 Mac Lane CWM §I.7：在 Set_* 中，单态正好是单射映射。两个方向都是无条件的。困难的方向将两个探针送入 [f]：它们在 [a] 和 [b] 处一致；因此在 [f] 之后也一致，因此一致，因此在自由点处有 a ≈ b。
*)
Theorem pointed_monic_iff {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : PointedInjective f ↔ Monic f.
Proof.
  split.
  - intros Hinj.
    constructor; intros Z g1 g2 Hg z; simpl in *.
    apply Hinj.
    exact (Hg z).
  - intros [Hmonic] a b Hab.
    specialize (Hmonic PointedTwo (pointed_probe a) (pointed_probe b)).
    simpl in Hmonic.
    refine (Hmonic _ (Datatypes.Some ttt)).
    intros [u|]; simpl.
    + exact Hab.
    + reflexivity.
Qed.

(* * ** Epimorphisms are exactly the surjections / * ** 上同态正好是满射 *)

(*
 The pointed cokernel pair of [f].  The carrier is two copies of Y; the
 relation is given in closed form rather than as the transitive closure of a
 generating relation, which is what keeps the development free of any
 quotient machinery:

 inl a ~ inl b   iff   a ≈ b
 inr a ~ inr b   iff   a ≈ b
 inl a ~ inr b   iff   a ≈ b  and  a lies in the image of f

 In words: the two copies are glued exactly along the image of [f].  The
 basepoint is [inl (pt Y)] — and the OTHER basepoint [inr (pt Y)] is
 equivalent to it, because [preserves_pt] puts [pt Y] in the image
 ([InImage_pt]); this is precisely why the right leg below is a pointed
 map. 

 --------
 [f] 的尖对余核对。载体是两个 Y 的副本；关系以封闭形式给出，而不是作为生成关系的传递闭包，这正是保持开发过程不依赖任何商构造的原因：

 inl a ~ inl b   当且仅当   a ≈ b
 inr a ~ inr b   当且仅当   a ≈ b
 inl a ~ inr b   当且仅当   a ≈ b 且 a 位于 f 的像中

 用文字来说：这两个副本恰好沿 [f] 的像被粘合在一起。基点是 [inl (pt Y)] ——而另一个基点 [inr (pt Y)] 与它等价，因为 [preserves_pt] 将 [pt Y] 放入像中（[InImage_pt]）；这正是为什么下图右边的箭头是一个尖点映射的原因。
*)
Definition CP_rel {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (u v : carrier Y + carrier Y) : Type :=
  match u, v with
  | Datatypes.inl a, Datatypes.inl b => a ≈ b
  | Datatypes.inr a, Datatypes.inr b => a ≈ b
  | Datatypes.inl a, Datatypes.inr b => (a ≈ b) ∧ InImage f a
  | Datatypes.inr a, Datatypes.inl b => (a ≈ b) ∧ InImage f a
  end.

Program Definition CP_setoid {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Setoid (carrier Y + carrier Y) := {|
  equiv := CP_rel f
|}.
Next Obligation.
  intros X Y f.
  constructor.
  - intros [a|a]; simpl; reflexivity.
  - intros [a|a] [b|b]; simpl; intros H.
    + now symmetry.
    + destruct H as [Hab Him].
      split.
      * now symmetry.
      * exact (InImage_respects f Hab Him).
    + destruct H as [Hab Him].
      split.
      * now symmetry.
      * exact (InImage_respects f Hab Him).
    + now symmetry.
  - intros [a|a] [b|b] [c|c]; simpl; intros H1 H2.
    (* inl a ~ inl b ~ inl c / 在 a ~ 在 b ~ 在 c *)
    + now transitivity b.
    (* inl a ~ inl b ~ inr c: the image membership travels back along H1 / inl a ~ inl b ~ inr c：像的成员沿着 H1 返回 *)
    + destruct H2 as [Hbc Him].
      split.
      * now transitivity b.
      * exact (InImage_respects f (symmetry H1) Him).
    (* inl a ~ inr b ~ inl c / 在左 a ~ 在右 b ~ 在左 c *)
    + destruct H1 as [Hab _], H2 as [Hbc _].
      now transitivity b.
    (* inl a ~ inr b ~ inr c / 在左 a ~ 在右 b ~ 在右 c *)
    + destruct H1 as [Hab Him].
      split; [ now transitivity b | exact Him ].
    (* inr a ~ inl b ~ inl c / 在 a 内部 b 内部 c *)
    + destruct H1 as [Hab Him].
      split; [ now transitivity b | exact Him ].
    (* inr a ~ inl b ~ inr c / inr a ~ inl b ~ inr c *)
    + destruct H1 as [Hab _], H2 as [Hbc _].
      now transitivity b.
    (* inr a ~ inr b ~ inl c / 在 inr a ~ 在 inr b ~ 在 inl c *)
    + destruct H2 as [Hbc Him].
      split.
      * now transitivity b.
      * exact (InImage_respects f (symmetry H1) Him).
    (* inr a ~ inr b ~ inr c / 印度卢比 a ~ 印度卢比 b ~ 印度卢比 c *)
    + now transitivity b.
Qed.

Definition PointedCP {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  PointedSetoid := {|
  pointed_setoid := {| carrier := carrier Y + carrier Y
                     ; is_setoid := CP_setoid f |};
  pt := Datatypes.inl (pt Y)
|}.

(* The two legs of the cokernel pair. The left leg is pointed on the nose; the right leg is pointed because the two basepoints have been identified, which needs [InImage_pt]. / 余核对的两条腿。左腿在顶端是尖的；右腿是尖的，因为两个基点已经被识别，这需要 [InImage_pt]。 *)
Program Definition CP_left_map {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid (PointedCP f)) := {|
  morphism := fun y => Datatypes.inl y
|}.
Next Obligation. intros X Y f; simpl; intros a b Hab; exact Hab. Qed.

Program Definition CP_right_map {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid (PointedCP f)) := {|
  morphism := fun y => Datatypes.inr y
|}.
Next Obligation. intros X Y f; simpl; intros a b Hab; exact Hab. Qed.

Definition CP_left {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Y ~{PointedSets}~> PointedCP f.
Proof.
  refine (Build_PointedMorphism Y (PointedCP f) (CP_left_map f) _).
  simpl.
  reflexivity.
Defined.

Definition CP_right {X Y : PointedSetoid} (f : PointedMorphism X Y) :
  Y ~{PointedSets}~> PointedCP f.
Proof.
  refine (Build_PointedMorphism Y (PointedCP f) (CP_right_map f) _).
  simpl.
  split.
  - reflexivity.
  - apply InImage_pt.
Defined.

(*
 The two legs agree after [f]: every point of the form [f x] is in the image
 by definition, which is exactly the gluing condition. 

 --------
 在 [f] 之后，两条腿是一致的：形式为 [f x] 的每一个点根据定义都在映像中，这正是拼接条件。
*)
Lemma CP_coequalizes {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  CP_left f ∘ f ≈ CP_right f ∘ f.
Proof.
  intro x; simpl.
  split.
  - reflexivity.
  - exists x.
    reflexivity.
Qed.

(*
 An epimorphism of pointed sets is surjective.  Feed the cokernel pair to
 the cancellation property: the two legs become equal, and equality of the
 legs at [b] says precisely that [b] lies in the image.  No decidability and
 no choice enter — the image-membership witness is read straight off the
 relation. 

 --------
 一个带基点集合的满同态是满射。将余核对传入消去性质：两条箭头变得相等，而在  [b]  上两条箭头的相等性恰好说明  [b]  位于像中。无需可判定性，也无需选择——像成员的证明可以直接从关系中读出。
*)
Theorem pointed_epic_surjective {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Epic f → PointedSurjective f.
Proof.
  intros [Hepic] b.
  spose (Hepic (PointedCP f) (CP_left f) (CP_right f) (CP_coequalizes f) b)
    as Hb.
  exact (snd Hb).
Qed.

(* Mac Lane CWM §I.7: in Set_* the epimorphisms are exactly the surjective maps. Both directions are unconditional. / Mac Lane CWM §I.7：在 Set_* 中，满射正则态射恰好是满射映射。两个方向都是无条件的。 *)
Theorem pointed_epic_iff {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  PointedSurjective f ↔ Epic f.
Proof.
  split.
  - intros Hsurj.
    constructor; intros Z g1 g2 Hg b; simpl in *.
    destruct (Hsurj b) as [a Ha].
    rewrite <- Ha.
    exact (Hg a).
  - apply pointed_epic_surjective.
Qed.

(* * ** Mac Lane's Proposition (CWM §I.7): splitting, and balance / * ** 麦克·莱恩的命题 (CWM §I.7)：分裂和平衡 *)

(*
 The easy halves, valid in any category and proved here pointwise: a
 morphism with a left inverse is monic, one with a right inverse is epic. 

 --------
 容易的一半，在任何范畴中都是有效的，并且在这里逐点证明：具有左逆的态射是单射，具有右逆的态射是满射。
*)

Corollary pointed_split_monic_is_monic {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Section f → Monic f.
Proof.
  intros [r Hr].
  constructor; intros Z g1 g2 Hg z; simpl in *.
  transitivity (r (f (g1 z))).
  - symmetry.
    exact (Hr (g1 z)).
  - rewrite (Hg z).
    exact (Hr (g2 z)).
Qed.

Corollary pointed_split_epic_is_epic {X Y : PointedSetoid}
  (f : X ~{PointedSets}~> Y) : Retraction f → Epic f.
Proof.
  intros [s Hs].
  constructor; intros Z g1 g2 Hg b; simpl in *.
  transitivity (g1 (f (s b))).
  - now rewrite (Hs b).
  - rewrite (Hg (s b)).
    now rewrite (Hs b).
Qed.

(* * *** Monic implies split monic, given decidable image membership / * *** Monic 意味着分裂 monic，前提是图像成员资格可判定 *)

(*
 The hypothesis that makes the classical argument constructive: for each
 point of the codomain we may DECIDE whether it is hit.  Classically this is
 free; constructively it is exactly the missing content, and
 Instance/Sets/Pointed/Finite.v supplies it for every map out of a finitely
 enumerated pointed set into one with decidable `≈`. 

 --------
 使经典论证具有构造性的假设：对于陪域的每个点，我们可以决定它是否被命中。在经典逻辑中这是免费的；在构造逻辑中，这正是缺失的内容，而 Instance/Sets/Pointed/Finite.v 为从有限枚举的带基点集合到具有可判定 `≈` 的集合的每个映射提供了它。
*)
Definition ImageDecidable {X Y : PointedSetoid}
  (f : PointedMorphism X Y) : Type :=
  ∀ b : carrier Y, InImage f b + ¬ InImage f b.

(*
 The retraction: send a point of the image to its (unique, by injectivity)
 preimage, and everything else to the basepoint.  The basepoint of Y is
 never in the "everything else" branch — [InImage_pt] — so the retraction is
 automatically pointed. 

 --------
 收缩：将图像的一个点发送到其（通过单射唯一的）原像，其他所有点发送到基点。Y 的基点永远不在“其他所有点”分支中 —— [InImage_pt] —— 因此收缩自动是基于点的。
*)
Definition pointed_retract_fun {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (dec : ImageDecidable f) (b : carrier Y) :
  carrier X :=
  match dec b with
  | Datatypes.inl w => `1 w
  | Datatypes.inr _ => pt X
  end.

Program Definition pointed_retract_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (Hinj : PointedInjective f)
  (dec : ImageDecidable f) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := pointed_retract_fun f dec
|}.
Next Obligation.
  intros X Y f Hinj dec; simpl; intros b b' Hbb.
  unfold pointed_retract_fun.
  destruct (dec b) as [[a Ha]|n], (dec b') as [[a' Ha']|n']; simpl.
  - apply Hinj.
    rewrite Ha, Ha'.
    exact Hbb.
  - destruct (n' (InImage_respects f Hbb (a; Ha))).
  - destruct (n (InImage_respects f (symmetry Hbb) (a'; Ha'))).
  - reflexivity.
Qed.

Definition pointed_retract {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (Hinj : PointedInjective f) (dec : ImageDecidable f) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_retract_map f Hinj dec) _).
  simpl.
  unfold pointed_retract_fun.
  destruct (dec (pt Y)) as [[a Ha]|n]; simpl.
  - apply Hinj.
    rewrite Ha.
    symmetry.
    exact (preserves_pt f).
  - destruct (n (InImage_pt f)).
Defined.

(*
 Mac Lane's Proposition, first half: a monic pointed map splits, PROVIDED
 image membership is decidable.  The retraction is the one above; both of
 its laws are consequences of injectivity.  Ends in [Defined] because the
 retraction is DATA: Instance/Sets/Pointed/Finite.v evaluates it at concrete
 points by [reflexivity]. 

 --------
 Mac Lane 的命题，前半部分：一个单射指向的映射会分裂，前提是像的成员资格是可判定的。回缩映射就是上面的那个；它的两个定律都是单射性的结果。最终得到 [Defined]，因为回缩映射是数据：Instance/Sets/Pointed/Finite.v 通过 [reflexivity] 在具体点上进行计算。
*)
Theorem pointed_monic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (dec : ImageDecidable f) : Monic f → Section f.
Proof.
  intros Hm.
  pose proof (snd (pointed_monic_iff f) Hm) as Hinj.
  refine (@Build_Section PointedSets X Y f (pointed_retract f Hinj dec) _).
  intro a; simpl.
  unfold pointed_retract_fun.
  destruct (dec (f a)) as [[a' Ha']|n]; simpl.
  - now apply Hinj.
  - refine (False_rect _ (n _)).
    exists a.
    reflexivity.
Defined.

(* * *** Balance: invertible IS monic and epic, with no hypotheses at all / * *** 平衡：可逆的是单射且满射，并且没有任何假设 *)

(*
 The inverse of a bimorphism.  Injectivity supplies respectfulness (the
 witness attached to [b] is pinned by its value) and pointedness; the
 surjectivity witness supplies the function itself. 

 --------
 双态射的逆。单射性提供了尊重性（附加在 [b] 上的证人由其值固定）和指向性；满射性的证人提供了函数本身。
*)
Program Definition pointed_inverse_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (Hinj : PointedInjective f)
  (Hsurj : PointedSurjective f) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := fun b => `1 (Hsurj b)
|}.
Next Obligation.
  intros X Y f Hinj Hsurj; simpl; intros b b' Hbb.
  apply Hinj.
  rewrite (`2 (Hsurj b)), (`2 (Hsurj b')).
  exact Hbb.
Qed.

Definition pointed_inverse {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (Hinj : PointedInjective f) (Hsurj : PointedSurjective f) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_inverse_map f Hinj Hsurj) _).
  simpl.
  apply Hinj.
  rewrite (`2 (Hsurj (pt Y))).
  symmetry.
  exact (preserves_pt f).
Defined.

(*
 Mac Lane's Proposition, the balanced statement: in Set_* a map is
 invertible exactly when it is both monic and epic — and, in contrast with
 the two splitting results, this needs NO hypotheses.  The forward direction
 is formal; the converse assembles the inverse from the injectivity of a
 monic and the surjectivity of an epic, both established unconditionally
 above, the surjectivity witness being data rather than a mere existence
 claim. 

 --------
 麦克莱恩命题，这个平衡的陈述：在 Set_* 中，一个映射恰好在它既为单态又为满态时可逆——与两个分裂结果形成对比，这不需要任何假设。正向推理是形式化的；逆向推理则从单态的单射性和满态的满射性组装出逆映射，这两者在上文中都是无条件建立的，其中满射性证据是数据，而不仅仅是存在性声明。
*)
Theorem pointed_balanced {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y) :
  IsIsomorphism f ↔ (Monic f ∧ Epic f).
Proof.
  split.
  - intros [g Hfg Hgf].
    split.
    + apply (pointed_split_monic_is_monic f).
      exact (@Build_Section PointedSets X Y f g Hgf).
    + apply (pointed_split_epic_is_epic f).
      exact (@Build_Retraction PointedSets X Y f g Hfg).
  - intros [Hm He].
    pose proof (snd (pointed_monic_iff f) Hm) as Hinj.
    pose proof (pointed_epic_surjective f He) as Hsurj.
    refine (@Build_IsIsomorphism PointedSets X Y f
              (pointed_inverse f Hinj Hsurj) _ _).
    + intro b; simpl.
      exact (`2 (Hsurj b)).
    + intro a; simpl.
      apply Hinj.
      exact (`2 (Hsurj (f a))).
Qed.

(* * *** Epic implies split epic, given an enumeration and a decidable codomain / * *** 史诗意味着分裂史诗，给定一个枚举和值域可判定 *)

(* Decidability of `≈` on a pointed setoid. / 在带点集合上的 `≈` 的可判定性。 *)
Definition DecidableEquiv (Y : PointedSetoid) : Type :=
  ∀ y y' : carrier Y, (y ≈ y') + ¬ (y ≈ y').

(*
 Decidability of "is this the basepoint?", the weaker hypothesis needed by
 the essential-surjectivity argument of Instance/Sets/Pointed/Part.v. 

 --------
 “这是基点吗？”的可判定性，这是 Instance/Sets/Pointed/Part.v 的本质满射性论证所需的较弱假设。
*)
Definition DecidablePt (Z : PointedSetoid) : Type :=
  ∀ z : carrier Z, (z ≈ pt Z) + ¬ (z ≈ pt Z).

(* Membership in a list up to `≈`, [Type]-valued so that the position of the witness may be inspected. / 列表中的成员直到 `≈`，[Type] 值，以便可以检查见证人的位置。 *)
Fixpoint InSetoid {X : PointedSetoid}
  (x : carrier X) (l : list (carrier X)) : Type :=
  match l with
  | Datatypes.nil => False
  | Datatypes.cons a l' => (a ≈ x) + InSetoid x l'
  end.

(*
 An enumeration of a pointed setoid: a list meeting every `≈`-class.  This
 is the finiteness hypothesis; the [bool] witness of
 Instance/Sets/Pointed/Finite.v satisfies it. 

 --------
 一个带基地的集合类的枚举：一个包含每个 `≈` 类的列表。这是有限性假设；Instance/Sets/Pointed/Finite.v 中的 [bool] 证据满足它。
*)
Record PointedEnumeration (X : PointedSetoid) := {
  enum_list : list (carrier X);
  enum_covers : ∀ x : carrier X, InSetoid x enum_list
}.

Arguments enum_list {X} _.
Arguments enum_covers {X} _ _.

(*
 First-preimage search.  The KEY property is [pointed_search_respects]: the
 result depends on [b] only through its `≈`-class, and it does so up to
 Leibniz equality, not merely up to `≈`.  That is what makes the section
 below respectful — a bare choice of preimages need not be, since
 `≈`-related points can have wholly unrelated preimages when [f] is not
 injective, and this is precisely the obstruction that makes "every epi
 splits" a choice principle in general. 

 --------
 第一原像搜索。关键属性是 [pointed_search_respects]：结果仅通过 `≈` 类依赖于 [b]，并且这种依赖是到莱布尼茨等价，而不仅仅是到 `≈`。正因为如此，下面的部分是尊重的——单纯选择原像不一定是，因为当 [f] 不是单射时，`≈` 相关的点可能有完全无关的原像，而这正是导致“一切满射可拆分”通常只是一个选择原理的障碍。
*)
Fixpoint pointed_search {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y) :
  option (carrier X) :=
  match l with
  | Datatypes.nil => Datatypes.None
  | Datatypes.cons a l' =>
    match deq (f a) b with
    | Datatypes.inl _ => Datatypes.Some a
    | Datatypes.inr _ => pointed_search f deq l' b
    end
  end.

Lemma pointed_search_respects {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b b' : carrier Y) :
  b ≈ b' → pointed_search f deq l b = pointed_search f deq l b'.
Proof.
  intro Hbb.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - destruct (deq (f a) b) as [p|n], (deq (f a) b') as [p'|n'].
    + reflexivity.
    + destruct (n' (transitivity p Hbb)).
    + destruct (n (transitivity p' (symmetry Hbb))).
    + exact IH.
Qed.

Lemma pointed_search_correct {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y)
  (a : carrier X) :
  pointed_search f deq l b = Datatypes.Some a → f a ≈ b.
Proof.
  induction l as [|a0 l IH]; simpl.
  - intro H; discriminate.
  - destruct (deq (f a0) b) as [p|n].
    + intro H.
      injection H; intro Ha; subst.
      exact p.
    + exact IH.
Qed.

Lemma pointed_search_complete {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (l : list (carrier X)) (b : carrier Y)
  (a : carrier X) :
  InSetoid a l → f a ≈ b → pointed_search f deq l b <> Datatypes.None.
Proof.
  induction l as [|a0 l IH]; simpl.
  - intros [].
  - intros [Hh|Ht] Hfa; destruct (deq (f a0) b) as [p|n].
    + discriminate.
    + refine (False_rect _ (n _)).
      rewrite Hh.
      exact Hfa.
    + discriminate.
    + exact (IH Ht Hfa).
Qed.

(*
 The section: the basepoint goes to the basepoint (which IS a preimage, by
 [preserves_pt]) and every other point to the FIRST element of the
 enumeration mapping onto it.  Special-casing the basepoint is not a
 convenience — without it the section need not be a morphism of Set_* at
 all, since the first preimage of the basepoint may well be an ordinary
 point. 

 --------
 该截面：将基点映射到基点（它确实是一个原像，通过 [preserves_pt]）并将每个其他点映射到映射到它的枚举中的第一个元素。对基点进行特殊处理并非出于方便——如果没有这一点，该截面可能根本不是 Set_* 的一个态射，因为基点的第一个原像很可能是一个普通点。
*)
Definition pointed_section_fun {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) (b : carrier Y) :
  carrier X :=
  match deq b (pt Y) with
  | Datatypes.inl _ => pt X
  | Datatypes.inr _ =>
    match pointed_search f deq (enum_list E) b with
    | Datatypes.Some a => a
    | Datatypes.None => pt X
    end
  end.

Program Definition pointed_section_map {X Y : PointedSetoid}
  (f : PointedMorphism X Y) (deq : DecidableEquiv Y)
  (E : PointedEnumeration X) :
  SetoidMorphism (pointed_setoid Y) (pointed_setoid X) := {|
  morphism := pointed_section_fun f deq E
|}.
Next Obligation.
  intros X Y f deq E; simpl; intros b b' Hbb.
  unfold pointed_section_fun.
  destruct (deq b (pt Y)) as [p|n], (deq b' (pt Y)) as [p'|n'].
  - reflexivity.
  - destruct (n' (transitivity (symmetry Hbb) p)).
  - destruct (n (transitivity Hbb p')).
  - rewrite (pointed_search_respects f deq (enum_list E) b b' Hbb).
    reflexivity.
Qed.

Definition pointed_section {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) :
  Y ~{PointedSets}~> X.
Proof.
  refine (Build_PointedMorphism Y X (pointed_section_map f deq E) _).
  simpl.
  unfold pointed_section_fun.
  destruct (deq (pt Y) (pt Y)) as [p|n].
  - reflexivity.
  - refine (False_rect _ (n _)).
    reflexivity.
Defined.

(*
 Mac Lane's Proposition, second half: an epic pointed map splits, PROVIDED
 the domain is enumerated and `≈` on the codomain is decidable.  In Set the
 unrestricted statement "every epi splits" IS the axiom of choice, so the
 hypothesis pack is the honest constructive content of the proposition, not
 an artefact of the formalization: what a section must supply is a COHERENT
 choice of preimages, and an enumeration plus a decidable codomain is the
 smallest structure that produces one canonically.  As with
 [pointed_monic_split], this ends in [Defined] so that the section it builds
 computes. 

 --------
 麦克莱恩命题，后半部分：一个史诗般的满射映射会分解，前提是定义域可枚举且值域上的 `≈` 可判定。在集合论中，无限制的陈述“每个满射映射都分解”就是选择公理，因此假设集合是真正的构造性内容，而不是形式化的人工产物：一个截面必须提供的是一致的原像选择，而一个枚举加上可判定的值域是产生一个规范选择的最小结构。与 [pointed_monic_split] 一样，这在 [Defined] 处结束，因此它构建的截面是可计算的。
*)
Theorem pointed_epic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) :
  Epic f → Retraction f.
Proof.
  intros He.
  pose proof (pointed_epic_surjective f He) as Hsurj.
  refine (@Build_Retraction PointedSets X Y f (pointed_section f deq E) _).
  intro b; simpl.
  unfold pointed_section_fun.
  destruct (deq b (pt Y)) as [p|n].
  - rewrite (preserves_pt f).
    now symmetry.
  - destruct (pointed_search f deq (enum_list E) b) as [a|] eqn:Hs.
    + exact (pointed_search_correct f deq (enum_list E) b a Hs).
    + destruct (Hsurj b) as [a Ha].
      destruct (pointed_search_complete f deq (enum_list E) b a
                  (enum_covers E a) Ha Hs).
Defined.

(* ------------------------------------------------------------------------ *)
(* * ** The two splitting hypotheses are necessary, in-tree / * ** 这两个分裂假设是必要的，在树内 *)

(*
 The header above prices the two splitting converses by CITATION: in Set,
 "every epimorphism splits" is the axiom of choice.  That is a fact about
 Set, quoted from outside; an audit of the first commit observed that the
 file asserted it without in-tree evidence, and supplied the evidence.
 It is integrated here.

 The two theorems below show that dropping either hypothesis is not a
 matter of finding a cleverer proof: a hypothesis-free splitting for
 Set_* yields INFORMATIVE excluded middle, `∀ P : Prop, P + ¬P`, which is
 not provable in Rocq's core logic.  The probes are the pointed sets built
 over an arbitrary proposition P — `option P` based at `None` for the
 monic side, and the two-point set glued by P for the epic side — so
 deciding the splitting decides P.

 This is the same discipline applied elsewhere in the tree: rather than
 claim an impossibility, exhibit the principle the missing hypothesis is
 equivalent to. 

 --------
 上面标题通过引用(CITATION)给出了两个可分对偶的定价：在 Set 中，“每个满射可分裂”是选择公理。这是关于 Set 的一个事实，引用自外部；对第一次提交的审查发现该文件在没有内部证据的情况下断言了它，并提供了证据。这里已将其整合。

 下面的两个定理表明，去掉任一假设并不是找到更聪明证明的问题：对于 Set_* 的无假设可分裂会产生信息性排中 (INFORMATIVE excluded middle)，`∀ P : Prop, P + ¬P`，而这在 Rocq 的核心逻辑中不可证明。探针是建立在任意命题 P 上的指定点集 — 对单射边基于 `None` 的 `option P`，以及对满射边由 P 粘合的两点集 — 因此决定可分裂即决定 P。这是在树的其他地方应用的相同原则：不是声称不可能，而是展示缺失假设所等价的原理。
*)

Definition InformativeEM := ∀ P : Prop, P + ¬ P.

Section Necessity.

(*
 The monic side: `option P` based at `None`, mapping to the two-point set
 by forgetting the proof.  It is injective for every P, hence monic. 

 --------
 单射方面：`option P` 位于 `None`，通过忘记证明映射到两点集。对于每个 P 它都是单射，因此是单射的。
*)

Definition optP_rel (P : Prop) (u v : option P) : Type :=
  match u, v with
  | Datatypes.Some _, Datatypes.Some _ => True
  | Datatypes.None,   Datatypes.None   => True
  | _, _ => False
  end.

Definition optP_setoid (P : Prop) : Setoid (option P).
Proof.
  refine {| equiv := optP_rel P |}.
  constructor.
  - intros x; destruct x; exact I.
  - intros x y H; destruct x, y; try exact I; exact H.
  - intros x y z H1 H2; destruct x, y, z; try exact I; contradiction.
Defined.

Definition OptP (P : Prop) : PointedSetoid := {|
  pointed_setoid := {| carrier := option P ; is_setoid := optP_setoid P |};
  pt := Datatypes.None
|}.

Definition optP_fun (P : Prop) (u : option P) : option poly_unit :=
  match u with
  | Datatypes.Some _ => Datatypes.Some ttt
  | Datatypes.None   => Datatypes.None
  end.

Definition optP_map (P : Prop) :
  SetoidMorphism (pointed_setoid (OptP P)) (pointed_setoid PointedTwo).
Proof.
  refine {| morphism := optP_fun P |}.
  intros x y H; destruct x, y; simpl in *; try contradiction; try reflexivity;
    try exact I.
Defined.

Definition optP_f (P : Prop) : OptP P ~{PointedSets}~> PointedTwo :=
  Build_PointedMorphism _ _ (optP_map P) I.

Lemma optP_injective (P : Prop) : PointedInjective (optP_f P).
Proof. intros x y H; destruct x, y; simpl in *; try exact I; contradiction. Qed.

Definition optP_monic (P : Prop) : Monic (optP_f P) :=
  fst (pointed_monic_iff (optP_f P)) (optP_injective P).

(*
 Dropping [ImageDecidable] from [pointed_monic_split] decides every
 proposition: the retraction's value at the free point says whether P
 holds. 

 --------
 从 [pointed_monic_split] 中去掉 [ImageDecidable] 决定了每个命题：在自由点的收缩值说明了 P 是否成立。
*)
Theorem unconditional_monic_split_gives_IEM :
  (∀ (X Y : PointedSetoid) (g : X ~{PointedSets}~> Y), Monic g → Section g)
  → InformativeEM.
Proof.
  intros H P.
  destruct (H _ _ (optP_f P) (optP_monic P)) as [r Hr].
  destruct (pointed_map r (Datatypes.Some ttt)) as [p|] eqn:Heq.
  - left; exact p.
  - right; intro p.
    pose proof (Hr (Datatypes.Some p)) as Hp; simpl in Hp.
    change (optP_fun P (Datatypes.Some p)) with (Datatypes.Some ttt) in Hp.
    rewrite Heq in Hp.
    exact Hp.
Qed.

(*
 The epic side: the two-point set with its two points glued exactly when P
 holds.  The identity carrier map into it is surjective, hence epic. 

 --------
 上史诗面：当 P 成立时，两个点的两点集合恰好被粘在一起。映入它的恒等载荷映射是满射的，因此是上史诗。
*)

Definition glueP_rel (P : Prop) (u v : option poly_unit) : Type :=
  match u, v with
  | Datatypes.Some _, Datatypes.Some _ => True
  | Datatypes.None,   Datatypes.None   => True
  | _, _ => P
  end.

Definition glueP_setoid (P : Prop) : Setoid (option poly_unit).
Proof.
  refine {| equiv := glueP_rel P |}.
  constructor.
  - intros x; destruct x; exact I.
  - intros x y H; destruct x, y; try exact I; exact H.
  - intros x y z H1 H2; destruct x, y, z; try exact I;
      first [ exact H1 | exact H2 ].
Defined.

Definition GlueP (P : Prop) : PointedSetoid := {|
  pointed_setoid := {| carrier := option poly_unit
                     ; is_setoid := glueP_setoid P |};
  pt := Datatypes.None
|}.

Definition glueP_map (P : Prop) :
  SetoidMorphism (pointed_setoid PointedTwo) (pointed_setoid (GlueP P)).
Proof.
  refine {| morphism := fun u : option poly_unit => u |}.
  intros x y H; destruct x, y; simpl in *; try contradiction; try reflexivity;
    try exact I.
Defined.

Definition glueP_f (P : Prop) : PointedTwo ~{PointedSets}~> GlueP P :=
  Build_PointedMorphism _ _ (glueP_map P) I.

Lemma glueP_surjective (P : Prop) : PointedSurjective (glueP_f P).
Proof. intro b; exists b; destruct b; exact I. Qed.

Definition glueP_epic (P : Prop) : Epic (glueP_f P) :=
  fst (pointed_epic_iff (glueP_f P)) (glueP_surjective P).

(*
 Dropping the enumeration and decidable equality from [pointed_epic_split]
 likewise decides every proposition: a section either sends the glued
 point to a free point, refuting P by respectfulness, or to the
 basepoint, in which case the retract law establishes P. 

 --------
 从 [pointed_epic_split] 中去掉枚举和可判定的等式同样可以判定每个命题：一个截面要么将粘合点发送到自由点，通过尊重性来反驳 P，要么发送到基点，在这种情况下，重traction定律建立 P。
*)
Theorem unconditional_epic_split_gives_IEM :
  (∀ (X Y : PointedSetoid) (g : X ~{PointedSets}~> Y), Epic g → Retraction g)
  → InformativeEM.
Proof.
  intros H P.
  destruct (H _ _ (glueP_f P) (glueP_epic P)) as [s Hs].
  pose proof (preserves_pt s) as Hpt; simpl in Hpt.
  destruct (pointed_map s Datatypes.None) as [v|] eqn:Heq2;
    [ simpl in Hpt; contradiction | ].
  destruct (pointed_map s (Datatypes.Some ttt)) as [u|] eqn:Heq.
  - right; intro p.
    pose proof (proper_morphism (pointed_map s)
                  (Datatypes.Some ttt) Datatypes.None p) as Hresp.
    rewrite Heq, Heq2 in Hresp.
    exact Hresp.
  - left.
    pose proof (Hs (Datatypes.Some ttt)) as Hp; simpl in Hp.
    rewrite Heq in Hp.
    exact Hp.
Qed.

End Necessity.
