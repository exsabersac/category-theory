Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Top.

Generalizable All Variables.

(*
   * * The underlying-set functor of Top and its adjoint triple

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.9
   (book pp. 132-135): the underlying-set functor of spaces
   [maclane:V.9:construction1] and Exercise 2 [maclane:V.9:ex2].
   Riehl, "Category Theory in Context", §4.1, Example 4.1.6: the adjoint
   triple D ⊣ U ⊣ I for spaces, each adjunction a transposition bijection
   on continuous maps.
   Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
   Example 7.28 and Exercise 7.29: the two extreme topologies on a set,
   and the fact that every function out of a discrete space is continuous.
   nLab: https://ncatlab.org/nlab/show/Top
   nLab: https://ncatlab.org/nlab/show/adjoint+triple

   The classical statement: the functor stripping a space to its set of
   points is faithful and sits in an adjoint triple

   Discrete  ⊣  Forget  ⊣  Indiscrete,

   so it preserves all limits and all colimits; and the triple stops
   there — the indiscrete functor has no right adjoint, because a right
   adjoint would make it preserve colimits and it visibly does not
   (Exercise 2).  Both extreme topologies already live in Instance/Top.v
   ([Discrete_Top], [Indiscrete_Top] — Seven Sketches' Example 7.28), as
   do both transposes: [out_of_discrete_continuous] (every setoid map out
   of a discrete space is continuous — Exercise 7.29, the counit-side
   transpose of the first adjunction) and [into_indiscrete_continuous]
   (every setoid map into an indiscrete space is continuous — the
   unit-side transpose of the second).

   WHERE THE PACKAGED ADJUNCTIONS CANNOT LIVE, AND WHY.  In this library
   the statement above meets a genuine size stratification, and the file's
   shape is dictated by it, so it is spelled out once, here.

   - The hom-sets of [Top] are LARGE: continuity is Type-valued data
   quantifying over the opens of the codomain, so a continuous map
   does not fit at the level [o] of the points — the hom level [h]
   of [Top@{h o}] carries the strict constraint o < h
   (Instance/Top.v, header point 2 and [ContinuousMorphism_equiv]).
   - Every functor in this library imposes h₁ ≤ h₂ between its domain
   and codomain hom levels: the [fmap_respects] field of [Functor] is
   a [Proper] instance taken at the CODOMAIN's levels
   (Theory/Functor.v), which squeezes the hom-map's function space
   into the codomain level.
   - [Sets@{o so}] has objects SetoidObject@{o o} and homs at level
   [o], and the records involved are not cumulative.

   Consequently a functor [Top@{h o} ⟶ Sets@{o so}] — the underlying-set
   functor valued in the Sets WHOSE OBJECTS ARE THE POINT SETOIDS — is
   rejected by the elaborator outright (it would need h ≤ o against
   o < h).  A functor out of [Top] must land one level up, in
   [Sets@{h so}], with the point setoids lifted ([Setoid_Lift],
   Instance/Sets/Classifier.v — the lift changes carrier and equivalence
   not at all, only their universe packaging); this is the same placement
   Instance/Top/Closed.v gives its open- and closed-set functors out of
   [Top^op].  Dually, a functor INTO [Top@{h o}] from a Sets must come
   from [Sets@{o so}] exactly — its objects must be point setoids.  An
   [Adjunction] record between the two would need both functors to share
   ONE Sets, at levels o and h simultaneously, with o < h: the packaged
   triple is unformable at every universe assignment.  This is the
   library's familiar classifier phenomenon (Instance/Sets/Classifier.v
   keeps the Sets classifier as cross-universe theorems for the same
   reason), not a defect of the mathematics: with invariant records, "the
   category of sets containing the points" and "the category of sets
   large enough to receive the homs of Top" are different instantiations
   of [Sets].

   WHAT IS DELIVERED INSTEAD — the strongest formable readings, in the
   Classifier.v style:

   - [Top_Forget : Top@{h o} ⟶ Sets@{h so}], the underlying-set
   functor into the lifted Sets, with [Top_Forget_Faithful].
   - [Top_Discrete], [Top_Indiscrete] : Sets@{o so} ⟶ Top@{h o}, the
   two extreme-topology functors at their natural level.
   - The two adjunctions as CROSS-UNIVERSE TRANSPOSITION ISOMORPHISMS
   of hom-setoids ([discrete_adj], [indiscrete_adj]) with all four
   naturality squares each, packaged as
   [discrete_forget_indiscrete_triple].  Both bijections are the
   identity on underlying maps.  (Where the classical naturality
   square mentions [fmap] of the forgetful functor, the formable
   statement uses the stripped map itself — the lifted [fmap] lives
   between lifted objects and cannot be composed with the unlifted
   transpose.)
   - Preservation of limits and colimits by the underlying-set functor,
   stated shape-wise: the per-diagram stripping functor
   [Forget_Diagram] (for shapes small enough to carry it, which every
   concrete shape in this library is), and the theorems
   [Forget_preserves_limit_cone] / [Forget_preserves_colimit_cocone],
   proved by the two transposes exactly as the adjunctions would have
   — a competing cone in [Sets] transposes along Discrete, a
   competing cocone along Indiscrete.  (The competitor side is stated
   as raw vertex-legs-coherence data; the preservation section
   explains the second stratification that forces this.)  Cone-level
   preservation for the LIFTED functor is neither claimed nor
   concluded: its competitors have big vertices, which no space can
   receive.
   - Exercise 2 in two strengths:
   [indiscrete_image_not_colimiting] — the indiscrete image of the
   coproduct cocone 1 + 1 = 2 of [Sets] is not colimiting in
   [Top]: the indiscrete functor does not preserve a coproduct.
   (The packaged contrapositive through
   [CocontinuousFunctor] cannot even be instantiated at
   [Top_Indiscrete] — see the preservation section — so the
   concrete refutation is the statement.)
   [indiscrete_no_right_adjoint] — no adjunction-shaped data for a
   right adjoint exists: quantifying over an object map
   [R₀ : TopSpace → SetoidObject] together with a transposition
   bijection natural in the Sets variable — exactly the data any
   right adjoint would restrict to, and strictly less than
   functoriality — still yields False.  The classical statement
   "there is no functor R : Top ⟶ Sets with Indiscrete ⊣ R" is
   subsumed: here the TYPE of such an R is itself unformable
   (first bullet above), and the theorem refutes even the data a
   candidate at any level would provide.

   THE OBSTRUCTION, CONCRETELY.  The refuted colimit is the issue's
   suggested one.  In [Sets] the coproduct of two one-point setoids is
   the two-point setoid with its constant injections; [Top_Indiscrete]
   sends it to the two-point indiscrete space, but the coproduct of two
   one-point spaces in [Top] is the two-point DISCRETE space.  The
   mediating map the colimit property would produce into the discrete
   competitor sends true to true and false to false — the identity
   carrier map from the indiscrete two-point space to the discrete one,
   which Instance/Top.v's [indiscrete_to_discrete_id_not_continuous]
   already refutes; here the refutation is re-derived directly: the
   preimage of [singleton_true_open] would be an open of the indiscrete
   space holding at true but not at false, and indiscrete opens are
   UNIFORM.  (Issue #432 will package the adjoint-obstruction idiom
   reusably; it has not landed, so per the issue's correction the
   contrapositive is taken locally.) 

   --------
   * * 拓扑空间的基本集合函子及其伴随三重

   Mac Lane，《为工作中的数学家论范畴》，第2版，第V.9节
   （书页 132-135）：空间的基本集合函子 [maclane:V.9:construction1] 及练习 2 [maclane:V.9:ex2]。
   Riehl，《语境中的范畴论》，§4.1, 示例 4.1.6：空间的伴随三重 D ⊣ U ⊣ I，每个伴随对应连续映射的换位双射。
   Fong 和 Spivak，《组合性中的七个草图》，§7.3.2，示例 7.28 和练习 7.29：集合上的两个极端拓扑，以及每个从离散空间出发的函数都是连续的事实。
   nLab: https://ncatlab.org/nlab/show/Top
   nLab: https://ncatlab.org/nlab/show/adjoint+triple

   经典表述：将空间剥离为其点集合的函子是忠实的，并且位于一个伴随三重中

   离散 ⊣ 忘记 ⊣ 极限因此它保留所有极限和所有余极限；而这个三重结构就止步于此——不离散函子没有右伴随，因为右伴随会使它保留余极限，而显然它并不保留（练习 2）。两种极端拓扑已经存在于 Instance/Top.v 中（[Discrete_Top], [Indiscrete_Top]——Seven Sketches 示例 7.28），两种对偶映射也是如此：[out_of_discrete_continuous]（从离散空间到任意集合范畴的映射都是连续的——练习 7.29，第一个伴随对偶的上余单位）以及 [into_indiscrete_continuous]（进入不离散空间的任意集合范畴映射都是连续的——第二个伴随对偶的下余单位）。

   封装的伴随不能存在的地方，以及原因。在该库中，上述声明遇到了真正的大小分层，文件的结构也是由此决定的，因此在这里被明确说明一次。- [Top] 的同态集合是大的：连续性是类型值的数据，它在象域的开集上量化，所以连续映射不适合集合在 [o] 的点级——[Top@{h o}] 的同态层 [h] 承载严格约束 o < h（Instance/Top.v，第2点标题和 [ContinuousMorphism_equiv]）。
   - 该库中的每个函子在其定义域和象域的同态层之间都强加 h₁ ≤ h₂：[Functor] 的 [fmap_respects] 字段是一个在象域层级取的 [Proper] 实例（Theory/Functor.v），这将同态映射的函数空间压缩到象域层级。
   - [Sets@{o so}] 的对象是 SetoidObject@{o o}，同态在 [o] 层级，而涉及的记录不是累积的。因此，一个函子 [Top@{h o} ⟶ Sets@{o so}] —— 取值于对象为点集合的集合（Sets WHOSE OBJECTS ARE THE POINT SETOIDS）的底层集合函子 —— 会被细化器直接拒绝（它需要满足 h ≤ o，而 o < h）。一个从 [Top] 出来的函子必须到达更高一级的 [Sets@{h so}]，其中点集合被提升（[Setoid_Lift]，Instance/Sets/Classifier.v —— 提升并不改变承载体和等价关系，只改变它们的宇宙包装）；这与 Instance/Top/Closed.v 对其开集和闭集函子从 [Top^op] 出来的放置相同。对偶地，从 Sets 出发到 [Top@{h o}] 的函子必须恰好来自 [Sets@{o so}] —— 其对象必须是点集合。两个之间的 [Adjunction] 记录需要两个函子在 o 和 h 两个层级同时共享一个集合，且 o < h：打包的三元组在每个宇宙分配下都是不可形成的。这是库中熟悉的分类器现象（Instance/Sets/Classifier.v 出于相同的原因将 Sets 分类器作为跨宇宙定理保留），并不是数学上的缺陷：对于不变量记录，“包含点的集合范畴”和“足够大的集合范畴以接收 Top 的同态”是 [Sets] 的不同实例化。

   取而代之的是交付的内容——在 Classifier.v 风格中，最强形式化的可读解：-  [Top_Forget : Top@{h o} ⟶ Sets@{h so}]，作为升起集合的底层集合函子，具有 [Top_Forget_Faithful]。-  [Top_Discrete]，[Top_Indiscrete]：Sets@{o so} ⟶ Top@{h o}，在其自然层次上的两个极端拓扑函子。-  这两个伴随作为同态集合的跨宇宙换位同构（[discrete_adj]，[indiscrete_adj]），每个都带有四个自然性方框，打包为 [discrete_forget_indiscrete_triple]。两个双射在底层映射上都是恒等映射。(当经典的自然性方阵提到遗忘函子 [fmap] 时，可形成的陈述使用剥离的映射本身 —— 提升后的 [fmap] 存在于提升对象之间，不能与未提升的转置组合。) 
   - 基本集合函子对极限和余极限的保持，按形状说明：按图剥离函子 [Forget_Diagram]（对于小到可以承载它的形状，每个该库中的具体形状都是如此），以及定理 [Forget_preserves_limit_cone] / [Forget_preserves_colimit_cocone]，由两次转置正好像伴随一样证明 —— [Sets] 中的一个竞争锥沿离散转置，一个竞争余锥沿非离散转置。（竞争方被说明为原始的顶点-腿-相干数据；保留部分解释了导致这种情况的第二次分层。）对于 LIFTED 函子，锥级保留既未被声称，也未被得出结论：它的竞争对手具有大顶点，没有空间可以容纳。—— 第二题的两种强度：
   [indiscrete_image_not_colimiting] — [Sets] 的余积余锥 1 + 1 = 2 的不离散像在 [Top] 中不是余极限：不离散函子不保留余积。（通过 [CocontinuousFunctor] 打包的对位命题甚至无法在 [Top_Indiscrete] 上实例化——参见保存部分——因此具体反驳就是这个陈述。）[indiscrete_no_right_adjoint] ——不存在右伴随的附加形数据：对对象映射 [R₀ : TopSpace → SetoidObject] 以及在 Sets 变量中自然的换位双射进行量化——正是任何右伴随会限制的全部数据，并且严格少于函子性——仍然得出 False。经典表述
   “没有函子 R : Top ⟶ Sets 与 Indiscrete ⊣ R”被纳入其中：这里这样的 R 的类型本身就是不可构造的（上面第一点），并且该定理甚至否定了候选对象在任何层级可能提供的数据。阻塞，具体来说。被反驳的余极限就是问题所提出的那个。在 [Sets] 中，两个单点集体的积是一个带有恒等注入的两点集体；[Top_Indiscrete] 将其发送到两点不可分空间，但在 [Top] 中，两个单点空间的积是两点离散空间。余极限性质会生成的介导映射进入离散空间竞争者，将真映到真、假映到假——即从两点不可分空间到离散空间的恒等载体映射，Instance/Top.v 的 [indiscrete_to_discrete_id_not_continuous] 已经反驳；在这里，反驳被直接重新导出：[singleton_true_open] 的原像将是不可分空间的一个开集，在真处成立但在假处不成立，而不可分的开集是统一的。（问题 #432 将可重用地打包伴随-阻碍惯用法；它尚未实现，因此根据该问题的修正，逆否命题在本地采用。）
*)

#[local] Obligation Tactic := idtac.

(** ** The underlying-set functor / ** 底层集合函子 *)

(*
 Objects to their point setoids — lifted one level, as the header
 explains — and arrows to their setoid maps.  Carrier and equivalence
 of every image are definitionally those of the space's own points. 

 --------
 对象对应于它们的点集合——如标题所述提升了一层——箭头对应于它们的集合映射。每个像的承载体和等价性在定义上都是该空间自身点的承载体和等价性。
*)
Program Definition Top_Forget@{o h so | o < h, h < so +} :
  Top@{h o} ⟶ Sets@{h so} := {|
  fobj := fun X : TopSpace@{o} => Setoid_Lift@{o h} (top_carrier X);
  fmap := fun X Y f => SetoidMorphism_Lift@{o h} (continuous_map f)
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(*
 Faithfulness, Mac Lane's "concrete category" clause for Top: the
 hom-setoid of [Top] compares exactly what the image compares — the
 action on points — so injectivity of fmap is the identity. 

 --------
 忠诚，Mac Lane 对 Top 的“具体范畴”条款：[Top] 的同态集合严格比较了图像所比较的内容——对点的作用——因此 fmap 的单射性就是恒等映射。
*)
#[export] Instance Top_Forget_Faithful : Faithful Top_Forget.
Proof. constructor; intros x y f g H p; exact (H p). Qed.

(* * ** The discrete-topology functor and its transposition / * ** 离散拓扑函子及其转置 *)

Program Definition Top_Discrete@{o h so | o < h, o < so +} :
  Sets@{o so} ⟶ Top@{h o} := {|
  fobj := fun A : SetoidObject@{o o} => Discrete_Top@{o o} A;
  fmap := fun A B f => {|
    continuous_map := f;
    continuity := out_of_discrete_continuous A (Discrete_Top B) f
  |}
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(*
 The transposition bijection of Discrete ⊣ Forget: a continuous map out
 of a discrete space IS its underlying setoid map ([to]), and every
 setoid map out of a discrete space is continuous ([from] — Seven
 Sketches' Exercise 7.29, [out_of_discrete_continuous]).  The Sets-side
 hom-setoid is lifted to sit beside Top's large hom-setoid in one
 ambient Sets — the piecewise-lift discipline of
 Instance/Sets/Classifier.v. 

 --------
 离散 ⊣ 忘记 的换位双射：从离散空间出的连续映射是其底层集合类映射 ([to])，并且从离散空间出的每个集合类映射都是连续的 ([from] — 《七个草图》练习 7.29, [out_of_discrete_continuous])。Sets 端的同态集合类被提升，与 Top 的大同态集合类并列在一个整体 Sets 中——Instance/Sets/Classifier.v 的分段提升规范。
*)
Program Definition discrete_adj (A : SetoidObject) (Y : TopSpace) :
  @Isomorphism Sets
    {| carrier := Top_Discrete A ~{Top}~> Y
     ; is_setoid := @homset Top (Top_Discrete A) Y |}
    (Setoid_Lift
       {| carrier := A ~{Sets}~> top_carrier Y
        ; is_setoid := @homset Sets A (top_carrier Y) |}) := {|
  to := {| morphism := fun f => continuous_map f |};
  from := {| morphism := fun g =>
    {| continuous_map := g;
       continuity := out_of_discrete_continuous A Y g |} |}
|}.
Next Obligation. intros A Y f g H; exact H. Qed.
Next Obligation. intros A Y f g H; exact H. Qed.
Next Obligation. intros A Y g p; reflexivity. Qed.
Next Obligation. intros A Y f p; reflexivity. Qed.

(*
 The four naturality squares of the adjunction, for the forward and the
 inverse transpose.  Where the classical square would say
 [fmap[Top_Forget] f] the statement uses the stripped map
 [continuous_map f] — see the header. 

 --------
 伴随的四个自然性方形，针对正向和逆向转置。经典的方形会说 [fmap[Top_Forget] f]，该语句使用了简化映射 [continuous_map f] —— 见标题。
*)
Lemma discrete_adj_nat_l (A A' : SetoidObject) (Y : TopSpace)
  (f : Top_Discrete A ~{Top}~> Y) (g : A' ~{Sets}~> A) :
  to (discrete_adj A' Y) (f ∘[Top] fmap[Top_Discrete] g)
    ≈ to (discrete_adj A Y) f ∘[Sets] g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_nat_r (A : SetoidObject) (Y Z : TopSpace)
  (f : Y ~{Top}~> Z) (g : Top_Discrete A ~{Top}~> Y) :
  to (discrete_adj A Z) (f ∘[Top] g)
    ≈ continuous_map f ∘[Sets] to (discrete_adj A Y) g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_inv_nat_l (A A' : SetoidObject) (Y : TopSpace)
  (f : A ~{Sets}~> top_carrier Y) (g : A' ~{Sets}~> A) :
  from (discrete_adj A' Y) (f ∘[Sets] g)
    ≈ from (discrete_adj A Y) f ∘[Top] fmap[Top_Discrete] g.
Proof. intro p; reflexivity. Qed.

Lemma discrete_adj_inv_nat_r (A : SetoidObject) (Y Z : TopSpace)
  (f : Y ~{Top}~> Z) (g : A ~{Sets}~> top_carrier Y) :
  from (discrete_adj A Z) (continuous_map f ∘[Sets] g)
    ≈ f ∘[Top] from (discrete_adj A Y) g.
Proof. intro p; reflexivity. Qed.

(* * ** The indiscrete-topology functor and its transposition / * ** 不离散拓扑函子及其转置 *)

Program Definition Top_Indiscrete@{o h so | o < h, o < so +} :
  Sets@{o so} ⟶ Top@{h o} := {|
  fobj := fun A : SetoidObject@{o o} => Indiscrete_Top@{o o} A;
  fmap := fun A B f => {|
    continuous_map := f;
    continuity := into_indiscrete_continuous (Indiscrete_Top A) B f
  |}
|}.
Next Obligation. intros X Y f g H p; exact (H p). Qed.
Next Obligation. intros; intro p; reflexivity. Qed.
Next Obligation. intros; intro p; reflexivity. Qed.

(*
 The transposition bijection of Forget ⊣ Indiscrete: a continuous map
 into an indiscrete space IS its underlying setoid map ([from]), and
 every setoid map into an indiscrete space is continuous ([to] —
 [into_indiscrete_continuous]).  This time the small side is the
 Sets-hom out of the points, lifted as before. 

 --------
 忘记 ⊣ 不连续的换位双射：映射到一个不连续空间的连续映射就是它的基础集合同构映射（[from]），并且每个映射到不连续空间的集合同构映射都是连续的（[to] — [into_indiscrete_continuous]）。这一次，小的一边是从点出发的集合同态，像之前一样提升。
*)
Program Definition indiscrete_adj (X : TopSpace) (B : SetoidObject) :
  @Isomorphism Sets
    (Setoid_Lift
       {| carrier := top_carrier X ~{Sets}~> B
        ; is_setoid := @homset Sets (top_carrier X) B |})
    {| carrier := X ~{Top}~> Top_Indiscrete B
     ; is_setoid := @homset Top X (Top_Indiscrete B) |} := {|
  to := {| morphism := fun g =>
    {| continuous_map := g;
       continuity := into_indiscrete_continuous X B g |} |};
  from := {| morphism := fun f => continuous_map f |}
|}.
Next Obligation. intros X B f g H; exact H. Qed.
Next Obligation. intros X B f g H; exact H. Qed.
Next Obligation. intros X B f p; reflexivity. Qed.
Next Obligation. intros X B g p; reflexivity. Qed.

Lemma indiscrete_adj_nat_l (X X' : TopSpace) (B : SetoidObject)
  (g : top_carrier X ~{Sets}~> B) (f : X' ~{Top}~> X) :
  to (indiscrete_adj X' B) (g ∘[Sets] continuous_map f)
    ≈ to (indiscrete_adj X B) g ∘[Top] f.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_nat_r (X : TopSpace) (B B' : SetoidObject)
  (g' : B ~{Sets}~> B') (g : top_carrier X ~{Sets}~> B) :
  to (indiscrete_adj X B') (g' ∘[Sets] g)
    ≈ fmap[Top_Indiscrete] g' ∘[Top] to (indiscrete_adj X B) g.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_inv_nat_l (X X' : TopSpace) (B : SetoidObject)
  (f : X ~{Top}~> Top_Indiscrete B) (g : X' ~{Top}~> X) :
  from (indiscrete_adj X' B) (f ∘[Top] g)
    ≈ from (indiscrete_adj X B) f ∘[Sets] continuous_map g.
Proof. intro p; reflexivity. Qed.

Lemma indiscrete_adj_inv_nat_r (X : TopSpace) (B B' : SetoidObject)
  (g' : B ~{Sets}~> B') (f : X ~{Top}~> Top_Indiscrete B) :
  from (indiscrete_adj X B') (fmap[Top_Indiscrete] g' ∘[Top] f)
    ≈ g' ∘[Sets] from (indiscrete_adj X B) f.
Proof. intro p; reflexivity. Qed.

(*
 Mac Lane §V.9's construction, packaged: the two natural transposition
 bijections flanking the underlying-set functor, with their eight
 naturality squares.  This is Riehl's Example 4.1.6 in the only form the
 universe stratification lets the library state it. 

 --------
 Mac Lane §V.9的构造，打包：围绕底层集合函子两侧的两个自然换位双射，以及它们的八个自然性方框。这是Riehl的例子4.1.6，是宇宙分层唯一允许库陈述的形式。
*)
Definition discrete_forget_indiscrete_triple :=
  (@discrete_adj, @indiscrete_adj,
   (@discrete_adj_nat_l, @discrete_adj_nat_r,
    @discrete_adj_inv_nat_l, @discrete_adj_inv_nat_r),
   (@indiscrete_adj_nat_l, @indiscrete_adj_nat_r,
    @indiscrete_adj_inv_nat_l, @indiscrete_adj_inv_nat_r)).

(*
   * ** The underlying-set functor preserves limits and colimits

   Shape-wise, through the stripping functor: for a diagram in [Top] over
   a (small-hommed) shape, the underlying diagram in [Sets] at the
   natural level.  The two preservation theorems are RAPL and LAPC for
   the adjoint triple, proved exactly as the adjunctions would prove
   them: a competing cone in [Sets] transposes along Discrete to a
   competing cone in [Top], a competing cocone along Indiscrete.

   ONE MORE STRATIFICATION NOTE, parallel to the header's.  The
   limit-cone predicates share a single hom universe between the shape
   and the ambient category: [IsLimitCone] and [IsColimitCocone]
   (Structure/Limit/Preservation.v) accept only cones at instance
   Cone@{u u0 u0 u1 u0 u0}, and [Cocone] (Structure/Cone.v) pins the
   same identification, so LIMITING cones over ONE shape variable
   cannot live in [Top] (homs at h) and in [Sets] (homs at o) within
   one statement.  (The bare [Cone] record itself imposes only
   shape-hom ≤ ambient-hom; both cones exist separately — it is the
   predicate applied to both that cannot be formed.)  The competitor side is therefore stated RAW —
   vertex, legs and coherence as bare data, which is [IsLimitCone] with
   the competing cone's record unfolded — while the [Top] side keeps the
   record vocabulary.  (An earlier revision of this note said the packaged
   image-cone machinery — [FCocone], [PreservesColimitCocone], the
   Continuous/CocontinuousFunctor classes — "cannot be instantiated across
   the o < h gap at all"; that generalized too far: at [Top_Forget], which
   lands in [Sets@{h so}] at [Top]'s own hom level, they DO elaborate, as
   Instance/Top/CompHaus.v measures.  Preservation here stays raw, and the
   breakdown for [Top_Indiscrete] is the concrete refutation of Exercise 2. 

   --------
   * ** 底层集合函子保持极限和余极限

   从形状上看，通过剥离函子：对于在 [Top] 上的一个（小同态）形状的图表，底层在 [Sets] 的自然层面的图表。这两个保持定理是 RAPL 和 LAPC，适用于伴随三重关系，证明方法完全按照伴随的方式进行：[Sets] 中的一个竞争锥沿离散函子转置为 [Top] 中的竞争锥，沿非离散函子则为竞争余锥。再补充一个分层注释，与标题处相平行。极限锥谓词在形状与环境范畴之间共享一个单一的同态宇宙：[IsLimitCone] 和 [IsColimitCocone]（Structure/Limit/Preservation.v）仅接受实例 Cone@{u u0 u0 u1 u0 u0} 的锥，而 [Cocone]（Structure/Cone.v）固定了相同的识别，因此单个形状变量上的极限锥不能同时出现在 [Top]（h 上的 homs）和 [Sets]（o 上的 homs）中。（裸的 [Cone] 记录本身只强加了 shape-hom ≤ ambient-hom；两个锥体各自存在——问题是在两者上应用谓词无法形成。）因此，竞争方被原始陈述——顶点、边和相干性作为裸数据，这是 [IsLimitCone] 并展开竞争锥体的记录——而 [Top] 方保持记录词汇。（此笔记的早期版本说打包的图像锥体机制——[FCocone]、[PreservesColimitCocone]、Continuous/CocontinuousFunctor 类——“根本无法跨 o < h 缺口实例化”；这泛化得太远：在 [Top_Forget] 处，它降落在 [Sets@{h so}] 的 [Top] 自身 hom 层次上，它们确实会展开，正如 Instance/Top/CompHaus.v 测量所示。）这里的保存保持原始状态，而 [Top_Indiscrete] 的分解是对练习 2 的具体反驳。
*)

(*
 The raw competitors of the two theorems below are cones over this
 functor up to conversion — [legs j : A ~{Sets}~> top_carrier (K j)]
 IS [A ~{Sets}~> Forget_Diagram K j] definitionally; only the
 [IsLimitCone]-level packaging is unformable. 

 --------
 下面两个定理的原始竞争者在转换下是这个函子的圆锥——[legs j : A ~{Sets}~> top_carrier (K j)] 在定义上等于 [A ~{Sets}~> Forget_Diagram K j]；只有 [IsLimitCone] 级别的封装是无法形成的。
*)
Program Definition Forget_Diagram {J : Category} (K : J ⟶ Top) :
  J ⟶ Sets := {|
  fobj := fun j => top_carrier (K j);
  fmap := fun i j f => continuous_map (fmap[K] f)
|}.
Next Obligation.
  intros J K i j f g H p.
  exact (@fmap_respects _ _ K i j f g H p).
Qed.
Next Obligation. intros J K j p; exact (@fmap_id _ _ K j p). Qed.
Next Obligation.
  intros J K i j k f g p; exact (@fmap_comp _ _ K i j k f g p).
Qed.

(*
 Stripping preserves limiting cones.  The competitor is raw Sets-side
 data (vertex, legs, coherence); it transposes along the discrete
 topology to a genuine cone in [Top], the limit property of N answers,
 and the mediator strips back down.  This is RAPL for Discrete ⊣ Forget,
 in the only cross-universe form the [Cone] record allows. 

 --------
 剥离保留限制锥。竞争者是原始的 Sets 侧数据（顶点、边、相干性）；它沿离散拓扑转置到  [Top] 中的真实锥，N 的极限性质，以及中介者再剥离回去。这是离散 ⊣ 忘记的 RAPL，在 [Cone] 记录允许的唯一跨宇宙形式中。
*)
Theorem Forget_preserves_limit_cone {J : Category} {K : J ⟶ Top}
  (N : Cone K) (HN : IsLimitCone N)
  (A : SetoidObject) (legs : ∀ j : J, A ~{Sets}~> top_carrier (K j))
  (coh : ∀ (x y : J) (f : x ~{J}~> y),
     continuous_map (fmap[K] f) ∘[Sets] legs x ≈ legs y) :
  ∃! u : A ~{Sets}~> top_carrier (vertex_obj[N]),
    ∀ j : J, continuous_map (cone_leg N j) ∘[Sets] u ≈ legs j.
Proof.
  pose (M' := @Build_Cone J Top K (Discrete_Top A)
    (@Build_ACone J Top (Discrete_Top A) K
       (fun j => Build_ContinuousMorphism (Discrete_Top A) (K j)
                   (legs j)
                   (out_of_discrete_continuous A (K j) (legs j)))
       (fun x y f => coh x y f))).
  destruct (HN M') as [u Hu Huniq].
  unshelve refine {| unique_obj := continuous_map u |}.
  - intros j p; exact (Hu j p).
  - intros v Hv p.
    exact (Huniq (Build_ContinuousMorphism (Discrete_Top A)
                    (vertex_obj[N]) v
                    (out_of_discrete_continuous A (vertex_obj[N]) v))
                 (fun j q => Hv j q) p).
Defined.

(* Stripping preserves colimiting cocones, dually: a raw Sets-side cocone competitor transposes along the indiscrete topology. LAPC for Forget ⊣ Indiscrete. / 剥离保持余极限余锥，反之：一个原始的集合侧余锥竞争者沿着无差别拓扑变换。忘记 ⊣ 无差别的 LAPC。 *)
Theorem Forget_preserves_colimit_cocone {J : Category} {K : J ⟶ Top}
  (N : Cocone K) (HN : IsColimitCocone N)
  (A : SetoidObject) (injs : ∀ j : J, top_carrier (K j) ~{Sets}~> A)
  (coh : ∀ (x y : J) (f : x ~{J}~> y),
     injs y ∘[Sets] continuous_map (fmap[K] f) ≈ injs x) :
  ∃! u : top_carrier (vertex_obj[N]) ~{Sets}~> A,
    ∀ j : J, u ∘[Sets] continuous_map (cocone_inj N j) ≈ injs j.
Proof.
  pose (M' := @Build_Cone (J^op) (Top^op) (K^op) (Indiscrete_Top A)
    (@Build_ACone (J^op) (Top^op) (Indiscrete_Top A) (K^op)
       (fun j => Build_ContinuousMorphism (K j) (Indiscrete_Top A)
                   (injs j)
                   (into_indiscrete_continuous (K j) A (injs j)))
       (fun x y f => coh y x f))).
  destruct (HN M') as [u Hu Huniq].
  unshelve refine {| unique_obj := continuous_map u |}.
  - intros j p; exact (Hu j p).
  - intros v Hv p.
    exact (Huniq (Build_ContinuousMorphism (vertex_obj[N])
                    (Indiscrete_Top A) v
                    (into_indiscrete_continuous (vertex_obj[N]) A v))
                 (fun j q => Hv j q) p).
Defined.

(* * ** Exercise 2: the indiscrete functor has no right adjoint / * ** 练习 2：非离散函子没有右伴随函子 *)

(*
 THE SHAPE.  The two-object discrete shape is taken as [DiscreteCat bool]
 (Instance/Discrete.v) rather than the tree's walking pair
 [Two_Discrete]: the limit-cone predicates and [Cocone] pin the
 shape's hom level to the ambient category's (the stratification note
 above), [Two_Discrete]'s
 hom level is declared at [Set], and [Top]'s hom level is strictly above
 its point level, so no cocone in [Top] can sit over a [Two_Discrete]
 diagram at all.  [DiscreteCat] is universe-flexible, so its instances
 can meet [Sets] at the point level and [Top] at the hom level. 

 --------
 形状。两个对象的离散形状被取为 [DiscreteCat bool]（Instance/Discrete.v），而不是树的行走对 [Two_Discrete]：极限锥谓词和 [Cocone] 固定了形状的 Hom 级别与环境范畴的同级（如上面的分层注记），[Two_Discrete] 的 Hom 级别被声明为 [Set]，而 [Top] 的 Hom 级别严格高于其点级别，因此在 [Top] 中没有余锥能够完全位于 [Two_Discrete] 图之上。[DiscreteCat] 是宇宙灵活的，因此其实例可以在点级别上与 [Sets] 会合，在 Hom 级别上与 [Top] 会合。
*)

(*
 Coherence of a cocone over a discrete shape, in any category: the only
 arrows are (transported) identities. 

 --------
 在任何范畴中，离散形状上余锥的相干性：唯一的箭头是（被传输的）恒等箭头。
*)
Lemma discrete_cocone_coherence {A : Type} {C : Category}
  (H : DiscreteCat A ⟶ C) (c : C) (inj : ∀ x : A, H x ~{C}~> c)
  {x y : A} (f : y ~{DiscreteCat A}~> x) :
  inj x ∘ fmap[H] f ≈ inj y.
Proof.
  destruct f.
  change (inj y ∘ fmap[H] (@id (DiscreteCat A) y) ≈ inj y).
  rewrite fmap_id; apply id_right.
Qed.

(* The discrete pair of one-point setoids. / 一个点集合的离散对。 *)
Definition unit_pair_diagram : DiscreteCat bool ⟶ Sets :=
  @DiscreteCat_Functor bool Sets (fun _ => unit_setoid_object).

(* The coproduct cocone: apex the two-point setoid, injections the two constants. / 余积余锥：顶点为两点集合，注入为两个常数。 *)
Definition bool_cocone : Cocone unit_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Sets^op) (unit_pair_diagram^op)
    bool_setoid_object
    (@Build_ACone ((DiscreteCat bool)^op) (Sets^op) bool_setoid_object
       (unit_pair_diagram^op)
       (fun b => const_morphism unit_setoid_object bool_setoid_object b)
       (fun x y f => discrete_cocone_coherence unit_pair_diagram
                       bool_setoid_object _ f)).

(*
 [bool] with the constant injections is a colimiting cocone in [Sets]:
 the mediator reads a competitor's two legs off at the point, and any
 competitor agrees with it on both booleans.  ([IsColimitCocone] pins
 the ambient hom level to the shape's, and [bool : Set], so the
 colimit property is established at the Set hom level — the level at
 which the whole Exercise-2 argument runs.) 

 --------
 带有恒定注射的 [bool] 是 [Sets] 中的一个余极限余锥：中介在该点读取竞争者的两条腿，且任何竞争者在两个布尔值上都与它一致。（[IsColimitCocone] 将环境 Hom 水平固定到形状的 Hom 水平，[bool : Set]，因此，余极限性质在 Set Hom 水平上得以建立——也是整个练习 2 论证进行的水平。）
*)
Definition bool_cocone_colimit : IsColimitCocone bool_cocone.
Proof.
  intro M.
  unshelve refine
    {| unique_obj := {| morphism := fun b : bool =>
         if b then cocone_inj M true ttt else cocone_inj M false ttt |} |}.
  - intros x; destruct x; intro p; destruct p; simpl; reflexivity.
  - intros v Hv b; destruct b.
    + symmetry; exact (Hv true ttt).
    + symmetry; exact (Hv false ttt).
Defined.

(*
 The image diagram, presented at the target level: the discrete pair of
 one-point indiscrete spaces.  (The composite
 [Top_Indiscrete ◯ unit_pair_diagram] and the generic
 [FCocone Top_Indiscrete bool_cocone] cannot be formed: like the
 limit-cone predicates, the composition and image-cocone constants pin
 ONE hom level across their categories, and the composite would need
 the shape's instance at both levels.  This diagram is the composite presented directly — the same
 objects definitionally, and the only arrows are identities.) 

 --------
 图像图表，在目标层次上呈现：一对离散的一点不可分空间。（复合 [Top_Indiscrete ◯ unit_pair_diagram] 和通用 [FCocone Top_Indiscrete bool_cocone] 无法形成：像极锥谓词一样，复合和图像余锥常量在它们的范畴中固定了单一同层次，而复合需要在两个层次上都有该形状的实例。该图表是直接呈现的复合——定义上相同的对象，唯一的箭头是恒等映射。）
*)
Program Definition indiscrete_pair_diagram@{o h so | o < h, o < so +} :
  DiscreteCat@{h h h} bool ⟶ Top@{h o} := {|
  fobj := fun _ : bool => Indiscrete_Top@{o o} unit_setoid_object@{o o};
  fmap := fun _ _ _ => top_id
|}.
Next Obligation. intros x y f g H p; reflexivity. Qed.
Next Obligation. intros x p; reflexivity. Qed.
Next Obligation. intros x y z f g p; reflexivity. Qed.

(* The indiscrete image of the coproduct cocone: apex the two-point indiscrete space, injections the images of the two constants. / 余积锥的不连续图像：顶点为两点不连续空间，注入为两个常数的像。 *)
Definition indiscrete_image_cocone : Cocone indiscrete_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Top^op) (indiscrete_pair_diagram^op)
    TwoPoint_Indiscrete
    (@Build_ACone ((DiscreteCat bool)^op) (Top^op) TwoPoint_Indiscrete
       (indiscrete_pair_diagram^op)
       (fun b => fmap[Top_Indiscrete]
                   (const_morphism unit_setoid_object bool_setoid_object b))
       (fun x y f => discrete_cocone_coherence indiscrete_pair_diagram
                       TwoPoint_Indiscrete _ f)).

(*
 The competing cocone in [Top]: the DISCRETE two-point space, with the
 two point injections — continuous because any map out of a one-point
 space is, its preimages being constant predicates ([open_const]). 

 --------
 在 [Top] ：离散的两点空间中的竞争余锥，使用两个点的注入 —— 连续的，因为从一个单点空间出发的任何映射都是连续的，其原像是恒定谓词（ [open_const] ）。
*)
Definition disc_leg (b : bool) :
  Indiscrete_Top unit_setoid_object ~{Top}~> Bool_Discrete :=
  Build_ContinuousMorphism (Indiscrete_Top unit_setoid_object) Bool_Discrete
    (const_morphism unit_setoid_object bool_setoid_object b)
    (fun U _ => open_const (Indiscrete_Top unit_setoid_object) (U b)).

Definition disc_cocone : Cocone indiscrete_pair_diagram :=
  @Build_Cone ((DiscreteCat bool)^op) (Top^op) (indiscrete_pair_diagram^op)
    Bool_Discrete
    (@Build_ACone ((DiscreteCat bool)^op) (Top^op) Bool_Discrete
       (indiscrete_pair_diagram^op)
       (fun b => disc_leg b)
       (fun x y f => discrete_cocone_coherence indiscrete_pair_diagram
                       Bool_Discrete _ f)).

(*
 The image cocone is NOT colimiting: the mediator to the discrete
 competitor would send true to true and false to false, and the
 preimage of [singleton_true_open] under it would be a non-uniform open
 of an indiscrete space.  With [bool_cocone_colimit] this is exactly
 "the indiscrete functor does not preserve the coproduct 1 + 1". 

 --------
 像卷锥不是余极限：到离散竞争者的中介映射会将真映射为真，将假映射为假，而其下的 \([singleton_true_open]\) 的原像将是一个非均匀开集的不可分空间。对于 \([bool_cocone_colimit]\)，这正是“不可分函子不保余积 1 + 1”。
*)
Theorem indiscrete_image_not_colimiting :
  IsColimitCocone indiscrete_image_cocone → False.
Proof.
  intro P.
  pose proof (colimitcocone_ump P disc_cocone) as U.
  pose proof (unique_property U true ttt) as Ht.
  pose proof (unique_property U false ttt) as Hf.
  simpl in Ht, Hf.
  pose proof (continuity (unique_obj U)
                (fun b : bool_setoid_object => b = true)
                singleton_true_open true false) as HO.
  discriminate (eq_trans (eq_sym Hf) (HO Ht)).
Qed.

(*
 Mac Lane §V.9, Exercise 2, in adjunction-shaped form.  The hypotheses
 are the data any right adjoint R would provide at the objects involved:
 its object map, and the transposition bijection
 Top(Indiscrete A, Y) ≅ Sets(A, R₀ Y), natural in A.  Nothing else is
 assumed — no functoriality of R₀, no naturality in Y — and False
 follows.  The proof mirrors the standard one: transposing the discrete
 competitor's legs and transposing back the induced map produces the
 non-continuous mediator of [indiscrete_image_not_colimiting]. 

 --------
 Mac Lane §V.9，练习 2，以伴随形式表示。假设是任何右伴随 R 在涉及的对象上提供的数据：它的对象映射，以及自然于 A 的换位双射 Top(Indiscrete A, Y) ≅ Sets(A, R₀ Y)。没有其他假设——没有 R₀ 的函子性，也没有 Y 的自然性——并且由此得出 False。证明与标准证明类似：换位离散竞争者的边，然后再换位回诱导的映射，会产生 [indiscrete_image_not_colimiting] 的非连续中介。
*)
Theorem indiscrete_no_right_adjoint
  (R₀ : TopSpace → SetoidObject)
  (φ : ∀ (A : SetoidObject) (Y : TopSpace),
     @Isomorphism Sets
       {| carrier := Top_Indiscrete A ~{Top}~> Y
        ; is_setoid := @homset Top (Top_Indiscrete A) Y |}
       (Setoid_Lift
          {| carrier := A ~{Sets}~> R₀ Y
           ; is_setoid := @homset Sets A (R₀ Y) |}))
  (φ_nat : ∀ (A A' : SetoidObject) (g : A' ~{Sets}~> A) (Y : TopSpace)
             (f : Top_Indiscrete A ~{Top}~> Y),
     to (φ A' Y) (f ∘[Top] fmap[Top_Indiscrete] g)
       ≈ to (φ A Y) f ∘[Sets] g) :
  False.
Proof.
  (* the transposed legs, as points of R₀ Bool_Discrete / 作为 R₀ Bool_Discrete 点的转置腿 *)
  pose (r := fun b : bool =>
               to (φ unit_setoid_object Bool_Discrete) (disc_leg b) ttt).
  (* the induced map out of the coproduct, and its transpose back / 由余积引出的诱导映射，以及其回转映射 *)
  assert (sp : Proper (respectful (@equiv _ (is_setoid bool_setoid_object))
                                  (@equiv _ (is_setoid (R₀ Bool_Discrete))))
                 (fun b : bool => if b then r true else r false)).
  { intros b b' Hb; simpl in Hb; subst; reflexivity. }
  pose (s := {| morphism := fun b : bool => if b then r true else r false
              ; proper_morphism := sp |}
             : bool_setoid_object ~{Sets}~> R₀ Bool_Discrete).
  pose (h := from (φ bool_setoid_object Bool_Discrete) s).
  (* h restricts along each injection to the corresponding leg: transpose, compute through the bijection's round trips, transpose back / h 沿每个注射限制到相应的支路：转置，通过双射的往返计算，然后再转置回来 *)
  assert (Hleg : ∀ b : bool,
    h ∘[Top] fmap[Top_Indiscrete]
        (const_morphism unit_setoid_object bool_setoid_object b)
      ≈ disc_leg b).
  { intro b.
    assert (E : to (φ unit_setoid_object Bool_Discrete)
                   (h ∘[Top] fmap[Top_Indiscrete]
                      (const_morphism unit_setoid_object
                         bool_setoid_object b))
                  ≈ to (φ unit_setoid_object Bool_Discrete) (disc_leg b)).
    { etransitivity.
      { exact (φ_nat _ _ (const_morphism unit_setoid_object
                            bool_setoid_object b) _ h). }
      intro p; destruct p, b; simpl.
      - exact (iso_to_from (φ bool_setoid_object Bool_Discrete) s true).
      - exact (iso_to_from (φ bool_setoid_object Bool_Discrete) s false).
    }
    transitivity (from (φ unit_setoid_object Bool_Discrete)
                    (to (φ unit_setoid_object Bool_Discrete)
                        (h ∘[Top] fmap[Top_Indiscrete]
                           (const_morphism unit_setoid_object
                              bool_setoid_object b)))).
    { symmetry.
      exact (iso_from_to (φ unit_setoid_object Bool_Discrete) _). }
    transitivity (from (φ unit_setoid_object Bool_Discrete)
                    (to (φ unit_setoid_object Bool_Discrete) (disc_leg b))).
    { exact (proper_morphism (from (φ unit_setoid_object Bool_Discrete))
               _ _ E). }
    exact (iso_from_to (φ unit_setoid_object Bool_Discrete) (disc_leg b)).
  }
  (* whence h true = true and h false = false; continuity is refuted / 于是 h true = true 且 h false = false；连续性被驳斥 *)
  pose proof (Hleg true ttt) as Ht; simpl in Ht.
  pose proof (Hleg false ttt) as Hf; simpl in Hf.
  pose proof (continuity h (fun b : bool_setoid_object => b = true)
                singleton_true_open true false) as HO.
  discriminate (eq_trans (eq_sym Hf) (HO Ht)).
Qed.

(* * ** Acceptance tests The definitional facts the header claims really are definitional. / * **验收测试 抬头所声称的定义性事实确实是定义性的。 *)

(*
 Both adjoints are sections of the forgetful functor on objects, on the
 nose: forgetting either extreme topology returns the very lift of the
 original setoid. 

 --------
 两个伴随都是忘记函子在对象上的截面，严格来说：忘记任一极限拓扑都会返回原始集合范畴的提升。
*)
Example forget_discrete_on_objects (A : SetoidObject) :
  Top_Forget (Top_Discrete A) = Setoid_Lift A := eq_refl.
Example forget_indiscrete_on_objects (A : SetoidObject) :
  Top_Forget (Top_Indiscrete A) = Setoid_Lift A := eq_refl.

(* Both transposition bijections are the identity on underlying maps. / 两个换位双射在基础映射上都是恒等映射。 *)
Example discrete_transpose_identity (A : SetoidObject) (Y : TopSpace)
  (f : Top_Discrete A ~{Top}~> Y) :
  to (discrete_adj A Y) f = continuous_map f := eq_refl.
Example indiscrete_transpose_identity (X : TopSpace) (B : SetoidObject)
  (f : X ~{Top}~> Top_Indiscrete B) :
  from (indiscrete_adj X B) f = continuous_map f := eq_refl.

(* The indiscrete image of the coproduct apex is exactly the two-point indiscrete probe space of Instance/Top.v. / 余积顶点的不连续像正好是 Instance/Top.v 的两点不连续探针空间。 *)
Example image_apex_is_TwoPoint_Indiscrete :
  vertex_obj[indiscrete_image_cocone] = TwoPoint_Indiscrete := eq_refl.
Example image_apex_is_indiscrete_of_bool :
  vertex_obj[indiscrete_image_cocone]
    = Top_Indiscrete (vertex_obj[bool_cocone]) := eq_refl.
