Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.Limit.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(* * * The limit as a functor on the category of all diagrams / * * 所有图的范畴上极限作为函子 *)

(*
 Mac Lane §V.2 Exercise 5 (book p. 115; maclane:V.2:ex5), with the scope
 increment from §IX.7 Exercise 3 (book p. 229; maclane:IX.7:ex3) measured
 and declined below.
 nLab: https://ncatlab.org/nlab/show/limit
 https://ncatlab.org/nlab/show/comma+category

 BACKGROUND.  Beyond its functoriality in the diagram at a fixed shape
 (Adjunction/Diagonal/Limit.v [LimitFunctor], issue #353), the limit
 is functorial in the SHAPE as well.  Mac Lane's “super-comma” category
 has as objects all diagrams (J, F : J ⟶ C) in a fixed target and as
 arrows (J', F') → (J, F) a functor W : J' ⟶ J together with a natural
 transformation F ◯ W ⟹ F'; over a complete target, lim is a functor from
 the OPPOSITE of that category: the limit cone of F restricts along W
 (Structure/Limit/Comparison.v's [cone_reindex]), is pushed along the
 transformation (Theory/Equivalence/Colimit.v [cone_along]) into a
 cone over F', and mediates into lim F'.

 THE DIRECTION OF THE TRANSFORMATION.  The issue defers it to the book;
 Mac Lane's arrows (J', F') → (J, F) carry W : J' ⟶ J with a
 transformation F ◯ W ⟹ F', and [DHom] below is stated in that direction:
 for X → Y, [dtau : ddiag Y ◯ dW ⟹ ddiag X].  It is also the direction
 Construction/Comma.v produces for Id[Cat] ↓ Δ(C)
 ([F ◯ W ≈ Id ◯ F'] in Cat's hom setoid).  The reverse direction,
 F' ⟹ F ◯ W, ALSO forms a category under the same setoid recipe (the fess
 audit compiled it), but limits are not functorial on it: with it both
 lim F' and lim F map INTO lim (F ◯ W), so there is no mediator in either
 variance.  An earlier revision of this paragraph said that direction
 “does not compose” and attributed it to the issue; both statements were
 wrong.

 STALE PREMISES, RE-MEASURED.
 - “the limit functor at a fixed shape is #353's obligation”: #353
 landed — Adjunction/Diagonal/Limit.v has [HasLimitsOfShape],
 [lim_obj], [Lim_map], [LimitFunctor], the adjunction
 with the diagonal and [ColimitFunctor]; the docs/INDEX.md bullet
 for that file already lists “no functoriality in J” as the
 remaining gap — this file.
 - “no category of diagrams, no super-comma, no Cat ↓”: true as
 measured (0 hits for `Cat ↓` and `↓ Cat`; no category whose objects
 pair an index category with a diagram — Structure/AbCategory.v's
 [AbCatObj] is a sigma over [Category] of another kind), but of the
 issue's four prose citations only
 Instance/Fun/Topos.v and Structure/Cone/Const.v still carry
 the phrase “category of diagrams”; Theory/Adamek.v and
 Structure/Complete.v no longer do.
 - The mediator half the issue does not name already exists:
 Theory/Equivalence/Colimit.v has [isalimit_cone], [cone_along]
 (needing only naturality), [limit_induced] with its laws, and
 the colimit duals — the object-level shadows of this
 functor.
 - “the comma-category form over Cat is the sub-case where the
 transformation is the identity”: false on both halves — see (5).

 WHAT IS DELIVERED (39 constants, every one closed under the global
 context).
 (1) THE CATEGORY OF DIAGRAMS.  [DObj C] (an index category with a
 diagram), [DHom X Y] (a shape functor [dW] with
 [dtau : ddiag Y ◯ dW ⟹ ddiag X]), [DHom_equiv]: a pointwise
 isomorphism of the shape functors satisfying Cat's own
 [Functor_Setoid] clause (Theory/Functor.v; Instance/Cat.v)
 together with agreement of the transformations THROUGH THE
 ISOMORPHISM'S IMAGE — the dependent-setoid problem (τ's type moves
 with W) is solved by stating the τ clause at the image rather than
 by transport.  [Did] and [Dcomp] are built COMPONENTWISE because
 [◯] is neither strictly unital nor strictly associative (probe
 N1-N4); [Dcomp_respects] is one use of [naturality]; [Diagrams C :
 Category] with all four laws witnessed by [iso_id].  Readbacks
 [Diagrams_obj], [Diagrams_hom] at [eq_refl].
 (2) THE LIMIT FUNCTOR.  Under [L : Complete C]: [dlim], [dlim_is],
 [dlim_cone f := cone_along (dtau f) (cone_reindex (dW f)
 (isalimit_cone (dlim_is Y)))], [dlim_map f := limit_med (dlim_is X)
 (dlim_cone f)] with [dlim_map_commutes] and [dlim_map_unique], and
 [LimDiagrams : (Diagrams C)^op ⟶ C].  Respectfulness closes by
 [limit_leg_coherence]: the limit cone's own coherence absorbs the
 hom-setoid's isomorphism, which is why the Cat-style setoid is the
 right one and no [StrictCat] deviation (Instance/Cat/Limit.v)
 is needed.  Comparison.v's [reindex_comparison] is NOT the arrow
 part: it targets a separately supplied limit of the reindexed
 diagram and would need a second mediation.
 (3) AT A FIXED SHAPE, THIS IS #353.  [fixed_hom b] reads a
 transformation [b : F ⟹ G] as the arrow (J, G) → (J, F) with the
 identity shape functor; [lim_obj_is_dlim] at [eq_refl] and
 [dlim_map_fixed : dlim_map L (fixed_hom b) ≈ Lim_map b]
 (Adjunction/Diagonal/Limit.v, at [Complete_HasLimitsOfShape L J]).
 (4) THE COLIMIT DUAL.  [Cocomplete C] and [Complete (C^op)] are not
 convertible (probe N5) but interderivable because [(F^op)^op] IS
 [F] by conversion: Construction/Product/Limit.v's
 [Complete_op_of_Cocomplete] — REUSED, not re-defined; an earlier
 revision of this file re-defined it under another name, which the
 fess audit caught — and the new [cocomplete_of_complete_op],
 round-tripping at [eq_refl].  Then
 [ColimDiagrams (L : Cocomplete C) : Diagrams (C^op) ⟶ C :=
 Opposite_Functor (LimDiagrams …)], read through
 [Opposite (Opposite C) = C].  [Diagrams (C^op)] IS the covariant
 colimit category: an object is [F^op] for [F : K^op ⟶ C], and an
 arrow X → Y is [dW : didx X ⟶ didx Y] with [F_X ⟹ F_Y ◯ dW^op] in
 C.  Readbacks [ColimDiagrams_fobj], [dcolim_is_colimit_apex] at
 [eq_refl].
 (5) THE COMMA FORM.  [CommaDiagrams C := Id[Cat] ↓ Δ(C)]
 (Construction/Comma.v; Functor/Diagonal.v's [Diagonal])
 elaborates, also at [Sets] and [Coq] (measured): “Comma is never
 instantiated with Cat” was a fact about the tree, not an
 obstruction.  Its square is a natural ISOMORPHISM (Cat's hom
 setoid), not required to be an identity — the comma form is the
 INVERTIBLE sub-case, not the identity one — and its hom setoid compares
 the functor components only ([CommaDiagrams_equiv] at [eq_refl];
 Comma.v), so the square is forgotten.
 [comma_diagrams_obj] and [comma_diagrams_arrow] read every comma
 arrow as a [Diagrams] arrow ([dW] at [eq_refl]) — as a FUNCTION
 only: the probe's countermodel in [CommaDiagrams Sets]
 ([p420_f_id ≈ p420_f_negb], squares [id] and [negb], and
 [p420_no_respectful_arrow_part]) shows that no [Proper] assignment
 of arrows can return the square's component on both, so the
 canonical arrow part — the mediator the square determines — is not
 respectful and the comma form cannot carry it; a functor with some
 OTHER arrow part is not excluded.

 UNIVERSES (measured by [About] under [Set Printing Universes] on all 39
 constants).
 - No word-bounded [Set] in any block; no [JMeq], [EqdepFacts] or
 [eq_rect_r] cap anywhere ([prod_rect] caps from the comma's product
 category appear).
 - [Diagrams@{u u0 u1 u2 u3 u4} : Category@{u2 u4 u4} → Category@{u u0 u0}]
 with [u3 < u], [u4 < u], [u3 <= u0], [u4 <= u0]: the object universe
 sits strictly above the index categories' object level [u3] and hom
 level [u4], exactly the shape [Cat] has, and the target's hom level
 IS the index categories' ([Category@{u2 u4 u4}]).  Nothing was
 annotated.
 - [LimDiagrams@{u u0 u1 u2 u3 u4}] over [C : Category@{u u0 u0}]
 carries [u2 <= u0]: the index categories' OBJECT level at or below
 the target's HOM level — the smallness side condition, arriving on
 its own from [Complete]'s quantification (Structure/Complete.v).
 - [dlim_map_fixed] and [lim_obj_is_dlim] carry [u0 = u3] and
 [u1 = u4]: [Complete]'s index levels identified with the fixed
 shape's, the identification [HasLimitsOfShape] makes; [fixed_hom],
 whose type does not mention [Complete], carries only [u1 = u4].
 - [DHom] carries [u2 < u0]; [DObj] carries no constraint.

 COUNTS AND CONVENTIONS.
 - 39 constants (28 [def], 4 [prf], 1 [inst], 4 [proj], 2 [rec] in the
 [.glob]), all “Closed under the global context”, zero [Axioms:]
 lines, all gated fully qualified.  Two [Defined]
 ([comma_diagrams_arrow], for its [dW] readback; [fixed_hom], for
 [dlim_map_fixed]); thirteen [Qed].
 - Closure 78 files excluding self: Adjunction/Diagonal/Limit.v costs
 26 at the margin (the #353 bridge of (3)), Theory/Equivalence/
 Colimit.v 6, Structure/Limit/Comparison.v 5,
 Construction/Product/Limit.v 4 (the reused bridge), the other
 fifteen [Require]s 0.
 - Test/ProbeDiagrams420.v mirrors the [Require] list (plus
 Instance/Sets.v for the countermodel) and carries 7 refutation
 commands (1 instrument + 6 negatives of two kinds: three conversion,
 three typing), each stripped one at a time in a copy of the whole
 file; the compiled countermodel; readbacks at [eq_refl]; guard
 coverage 37 identifier tokens inside the refutation commands / 27 of
 them also named outside, comments stripped, with ten exhaustive
 exceptions (the keyword, two binder names, the six names the refuted
 declarations would introduce, the absent name); rename-simulated 5/5
 ([Compose], [nat_id], [nat_compose], [Cocomplete] and
 [Complete_op_of_Cocomplete], each renamed throughout a copy) with
 every first break on a guard line.  [make todo] grows by
 those 7 lines only (2202 → 2209), so the issue's “adds no new hits”
 box is not met as written; disclosed.

 NOT DELIVERED.
 - The §IX.7 Exercise 3 increment — the functoriality of lim through the
 limit's expression as an end and the functoriality of ends: the tree
 has neither in the general form.  Structure/End.v carries only
 [Class End] and [Coend]; no limit-as-end statement exists,
 and the only functoriality of a (co)end in the tree is
 Theory/Coend/Fubini.v's [Inner], a concrete coend functor into
 Sets rather than Proposition IX.7.1 (grep over Structure/End.v,
 Structure/Wedge.v and the Theory/Coend directory).
 - A limit functor on the comma form: its canonical arrow part is
 refuted by the countermodel; no other arrow part is attempted.  No
 functor between [CommaDiagrams C] and [Diagrams C] in
 either direction ([comma_diagrams_arrow] is a function on arrows,
 not a setoid morphism).
 - The colimit dual is stated on [Diagrams (C^op)], not on a separately
 built covariant category of C-diagrams with [F' ⟹ F ◯ W] arrows; the
 two coincide up to [K ↦ K^op] on shapes, and no equivalence between
 them is built.
 - At a fixed [W], the sharper natural-transformation form
 [LimitFunctor_J ⟹ LimitFunctor_J' ◯ Induced W]
 (Theory/Kan/Extension.v) is not stated.
 - Functoriality of [Diagrams] in the target, and any colimit-side
 counterpart of [dlim_map_fixed] against [Colim_map]. 

 --------
 Mac Lane §V.2 练习 5（书第 115 页；maclane:V.2:ex5），范围增量来自 §IX.7 练习 3（书第 229 页；maclane:IX.7:ex3），在下面进行了测量和下降。 nLab:  https://ncatlab.org/nlab/show/limit 
 https://ncatlab.org/nlab/show/comma+category背景。在固定形状的图中的函子性之外（参见 Adjunction/Diagonal/Limit.v  [LimitFunctor]，第 353 期），极限在形状上也是函子性的。Mac Lane 的“超级逗号”范畴的对象是在固定目标中的所有图 (J, F : J ⟶ C)，箭头 (J', F') → (J, F) 是一个函子 W : J' ⟶ J 以及一个自然变换 F ◯ W ⟹ F'；在一个完备目标上，lim 是从该范畴的对偶范畴出的函子：F 的极限锥沿 W 限制（参见 Structure/Limit/Comparison.v 的 [cone_reindex]），沿变换（参见 Theory/Equivalence/Colimit.v  [cone_along]）推进到 F' 的锥上，并介入到 lim F'。变换的方向。这个问题将其延迟到书中；
 Mac Lane 的箭头 (J', F') → (J, F) 携带 W : J' ⟶ J，并带有一个变换 F ◯ W ⟹ F'，下面的 [DHom] 是在该方向上陈述的：对于 X → Y，[dtau : ddiag Y ◯ dW ⟹ ddiag X]。同样，这也是 Construction/Comma.v 为 Id [Cat] ↓ Δ(C)（在 Cat 的同构集合 [F ◯ W ≈ Id ◯ F'] 中）生成的方向。反方向 F' ⟹ F ◯ W 也在相同的集合配方下形成一个范畴（汇编审计确认了），但是极限在其上不是函子化的：在它上面，lim F' 和 lim F 都映射到 lim (F ◯ W)，因此在任意变异下都没有中介。这个段落的早期修改版本说这个方向“不能组合”，并将其归因于该问题；这两个陈述都是错误的。陈旧的前提，重新测量。——“在固定形状下的极限函子是 #353 的义务”：#353 已经落地 — Adjunction/Diagonal/Limit.v 有 [HasLimitsOfShape]、[lim_obj]、[Lim_map]、[LimitFunctor]，与对角线的伴随以及 [ColimitFunctor]；该文件的 docs/INDEX.md 列表中已经列出“J 中没有函子性”作为剩余的空白 — 就是这个文件。- “没有图的类别，没有超级逗号，没有 Cat ↓”：根据测量为真（`Cat ↓` 和 `↓ Cat` 都未命中；没有类别，其对象将一个指数类别与一个图配对——Structure/AbCategory.v 的 [AbCatObj] 是另一个类型在 [Category] 上的 sigma），但该问题的四个文字引用中，仅 Instance/Fun/Topos.v 和 Structure/Cone/Const.v 仍然包含“diagram 类别”这一短语；Theory/Adamek.v 和 Structure/Complete.v 不再包含。- 本期中提到的一半中介者已经存在：Theory/Equivalence/Colimit.v 具有 [isalimit_cone]、[cone_along]（仅需要自然性）、[limit_induced] 及其定律，以及余极限的对偶——该函子在对象层面的影子。- “逗号类别形式在 Cat 上是变换为恒等的子情况”：两部分都是假的——见（5）。交付的内容是什么（39 个常量，每个在全局上下文下都是封闭的）。（1）图的范畴。[DObj C]（带有图的索引范畴），[DHom X Y]（一个形状函子 [dW] 与 [dtau : ddiag Y ◯ dW ⟹ ddiag X]），[DHom_equiv]：形状函子的一个逐点同构，满足 Cat 自身的 [Functor_Setoid] 子句（Theory/Functor.v；Instance/Cat.v），并且通过同构的像的一致性完成变换——依赖集等价的问题（τ 的类型随 W 移动）通过在像上声明 τ 子句而不是通过传输来解决。[Did] 和 [Dcomp] 是按组件构建的，因为 [◯] 既不是严格单位的，也不是严格结合的（探测 N1-N4）；[Dcomp_respects] 是 [naturality] 的一次使用；[图表 C：范畴]，所有四条定律都由 [iso_id] 证明。回读 [Diagrams_obj]、[Diagrams_hom] 于 [eq_refl]。（2）极限函子。在 [L : Complete C] 下：[dlim]，[dlim_is]，[dlim_cone f := cone_along (dtau f) (cone_reindex (dW f) (isalimit_cone (dlim_is Y)))], [dlim_map f := limit_med (dlim_is X) (dlim_cone f)] 与 [dlim_map_commutes] 和 [dlim_map_unique]，并且 [LimDiagrams : (Diagrams C)^op ⟶ C]。尊重性由以下关闭
 [limit_leg_coherence]：极限锥自身的相干性吸收了同构集的同构性，这就是为什么 Cat 风格的集是正确的，并且不需要任何 [StrictCat] 偏差（Instance/Cat/Limit.v）。Comparison.v 的 [reindex_comparison] 不是箭头部分：它针对重新索引图表单独提供的极限，并且需要第二个中介。(3) 在固定形状下，这是 #353。[fixed_hom b] 将一个变换 [b : F ⟹ G] 读取为箭头 (J, G) → (J, F) 与身份形状函子；[lim_obj_is_dlim] 在 [eq_refl] 和 [dlim_map_fixed : dlim_map L (fixed_hom b) ≈ Lim_map b]（Adjunction/Diagonal/Limit.v，在 [Complete_HasLimitsOfShape L J] 处）。(4) 余极限对偶。[Cocomplete C] 和 [Complete (C^op)] 不能相互转换（探针 N5），但可以相互推导，因为 [(F^op)^op] 通过转换是 [F]：Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete] — 重用的，没有重新定义；该文件的早期版本以另一个名字重新定义过它，审计时被发现 — 以及新的 [cocomplete_of_complete_op]，在 [eq_refl] 处完成往返。然后 [ColimDiagrams (L : Cocomplete C) : Diagrams (C^op) ⟶ C := Opposite_Functor (LimDiagrams …)]，通读 [Opposite (Opposite C) = C]。[Diagrams (C^op)] 是协变余极限范畴：对象是 [F^op] 对于 [F : K^op ⟶ C]，而箭头 X → Y 是 [dW : didx X ⟶ didx Y] 且 [F_X ⟹ F_Y ◯ dW^op] 属于 C。回读 [ColimDiagrams_fobj]，[dcolim_is_colimit_apex] 在 [eq_refl] 处。（5）逗号形式。[CommaDiagrams C := Id[Cat]  ↓ Δ(C)]
 （Construction/Comma.v；Functor/Diagonal.v 的  [Diagonal] ）
 还在  [Sets] 和  [Coq]（测量过）：“Comma 从不以 Cat 实例化” 是关于树的事实，而不是障碍。它的平方是一个自然同构（Cat 的同态集合），不要求是恒等——逗号形式是可逆子情况，而不是恒等情况——并且它的同态集合只比较函子分量（ [CommaDiagrams_equiv] 在  [eq_refl]；Comma.v），所以这个平方被忽略。[comma_diagrams_obj] 和 [comma_diagrams_arrow] 将每个逗号箭头读作 [Diagrams] 箭头（[dW] 在 [eq_refl]）——仅作为函数：探针在 [CommaDiagrams Sets] 的反模型（[p420_f_id ≈ p420_f_negb]，方块 [id] 和 [negb]，以及 [p420_no_respectful_arrow_part]）显示，没有任何 [Proper] 箭头分配能够同时返回方块的组成部分，因此规范箭头部分——方块确定的中介——不被尊重，并且逗号形式无法承载它；具有某些其他箭头部分的函子也不被排除。宇宙（由 [About] 在 [Set Printing Universes] 下测量，应用于所有 39 个常数）。- 在任何区块中没有词边界的 [Set]；在任何地方没有 [JMeq]、[EqdepFacts] 或 [eq_rect_r] 大写（来自逗号的产品类别的 [prod_rect] 大写出现）。- [Diagrams@{u u0 u1 u2 u3 u4} : Category@{u2 u4 u4} → Category@{u u0 u0}] 与 [u3 < u]、[u4 < u]、[u3 <= u0]、[u4 <= u0]：对象宇宙严格位于索引类别的对象层次 [u3] 和同态层次 [u4] 之上，正好是 [Cat] 的形状，并且目标的同态层次就是索引类别的同态层次（[Category@{u2 u4 u4}]）。没有进行注释。- [LimDiagrams@{u u0 u1 u2 u3 u4}] 在 [C : Category@{u u0 u0}] 上方承载 [u2 <= u0]：索引类别的对象层次位于目标的同态层次之下或相等——这个小性条件，从 [Complete] 的量化（Structure/Complete.v）中自行得出。- [dlim_map_fixed] 和 [lim_obj_is_dlim] 携带 [u0 = u3] 和 [u1 = u4]：[Complete] 的索引级别与固定形状的索引相对应，[HasLimitsOfShape] 进行识别；[fixed_hom]，其类型未提及 [Complete]，仅携带 [u1 = u4]。- [DHom] 携带 [u2 < u0]；[DObj] 不携带任何约束。计数与约定。- 39 个常量（28 个 [def]，4 个 [prf]，1 个 [inst]，4 个 [proj]，2 个 [rec] 在 [.glob] 中），全部“在全局上下文下封闭”，零条 [Axioms:] 行，全部为完全限定的门控。两个 [Defined]（[comma_diagrams_arrow]，用于其 [dW] 回读；[fixed_hom]，用于 [dlim_map_fixed]）；十三个 [Qed]。- 封闭 78 个文件（不包括自身）：Adjunction/Diagonal/Limit.v 在边缘成本为 26（(3) 的 #353 桥），Theory/Equivalence/Colimit.v 6，Structure/Limit/Comparison.v 5，Construction/Product/Limit.v 4（重复使用的桥），其他十五个 [Require] 为 0。- Test/ProbeDiagrams420.v 对应 [Require] 列表（加上计数模型的 Instance/Sets.v），并包含 7 条反驳命令（1 条仪器命令 + 6 条两种类型的负命令：三条转换命令，三条类型命令），每次在整个文件的副本中逐一去掉一条；已编译的计数模型；在 [eq_refl] 处的回读；反驳命令中有 37 个标识符标记被保护/其中 27 个在外部也被命名，注释已去掉，并有十个详尽的例外（关键字、两个束缚名、被反驳声明将引入的六个名字、缺失的名字）；重命名模拟 5/5（[Compose]、[nat_id]、[nat_compose]、[Cocomplete] 和 [Complete_op_of_Cocomplete]，每个副本中全部进行重命名）并在每个保护行上首次断开。[make todo] 只增长这 7 行（2202 → 2209），所以问题的“没有新增命中”框按原文未满足；已披露。未交付。- §IX.7 练习 3 增量——通过将极限表示为端 (end) 的极限的函子性以及端的函子性：一般形式中该树两者都没有。Structure/End.v 只包含 [Class End] 和 [Coend]；没有极限作为端的声明，并且树中 (co)end 的唯一函子性是 Theory/Coend/Fubini.v 的 [Inner]，这是一个具体的 coend 函子到 Sets，而不是命题 IX.7.1（可在 Structure/End.v、Structure/Wedge.v 和 Theory/Coend 目录中 grep）。- 逗号形式上的极限函子：其规范箭头部分被反例模型推翻；未尝试其他箭头部分。在 [CommaDiagrams C] 和 [Diagrams C] 之间没有任何函子（方向任意）（[comma_diagrams_arrow] 是箭头上的函数，而不是集合态态射）。- 对偶余极限在 [Diagrams (C^op)] 上陈述，而不是在单独构建的具有 [F' ⟹ F ◯ W] 箭头的 C-图协变范畴上；两者在 [K ↦ K^op] 形状上是一致的，但未建立它们之间的等价性。- 在固定的 [W] 上，更明确的自然变换形式 [LimitFunctor_J ⟹ LimitFunctor_J' ◯ Induced W]（Theory/Kan/Extension.v）未被陈述。- 在目标上的 [Diagrams] 的函子性，以及 [dlim_map_fixed] 针对 [Colim_map] 的任意余极限侧对应项。
*)

(* * ** The category of all diagrams in a fixed target / * ** 在固定目标中的所有图的范畴 *)

(* An object: an index category together with a diagram of that shape. / 一个对象：一个索引范畴以及一个该形状的图表。 *)
Record DObj (C : Category) : Type := {
  didx  : Category;
  ddiag : didx ⟶ C
}.

Arguments didx {C} _.
Arguments ddiag {C} _.

(*
 An arrow X → Y: a functor between the shapes and a transformation from
 the reindexed diagram of Y to the diagram of X.  This is the direction
 in which limits are contravariant: lim (ddiag Y) restricts along [dW]
 and pushes along [dtau] into a cone over [ddiag X]. 

 --------
 箭头 X → Y：一个在形状之间的函子，以及从 Y 的重索引图到 X 的图的变换。这是极限是逆变的方向：lim (ddiag Y) 沿 [dW] 限制，并沿 [dtau] 推入 [ddiag X] 上的锥。
*)
Record DHom {C : Category} (X Y : DObj C) : Type := {
  dW   : didx X ⟶ didx Y;
  dtau : ddiag Y ◯ dW ⟹ ddiag X
}.

Arguments dW {C X Y} _.
Arguments dtau {C X Y} _.

(*
 Two arrows are equivalent when their shape functors are naturally
 isomorphic (Cat's own hom setoid, Theory/Functor.v's [Functor_Setoid])
 and their transformations agree through that isomorphism's image. 

 --------
 当两个箭头的形状函子自然同构（类别自身的同态集合，Theory/Functor.v 中的 [Functor_Setoid]）并且它们的变换通过该同构的映射一致时，这两个箭头是等价的。
*)
Definition DHom_equiv {C : Category} {X Y : DObj C} (f g : DHom X Y) : Type :=
  { i : ∀ j : didx X, dW f j ≅ dW g j
  & ((∀ (x y : didx X) (h : x ~> y),
        fmap[dW f] h ≈ from (i y) ∘ fmap[dW g] h ∘ to (i x))
     * (∀ j : didx X,
        transform[dtau f] j ≈ transform[dtau g] j ∘ fmap[ddiag Y] (to (i j))))%type }.

#[export] Program Instance DHom_Setoid {C : Category} {X Y : DObj C} :
  Setoid (DHom X Y) := {| equiv := DHom_equiv |}.
Next Obligation.
  constructor.
  - intro f.
    exists (fun j => iso_id).
    split; intros; simpl.
    + now rewrite id_left, id_right.
    + now rewrite fmap_id, id_right.
  - intros f g [i [Hm Ht]].
    exists (fun j => iso_sym (i j)).
    split; intros; simpl.
    + rewrite Hm.
      rewrite <- !comp_assoc.
      rewrite iso_to_from, id_right.
      rewrite comp_assoc, iso_to_from, id_left.
      reflexivity.
    + rewrite Ht.
      rewrite <- comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Y) _ _ _ (to (i j)) (from (i j))).
      rewrite (iso_to_from (i j)).
      rewrite fmap_id, id_right.
      reflexivity.
  - intros f g h [i [Hmi Hti]] [k [Hmk Htk]].
    exists (fun j => iso_compose (k j) (i j)).
    split; intros; simpl.
    + rewrite Hmi, Hmk.
      rewrite <- !comp_assoc.
      reflexivity.
    + rewrite Hti, Htk.
      rewrite <- comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Y) _ _ _ (to (k j)) (to (i j))).
      reflexivity.
Qed.

(*
 Identity and composition are built componentwise: [◯] is neither
 strictly unital nor strictly associative, so [nat_id] lands at
 [ddiag X ◯ Id ⟹ ddiag X ◯ Id] and a whiskered composite at the wrong
 bracketing (the probe pins both). 

 --------
 恒等和组成是按组件构建的：[◯]既不严格是单位的，也不严格是结合的，所以[nat_id]落在[ddiag X ◯ Id ⟹ ddiag X ◯ Id]上，并且一个加鬚的复合在错误的括号（探针固定两个）。
*)
Program Definition Did {C : Category} (X : DObj C) : DHom X X := {|
  dW := Id[didx X];
  dtau := {| transform := fun j => id[ddiag X j] |}
|}.

Program Definition Dcomp {C : Category} {X Y Z : DObj C}
  (f : DHom Y Z) (g : DHom X Y) : DHom X Z := {|
  dW := dW f ◯ dW g;
  dtau := {| transform :=
               fun j => transform[dtau g] j ∘ transform[dtau f] (dW g j) |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite (naturality (dtau g) x y f0).
  change (@fmap _ _ (ddiag Y ◯ dW g) x y f0)
    with (fmap[ddiag Y] (fmap[dW g] f0)).
  rewrite <- !comp_assoc.
  rewrite (naturality (dtau f) (dW g x) (dW g y) (fmap[dW g] f0)).
  change (@fmap _ _ (ddiag Z ◯ dW f) (dW g x) (dW g y) (fmap[dW g] f0))
    with (fmap[ddiag Z] (fmap[dW f] (fmap[dW g] f0))).
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  rewrite comp_assoc.
  rewrite (naturality (dtau g) x y f0).
  change (@fmap _ _ (ddiag Y ◯ dW g) x y f0)
    with (fmap[ddiag Y] (fmap[dW g] f0)).
  rewrite <- !comp_assoc.
  rewrite (naturality (dtau f) (dW g x) (dW g y) (fmap[dW g] f0)).
  change (@fmap _ _ (ddiag Z ◯ dW f) (dW g x) (dW g y) (fmap[dW g] f0))
    with (fmap[ddiag Z] (fmap[dW f] (fmap[dW g] f0))).
  reflexivity.
Qed.

Lemma Dcomp_respects {C : Category} {X Y Z : DObj C}
  (f f' : DHom Y Z) (Ef : DHom_equiv f f')
  (g g' : DHom X Y) (Eg : DHom_equiv g g') :
  DHom_equiv (Dcomp f g) (Dcomp f' g').
Proof.
  destruct Ef as [i [Hmi Hti]].
  destruct Eg as [k [Hmk Htk]].
  unshelve eexists.
  - intro j.
    exact (iso_compose (@fobj_iso _ _ (dW f') _ _ (k j)) (i (dW g j))).
  - split.
    + intros x y h; simpl.
      rewrite Hmi.
      rewrite Hmk.
      rewrite !fmap_comp.
      rewrite <- !comp_assoc.
      reflexivity.
    + intro j; simpl.
      rewrite Htk.
      rewrite Hti.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap[ddiag Y] (to (k j)))
                          (transform[dtau f'] (dW g j))
                          (fmap[ddiag Z] (to (i (dW g j))))).
      rewrite (naturality (dtau f') (dW g j) (dW g' j) (to (k j))).
      change (@fmap _ _ (ddiag Z ◯ dW f') (dW g j) (dW g' j) (to (k j)))
        with (fmap[ddiag Z] (fmap[dW f'] (to (k j)))).
      rewrite <- !comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Z) _ _ _
                    (fmap[dW f'] (to (k j))) (to (i (dW g j)))).
      reflexivity.
Qed.

Program Definition Diagrams (C : Category) : Category := {|
  obj := DObj C;
  hom := @DHom C;
  homset := @DHom_Setoid C;
  id := @Did C;
  compose := @Dcomp C
|}.
Next Obligation.
  intros f f' Ef g g' Eg.
  exact (Dcomp_respects f f' Ef g g' Eg).
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, !id_right.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_left, id_right.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_right, comp_assoc.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_right, comp_assoc.
Qed.

Example Diagrams_obj (C : Category) : obj[Diagrams C] = DObj C := eq_refl.

Example Diagrams_hom (C : Category) (X Y : Diagrams C) :
  (X ~{Diagrams C}~> Y) = DHom X Y := eq_refl.

(* * ** The limit functor on the opposite of the category of diagrams / * ** 图表范畴对偶上的极限函子 *)

Section LimDiagrams.

Context {C : Category}.
Context (L : @Complete C).

Definition dlim (X : DObj C) : C :=
  vertex_obj[@limit_cone (didx X) C (ddiag X) (L (didx X) (ddiag X))].

Definition dlim_is (X : DObj C) : IsALimit (ddiag X) (dlim X) :=
  limit_is_alimit (L (didx X) (ddiag X)).

(*
 The cone over [ddiag X] with apex [dlim Y]: the limit cone of [ddiag Y]
 restricted along [dW f] (Comparison.v's [cone_reindex]) and pushed along
 [dtau f] (Theory/Equivalence/Colimit.v's [cone_along]). 

 --------
 以  [ddiag X]  为底、顶点为  [dlim Y]  的锥：沿  [dW f]  限制的  [ddiag Y]  的极限锥（Comparison.v 中的  [cone_reindex] ）并沿  [dtau f]  推送（Theory/Equivalence/Colimit.v 中的  [cone_along] ）。
*)
Definition dlim_cone {X Y : DObj C} (f : DHom X Y) : Cone (ddiag X) :=
  cone_along (dtau f)
    (cone_reindex (dW f) (isalimit_cone (dlim_is Y))).

Example dlim_cone_apex {X Y : DObj C} (f : DHom X Y) :
  vertex_obj[dlim_cone f] = dlim Y := eq_refl.

(* The arrow part: the unique mediator into the limit of [ddiag X]. / 箭头部分：进入 [ddiag X] 极限的唯一中介。 *)
Definition dlim_map {X Y : DObj C} (f : DHom X Y) : dlim Y ~{C}~> dlim X :=
  limit_med (dlim_is X) (dlim_cone f).

Lemma dlim_map_commutes {X Y : DObj C} (f : DHom X Y) (j : didx X) :
  limit_leg (dlim_is X) j ∘ dlim_map f
    ≈ transform[dtau f] j ∘ limit_leg (dlim_is Y) (dW f j).
Proof. exact (limit_med_commutes (dlim_is X) (dlim_cone f) j). Qed.

Lemma dlim_map_unique {X Y : DObj C} (f : DHom X Y)
  (v : dlim Y ~{C}~> dlim X) :
  (∀ j : didx X, limit_leg (dlim_is X) j ∘ v
                 ≈ transform[dtau f] j ∘ limit_leg (dlim_is Y) (dW f j)) →
  dlim_map f ≈ v.
Proof. intro Hv. exact (limit_med_unique (dlim_is X) (dlim_cone f) v Hv). Qed.

(*
 Mac Lane V.2 Exercise 5: over a complete target, taking limits is a
 functor on the opposite of the category of diagrams. 

 --------
 Mac Lane 第二版 练习 5：在一个完备的目标上，取极限是图范畴对偶上的一个函子。
*)
Program Definition LimDiagrams : (Diagrams C)^op ⟶ C := {|
  fobj := dlim;
  fmap := fun X Y f => dlim_map f
|}.
Next Obligation.
  intros f g [i [Hm Ht]].
  symmetry.
  apply dlim_map_unique; intro j.
  rewrite dlim_map_commutes.
  rewrite Ht.
  rewrite <- comp_assoc.
  rewrite (limit_leg_coherence (dlim_is x) (to (i j))).
  reflexivity.
Qed.
Next Obligation.
  apply dlim_map_unique; intro j.
  simpl.
  now rewrite id_left, id_right.
Qed.
Next Obligation.
  apply dlim_map_unique; intro j.
  simpl.
  rewrite comp_assoc.
  rewrite (dlim_map_commutes f j).
  rewrite <- comp_assoc.
  rewrite (dlim_map_commutes g (dW f j)).
  rewrite comp_assoc.
  reflexivity.
Qed.

Example LimDiagrams_fobj (X : DObj C) : LimDiagrams X = dlim X := eq_refl.

Example LimDiagrams_fmap {X Y : DObj C} (f : DHom X Y) :
  fmap[LimDiagrams] f = dlim_map f := eq_refl.

End LimDiagrams.

(** ** The colimit dual / ** 余极限对偶 *)

(*
 [Cocomplete C] and [Complete (C^op)] are not convertible (the probe pins
 the [eq_refl]), but they are interderivable because [(F^op)^op] IS [F]
 by conversion: Construction/Product/Limit.v's
 [Complete_op_of_Cocomplete] goes one way, and the converse below the
 other; the two round-trip at [eq_refl]. 

 --------
 [Cocomplete C] 和 [Complete (C^op)] 不能转换（探针针脚 [eq_refl]），但它们是可相互推导的，因为 [(F^op)^op] 可以通过转换成为 [F]：Construction/Product/Limit.v 的 [Complete_op_of_Cocomplete] 只能单向转换，相反的方式在下面，双向循环在 [eq_refl]。
*)
Definition cocomplete_of_complete_op {C : Category} (L : @Complete (Opposite C)) :
  @Cocomplete C :=
  fun D F => L (Opposite D) (Opposite_Functor F).

Example cocomplete_roundtrip {C : Category} (L : @Cocomplete C) :
  cocomplete_of_complete_op (Complete_op_of_Cocomplete L) = L := eq_refl.

Example complete_op_roundtrip {C : Category} (L : @Complete (Opposite C)) :
  Complete_op_of_Cocomplete (cocomplete_of_complete_op L) = L := eq_refl.

(*
 An object of [Diagrams (C^op)] is a diagram [G : K ⟶ C^op], i.e. [F^op] for
 [F : K^op ⟶ C]; an arrow X → Y is a shape functor [dW] with
 [ddiag Y ◯ dW ⟹ ddiag X] in [C^op], i.e. [F_X ⟹ F_Y ◯ dW^op] in [C] —
 exactly the arrows along which colimits are COVARIANT.  So the colimit
 functor is the limit functor of the opposite target, read back through
 [Opposite (Opposite C) = C]. 

 --------
 [Diagrams (C^op)] 的一个对象是一个图 [G : K ⟶ C^op]，即 [F^op] 对于 [F : K^op ⟶ C]；一个箭头 X → Y 是一个形状函子 [dW]，带有 [ddiag Y ◯ dW ⟹ ddiag X] 在 [C^op] 中，即 [F_X ⟹ F_Y ◯ dW^op] 在 [C] 中——正是沿着这些箭头余极限是协变的。因此，余极限函子是对偶目标的极限函子，通过 [Opposite (Opposite C) = C] 读回。
*)
Definition ColimDiagrams {C : Category} (L : @Cocomplete C) :
  Diagrams (Opposite C) ⟶ C :=
  Opposite_Functor (LimDiagrams (Complete_op_of_Cocomplete L)).

Definition dcolim {C : Category} (L : @Cocomplete C) (X : DObj (Opposite C)) : C :=
  dlim (Complete_op_of_Cocomplete L) X.

Example ColimDiagrams_fobj {C : Category} (L : @Cocomplete C) (X : DObj (Opposite C)) :
  ColimDiagrams L X = dcolim L X := eq_refl.

(*
 At a diagram given as [F^op], the object part is the colimit apex the
 hypothesis chooses for [F]. 

 --------
 在给定为 [F^op] 的图中，对象部分是假设为 [F] 选择的余极顶点。
*)
Example dcolim_is_colimit_apex {C : Category} (L : @Cocomplete C)
  {J : Category} (F : J ⟶ C) :
  dcolim L {| didx := Opposite J; ddiag := Opposite_Functor F |}
  = vertex_obj[@limit_cone (Opposite J) (Opposite C) (Opposite_Functor F) (L J F)]
  := eq_refl.

(* * ** The comma form over Cat, and why it cannot carry the arrow part / * ** 关于逗号形式在猫上的表现，以及为什么它不能承载箭头部分 *)

(*
 The issue names the comma category [Id[Cat] ↓ Δ(C)] as “the sub-case where
 the transformation is the identity”.  Its objects are the same pairs; its
 arrows pair a shape functor with a commuting square, which in Cat's hom
 setoid is a natural ISOMORPHISM [F' ◯ W ≅ F], never an identity; and its
 hom setoid compares the functor components only (Construction/Comma.v's
 [homset]), so the square is forgotten.  The probe carries the concrete
 countermodel: two comma arrows equivalent in this setoid whose squares
 would demand different mediators. 

 --------
 该问题将逗号范畴 [Id[Cat] ↓ Δ(C)] 称为“变换为恒等映射的子情况”。它的对象是相同的对；它的箭头将一个形状函子与一个交换方块配对，在 Cat 的同态集族中是一个自然同构 [F' ◯ W ≅ F]，绝不会是恒等映射；它的同态集族仅比较函子分量（Construction/Comma.v 的 [homset]），因此方块被忽略。探针携带具体的反例：在这个集合中等价的两个逗号箭头，其方块将要求不同的中介。
*)
Definition CommaDiagrams (C : Category) : Category :=
  @Comma Cat 1 Cat Id[Cat] (@Diagonal Cat 1 C).

Example CommaDiagrams_equiv (C : Category) (x y : CommaDiagrams C)
  (f g : x ~{CommaDiagrams C}~> y) :
  (f ≈ g) = ((fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g))%type := eq_refl.

(*
 Every comma arrow does give a [Diagrams] arrow — its square, read as the
 transformation — but only as a FUNCTION on arrows: the assignment depends on
 the square, which the comma setoid discards, so it is not a morphism of
 setoids (the probe's countermodel exhibits two equivalent comma arrows with
 different transformations). 

 --------
 每个逗号箭头确实会给出一个 [Diagrams] 箭头 —— 它的平方，被读作变换 —— 但仅作为箭头上的一个函数：该分配取决于平方，而逗号集合类会丢弃平方，因此它不是集合类的态射（探针的反例展示了两个等价的逗号箭头具有不同的变换）。
*)
Definition comma_diagrams_obj {C : Category} (x : CommaDiagrams C) : DObj C :=
  {| didx := fst `1 x; ddiag := `2 x |}.

Definition comma_diagrams_arrow {C : Category} {x y : CommaDiagrams C}
  (f : x ~{CommaDiagrams C}~> y) :
  DHom (comma_diagrams_obj x) (comma_diagrams_obj y).
Proof.
  unshelve refine (@Build_DHom C (comma_diagrams_obj x) (comma_diagrams_obj y) (fst `1 f)
                     (@Build_Transform _ _ (`2 y ◯ fst `1 f) (`2 x)
                        (fun j => to (`1 (`2 f) j)) _ _)).
  - intros a b h; simpl in *.
    pose proof (`2 (`2 f) a b h) as Hn; simpl in Hn.
    rewrite Hn.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
  - intros a b h; simpl in *.
    pose proof (`2 (`2 f) a b h) as Hn; simpl in Hn.
    rewrite Hn.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
Defined.

Example comma_diagrams_arrow_W {C : Category} {x y : CommaDiagrams C}
  (f : x ~{CommaDiagrams C}~> y) :
  dW (comma_diagrams_arrow f) = fst `1 f := eq_refl.

(* * ** At a fixed shape, the arrow part is #353's [Lim_map] / * ** 在固定形状下，箭头部分是 #353 的 [Lim_map] *)

Section FixedShape.

Context {C : Category} (L : @Complete C) {J : Category}.

(*
 A natural transformation [b : F ⟹ G] as an arrow (J, G) → (J, F) of
 [Diagrams C] with the identity shape functor. 

 --------
 一个自然变换 [b : F ⟹ G] 作为 [Diagrams C] 的箭头 (J, G) → (J, F)，其形状函子为恒等函子。
*)
Definition fixed_hom {F G : J ⟶ C} (b : F ⟹ G) :
  DHom {| didx := J; ddiag := G |} {| didx := J; ddiag := F |}.
Proof.
  unshelve refine (@Build_DHom C {| didx := J; ddiag := G |} {| didx := J; ddiag := F |}
                     Id[J] (@Build_Transform _ _ (F ◯ Id[J]) G (fun j => transform[b] j) _ _)).
  - intros; simpl. apply naturality.
  - intros; simpl. apply naturality_sym.
Defined.

Example lim_obj_is_dlim (F : J ⟶ C) :
  @lim_obj J C (Complete_HasLimitsOfShape L J) F = dlim L {| didx := J; ddiag := F |}
  := eq_refl.

(*
 Adjunction/Diagonal/Limit.v's fixed-shape limit functor is the restriction
 of [LimDiagrams] to the identity shape functor. 

 --------
 Adjunction/Diagonal/Limit.v 的固定形状极限函子是 [LimDiagrams] 在身份形状函子上的限制。
*)
Lemma dlim_map_fixed {F G : J ⟶ C} (b : F ⟹ G) :
  dlim_map L (fixed_hom b) ≈ @Lim_map J C (Complete_HasLimitsOfShape L J) F G b.
Proof.
  apply dlim_map_unique; intro j.
  exact (@Lim_map_commutes J C (Complete_HasLimitsOfShape L J) F G b j).
Qed.

End FixedShape.
