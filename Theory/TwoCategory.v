Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Metacategory.General.

Generalizable All Variables.

(** * Strict 2-categories, in both of Mac Lane's presentations / * 严格的2-范畴，在麦克莱恩的两种表述中 *)

(*
nLab:      https://ncatlab.org/nlab/show/strict+2-category
   nLab:      https://ncatlab.org/nlab/show/double+category
   nLab:      https://ncatlab.org/nlab/show/interchange+law
   nLab:      https://ncatlab.org/nlab/show/whiskering
   Wikipedia: https://en.wikipedia.org/wiki/Strict_2-category
   Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              GTM 5, §II.5, printed pp. 42-45 (horizontal composition, the
              interchange law, Theorem 1, and the definitions of a double
              category and of a 2-category)
   Book:      Mac Lane, ibid., §XII.3, printed p. 273 (2-categories)
   Book:      Riehl, “Category Theory in Context”, Definition 1.7.8
   Paper:     Ehresmann, “Catégories doubles et catégories structurées”,
              C. R. Acad. Sci. Paris 256 (1963), 1198-1201

   Mac Lane states the two-dimensional structure twice, in two different
   styles, and this file carries both.

   §II.5 Theorem 1 is the ARROWS-ONLY statement: the collection of all
   natural transformations is at once the arrow set of two different
   categories, one whose objects are functors (vertical composition, written
   `·`) and one whose objects are categories (horizontal composition, written
   `∘`); the two compositions satisfy the interchange law

       (τ' · σ') ∘ (τ · σ)  =  (τ' ∘ τ) · (σ' ∘ σ)               (5)

   and every arrow that is an identity for `∘` is also an identity for `·`.
   Mac Lane then abstracts: a DOUBLE CATEGORY (§II.5, printed p. 44, after
   Ehresmann) is “a set which is the set of arrows for two different
   composition operations which together satisfy the interchange law”, and a
   2-CATEGORY is “a double category in which every identity arrow for the
   first composition is also an identity for the second”. His own negative
   example is recorded there too: the commutative squares of Set form a
   double category which is NOT a 2-category.

   §XII.3 (and Riehl 1.7.8) states the same notion in the TYPED, globular
   style: 0-cells, 1-cells between them, and 2-cells between PARALLEL
   1-cells, with vertical composition making each hom into a category and
   horizontal composition compatible with composition of 1-cells.

   WHICH PRESENTATION IS PRIMARY, AND WHY BOTH.  The globular class
   [TwoCategory] is the workhorse: it is the one an instance can be built
   at, and Instance/Cat/TwoCategory.v builds `Cat_TwoCategory` on it.  The
   arrows-only classes [StrictDoubleCategory] and [StrictTwoCategory] are
   Mac Lane's own words, and they are what makes his def-3 condition —
   “every identity for one composition is an identity for the other” —
   LITERALLY statable, hence refutable: in the typed style that sentence
   compares two families of cells whose types do not even match unless the
   vertical arrow in question is already an identity, so a typed rendering
   must either presuppose what it wants to say or replace it by a proxy.
   Theory/Metacategory/General.v is the in-tree precedent for arrows-only
   axiomatisations with guarded composition, and the arrows-only half here
   reuses its axioms verbatim: [MetaComp] is that file's [Metacategory]
   data over a FIXED setoid, so that two of them may be laid on one
   collection of cells, and the two packagings are interconvertible
   ([Metacategory_of_MetaComp], [MetaComp_of_Metacategory], both
   field-for-field with no proof content).  A strict double category is
   then one setoid of cells carrying two [MetaComp] structures plus
   interchange, each of them a [Metacategory] ([dvert_Meta],
   [dhoriz_Meta]), so Mac Lane's “two different categories” are obtained by
   feeding them to that file's [Category_from_Metacategory]
   ([dvert_Category], [dhoriz_Category]).

   HOW STRICT IS “STRICT” HERE, EXACTLY.  A textbook strict 2-category has
   1-cell composition associative and unital ON THE NOSE, so that the two
   bracketings of a triple composite are the same 1-cell and a 2-cell
   between the one is a 2-cell between the other.  In this library that
   equality is not available: 2-cells are INDEXED by 1-cells, the 1-cell
   layer is an ordinary [Category] whose associativity is a proof in the
   hom-setoid, and transporting a 2-cell along such a proof cannot be shown
   proof-irrelevant without UIP (the same wall Theory/Metacategory/General.v
   meets as its ObjUIP hypothesis, and that Theory/Category/Monoid.v proves
   unavoidable in [arrow_mul_respects_forces_UIP]).  What IS available, and
   what the class asks for, is that re-bracketing RELATES the two types
   of 2-cells by chosen maps: the class carries [tassoc_cast],
   [tunitl_cast], [tunitr_cast] as data, required only to respect `≈`, to
   preserve vertical composition, and to carry the three horizontal laws
   — invertibility is deliberately NOT demanded (a model may collapse
   under them; [ChaoticTwoCat]'s casts are constant), though at `Cat`
   all three are bijections
   ([thassoc], [thunit_left], [thunit_right]).  At `Cat` all three are the
   IDENTITY on components — a [Transform] mentions only `fobj` and `fmap` of
   its two functors, and those agree definitionally across re-bracketing —
   so the three laws there are ordinary componentwise equations of natural
   transformations, with no transport anywhere.  That is the precise sense
   in which `Cat` is strict in this development, and it is why a general
   cast along `≈` of 1-cells is deliberately NOT a field: at `Cat` such a
   cast is the transport of a transformation along a strict functor
   equality, and its proof-irrelevance is exactly UIP on objects.

   RELATION TO Theory/DoubleCategory.v.  That file's [DoubleCategory] is the
   PSEUDO (coherence-only) notion: its vertical direction is strict but its
   horizontal composition of 1-cells is associative and unital only up to
   invertible GLOBULAR SQUARES ([dassoc], [dunit_left], [dunit_right]),
   subject to triangle and pentagon coherence.  The classes here are strict:
   the corresponding comparisons carry no 2-cell content at all, being mere
   identifications of cell types, so no coherence law is required of them —
   a strict double category is a pseudo one whose coherence squares are
   identities.  The two developments are independent (neither file requires
   the other); the degeneration is stated as prose rather than as a functor
   because [DoubleCategory] bundles its vertical direction as a [Category]
   and its squares with a two-sided boundary coercion, while the strict
   arrows-only classes below bundle nothing of the kind, so the comparison
   would be a construction between differently shaped records rather than a
   forgetting of structure.

   WHAT THE COMPARISON OF PRESENTATIONS ACHIEVES, EXACTLY.  Delivered:
   (a) [twocategory_def3], the globular class satisfies Mac Lane's def-3
   condition — the identity 2-cell on an identity 1-cell is a unit for both
   compositions, proved from the fields; (b) [twocategory_tid2_vunit],
   every identity 2-cell whatever is a `·`-unit, while [IsHUnit] is not
   even TYPEABLE except on an identity 1-cell, so the two families of units
   are different and def 3 is one-directional (that the inclusion is
   strict is a statement about which types exist, not a theorem, and none
   is claimed); (c) the arrows-only classes with def 2 and def 3 as
   records, both of their compositions exhibited as [Metacategory]
   structures hence as ordinary categories, and Mac Lane's own negative
   example refuted at a concrete model ([NatSq_not_a_two_category]); and
   (d) the FORWARD PASSAGE [TwoCategory_to_Strict], turning a globular
   [TwoCategory] into an arrows-only [StrictTwoCategory] under the explicit
   hypothesis pack [StrictBase], with the def-3 coincidence proved rather
   than assumed and the comparison measured by [TwoArr_at_faithful],
   [TwoArr_at_respects], [TwoArr_at_surjective], [TwoV_at] and [TwoH_at].
   The pack is [ToArrows]'s hypothesis raised one dimension (UIP on 0-cells
   AND on 1-cells) together with strictness of the 1-cell layer; it is
   satisfiable ([NatPlus_StrictBase]); at `Cat` it is NOT inhabitable in
   this library — no Leibniz path is derivable for [sb_assoc]'s equation,
   the two bracketings being non-convertible with proof-relevant law
   fields — though the identity type is not proved empty, so this is
   underivability recorded, not a refutation theorem.  NOT delivered: the
   CONVERSE passage, reading a globular [TwoCategory] off an arrows-only
   [StrictTwoCategory].  Its two-dimensional ingredient is supplied here
   and proved from interchange alone ([dvert_unit_hcomp]); what remains is
   the sub-setoid bookkeeping of [Category_from_Metacategory] run at two
   levels and interlocked.  That is ledgered, with the exact missing piece
   named at [dvert_unit_hcomp].

--------
nLab:      https://ncatlab.org/nlab/show/strict+2-category
   nLab:      https://ncatlab.org/nlab/show/2-category

   严格 2-范畴有 0-胞、1-胞与 2-胞，垂直与水平复合严格结合且有单位，并服从交换律
   (interchange)。与弱 2-范畴/双范畴（Theory/Bicategory.v）相对，严格性使重括号与单位调整
   在表面上为恒等。本文件给出严格 2-范畴类与交换律；长历史短文后续可续译。
*)

(*
Why two dimensions, and why the interchange law is the whole story

   nLab:  https://ncatlab.org/nlab/show/2-category
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Paper: Bénabou, “Introduction to bicategories”, Lecture Notes in
          Mathematics 47 (1967), 1-77
   Paper: Kelly, Street, “Review of the elements of 2-categories”, Lecture
          Notes in Mathematics 420 (1974), 75-103

   Categories organise objects and maps; but the maps between categories —
   functors — themselves carry maps, the natural transformations, and once
   those are present two ways of composing them appear at once.  Mac Lane's
   Theorem 1 is the observation that these two compositions are not merely
   coexistent but LOCKED TOGETHER by the single equation (5): a 2x2 grid of
   transformations may be assembled rows-first or columns-first with the
   same result.  Everything two-dimensional follows from that lock.
   Whiskering is the special case in which one factor is an identity
   ([twhisker_l], [twhisker_r]), and Mac Lane's display (3) — that a
   horizontal composite factors as a whiskering after a whiskering, in
   either order — is exactly interchange with two identities plugged in
   ([thcomp_whisker_left], [thcomp_whisker_right] below).

   The interchange law also explains why the two-dimensional world is not
   simply one-dimensional twice over.  Mac Lane's own Exercise 5 of §II.5 is
   the Eckmann-Hilton argument: two everywhere-defined operations with a
   COMMON unit satisfying (5) coincide and are commutative.  In a general
   2-category the two compositions have DIFFERENT units — that is precisely
   what def 3 legislates about — and the argument only bites where the units
   collapse, which is why the endomorphism 2-cells of an identity 1-cell
   form a commutative monoid while the whole structure does not degenerate.

   Bénabou's bicategories (1967) weaken the present notion by replacing the
   equations governing 1-cell composition with coherent isomorphisms; Kelly
   and Street's review is the standard source for the strict theory and its
   calculus of pasting and mates.  In this library the weak notion lives in
   Theory/Bicategory.v and its motivating model in Instance/Cat/Bicategory.v;
   the strict notion lives here, and the two meet in the observation, proved
   in Instance/Cat/TwoCategory.v, that every coherence cell of the
   bicategory `Cat_Bicategory` has IDENTITY components.  Double categories,
   Ehresmann's 1963 notion, keep two kinds of 1-cell rather than one and are
   the more general shape; Mac Lane's def 3 is the condition singling out
   the 2-categories among them.

--------
为什么是二维，以及为什么交换律就是全部故事

nLab: https://ncatlab.org/nlab/show/2-category
nLab: https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
论文: Bénabou, 《双范畴简介》, 数学讲义 47 (1967), 1-77
论文: Kelly, Street, 《二维范畴要素综述》, 数学讲义 420 (1974), 75-103

范畴组织对象和映射；但是范畴之间的映射——函子——本身也携带映射，即自然变换，一旦这些存在，就会同时出现两种组合它们的方式。Mac Lane 的定理 1 的观察是，这两种组合不仅仅是共存的，而是通过单一方程 (5) 紧密连接在一起：一个 2x2 的变换网格可以先按行组合，也可以先按列组合，结果相同。所有二维的事情都由这种锁定关系决定。 Whiskering 是一种特殊情况，其中一个因子是恒等 ([twhisker_l], [twhisker_r])，而 Mac Lane 的展示 (3) —— 一个水平复合可以分解为先后任意顺序的 whiskering —— 正是两恒等映射代入时的交换关系 ([thcomp_whisker_left], [thcomp_whisker_right] 以下) 。

交换律也解释了为什么二维世界并不是简单地重复一维两次。Mac Lane 自己在 §II.5 的练习 5 就是 Eckmann-Hilton 论证：两个在任何地方都定义的运算，如果有一个共同的单位并且满足 (5)，那么它们相同且可交换。在一般的 2-范畴中，这两个合成具有不同的单位——这正是定义 3 所规定的——而该论证只在单位合并时才成立，这就是为什么一个单位 1-态射的自同态 2-态射形成一个交换幺半群，而整个结构并未退化。

贝纳布的双范畴（1967）通过将支配 1-态射组合的方程替换为相干同构来弱化当前的概念；凯利（Kelly）和斯特里特（Street）的综述是严格理论及其拼接与伴随演算的标准来源。在这个库中，弱概念存在于 Theory/Bicategory.v 中，其激励模型存在于 Instance/Cat/Bicategory.v 中；严格概念存在于此处，而两者在 Instance/Cat/TwoCategory.v 中的观察中相交，该观察证明双范畴 `Cat_Bicategory` 的每个相干单元都有恒等分量。双范畴，埃雷斯曼（Ehresmann）1963 年的概念，保持两种 1-态射而不是一种，并且是更一般的结构；麦克莱恩（Mac Lane）的定义 3 是区分其中 2-范畴的条件。
*)

(** ** The globular presentation (Mac Lane §XII.3, Riehl 1.7.8) / ** 球状表示（Mac Lane §XII.3, Riehl 1.7.8） *)

Class TwoCategory : Type := {
  (* 0-cells and 1-cells, as an ordinary category. / 作为一个普通范畴的0-胞和1-胞。 *)
  tcat : Category;

  (* 2-cells, indexed by a PARALLEL pair of 1-cells (the globular shape). / 2-胞，按一对平行的1-胞索引（球状形状）。 *)
  tcell {a b : tcat} (f g : a ~{tcat}~> b) : Type;
  tcell_setoid {a b : tcat} {f g : a ~{tcat}~> b} : Setoid (tcell f g);

  (* Vertical composition, making each hom into a category ([thom]). / 垂直构图，将每个 hom 归入一个范畴 ([thom])。 *)
  tid2 {a b : tcat} (f : a ~{tcat}~> b) : tcell f f;

  tvcomp {a b : tcat} {f g h : a ~{tcat}~> b} :
    tcell g h → tcell f g → tcell f h;

  tvcomp_respects {a b : tcat} {f g h : a ~{tcat}~> b} :
    Proper (equiv ==> equiv ==> equiv) (@tvcomp a b f g h);

  tvid_left {a b : tcat} {f g : a ~{tcat}~> b} (α : tcell f g) :
    tvcomp (tid2 g) α ≈ α;

  tvid_right {a b : tcat} {f g : a ~{tcat}~> b} (α : tcell f g) :
    tvcomp α (tid2 f) ≈ α;

  tvassoc {a b : tcat} {f g h k : a ~{tcat}~> b}
    (γ : tcell h k) (β : tcell g h) (α : tcell f g) :
    tvcomp γ (tvcomp β α) ≈ tvcomp (tvcomp γ β) α;

  (*
Horizontal composition, lying over composition of 1-cells.  The outer
     factor comes first, matching the order of `∘`.

--------
水平组合，位于1-元胞组合之上。外层因子先出现，与`∘`的顺序匹配。
*)
  thcomp {a b c : tcat} {f f' : a ~{tcat}~> b} {g g' : b ~{tcat}~> c} :
    tcell g g' → tcell f f' → tcell (g ∘ f) (g' ∘ f');

  thcomp_respects {a b c : tcat} {f f' : a ~{tcat}~> b}
    {g g' : b ~{tcat}~> c} :
    Proper (equiv ==> equiv ==> equiv) (@thcomp a b c f f' g g');

  (*
Mac Lane's `1_{g f} = 1_g ∘ 1_f`: horizontal composition preserves the
     vertical identities.

--------
Mac Lane 的 `1_{g f} = 1_g ∘ 1_f`：水平组合保持了垂直同一性。
*)
  thcomp_id {a b c : tcat} (f : a ~{tcat}~> b) (g : b ~{tcat}~> c) :
    thcomp (tid2 g) (tid2 f) ≈ tid2 (g ∘ f);

  (* The interchange law, Mac Lane §II.5 display (5). / 交换律，Mac Lane §II.5 图示 (5)。 *)
  tinterchange {a b c : tcat} {f f' f'' : a ~{tcat}~> b}
    {g g' g'' : b ~{tcat}~> c}
    (δ : tcell g' g'') (γ : tcell g g') (β : tcell f' f'') (α : tcell f f') :
    thcomp (tvcomp δ γ) (tvcomp β α) ≈ tvcomp (thcomp δ β) (thcomp γ α);

  (*
STRICTNESS.  Re-bracketing and unit adjustment of the 1-cell boundary
     identify the corresponding types of 2-cells; the identifications are
     data, and the laws below say they behave as identities.  See the header
     for why this, and not an equation of 1-cells, is what is asked.

--------
严格性。重新分组和单元调整1-胞边界
    确定对应的2-胞类型；这些识别是
    数据，下面的定律说明它们表现为恒等式。见标题
    了解为何要求的是这个，而不是1-胞的方程式。
*)
  tassoc_cast {a b c d : tcat} {f f' : a ~{tcat}~> b}
    {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d} :
    tcell (h ∘ (g ∘ f)) (h' ∘ (g' ∘ f')) →
    tcell ((h ∘ g) ∘ f) ((h' ∘ g') ∘ f');

  tunitl_cast {a b : tcat} {f f' : a ~{tcat}~> b} :
    tcell (id ∘ f) (id ∘ f') → tcell f f';

  tunitr_cast {a b : tcat} {f f' : a ~{tcat}~> b} :
    tcell (f ∘ id) (f' ∘ id) → tcell f f';

  tassoc_cast_respects {a b c d : tcat} {f f' : a ~{tcat}~> b}
    {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d} :
    Proper (equiv ==> equiv) (@tassoc_cast a b c d f f' g g' h h');

  tunitl_cast_respects {a b : tcat} {f f' : a ~{tcat}~> b} :
    Proper (equiv ==> equiv) (@tunitl_cast a b f f');

  tunitr_cast_respects {a b : tcat} {f f' : a ~{tcat}~> b} :
    Proper (equiv ==> equiv) (@tunitr_cast a b f f');

  tassoc_cast_vcomp {a b c d : tcat} {f f' f'' : a ~{tcat}~> b}
    {g g' g'' : b ~{tcat}~> c} {h h' h'' : c ~{tcat}~> d}
    (β : tcell (h' ∘ (g' ∘ f')) (h'' ∘ (g'' ∘ f'')))
    (α : tcell (h ∘ (g ∘ f)) (h' ∘ (g' ∘ f'))) :
    tassoc_cast (tvcomp β α) ≈ tvcomp (tassoc_cast β) (tassoc_cast α);

  tunitl_cast_vcomp {a b : tcat} {f f' f'' : a ~{tcat}~> b}
    (β : tcell (id ∘ f') (id ∘ f'')) (α : tcell (id ∘ f) (id ∘ f')) :
    tunitl_cast (tvcomp β α) ≈ tvcomp (tunitl_cast β) (tunitl_cast α);

  tunitr_cast_vcomp {a b : tcat} {f f' f'' : a ~{tcat}~> b}
    (β : tcell (f' ∘ id) (f'' ∘ id)) (α : tcell (f ∘ id) (f' ∘ id)) :
    tunitr_cast (tvcomp β α) ≈ tvcomp (tunitr_cast β) (tunitr_cast α);

  (*
Horizontal composition is associative and unital ON THE NOSE, modulo
     the boundary identifications.

--------
水平组合在严格意义上是结合和幺元的，模掉边界同一化。
*)
  thassoc {a b c d : tcat} {f f' : a ~{tcat}~> b} {g g' : b ~{tcat}~> c}
    {h h' : c ~{tcat}~> d}
    (γ : tcell h h') (β : tcell g g') (α : tcell f f') :
    tassoc_cast (thcomp γ (thcomp β α)) ≈ thcomp (thcomp γ β) α;

  thunit_left {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
    tunitl_cast (thcomp (tid2 (@id tcat b)) α) ≈ α;

  thunit_right {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
    tunitr_cast (thcomp α (tid2 (@id tcat a))) ≈ α
}.

#[export] Existing Instance tcell_setoid.
#[export] Existing Instance tvcomp_respects.
#[export] Existing Instance thcomp_respects.
#[export] Existing Instance tassoc_cast_respects.
#[export] Existing Instance tunitl_cast_respects.
#[export] Existing Instance tunitr_cast_respects.

(**
** The hom-categories

    Riehl 1.7.8 asks that the 2-cells between 1-cells `a ~> b` form a
    category under vertical composition; here that is a construction rather
    than a field, assembled from [tid2], [tvcomp] and their three laws.

--------
** 同态范畴

Riehl 1.7.8 要求 1-态之间的 2-态 `a ~> b` 在垂直组合下形成一个范畴；在这里，这是一种构造而不是一个域，由 [tid2]、[tvcomp] 及其三个定律组装而成。
*)

Definition thom `{K : TwoCategory} (a b : @tcat K) : Category := {|
  obj              := a ~{tcat}~> b;
  hom              := @tcell K a b;
  homset           := @tcell_setoid K a b;
  id               := @tid2 K a b;
  compose          := @tvcomp K a b;
  compose_respects := @tvcomp_respects K a b;
  id_left          := @tvid_left K a b;
  id_right         := @tvid_right K a b;
  comp_assoc       := @tvassoc K a b;
  comp_assoc_sym   := fun f g h k γ β α =>
    symmetry (@tvassoc K a b f g h k γ β α)
|}.

Section TwoCategoryLemmas.

Context {K : TwoCategory}.

(**
** Whiskering (Mac Lane §II.5, the convention of def 1)

    Mac Lane lets a functor symbol stand for its identity transformation, so
    that `S' ∘ τ` and `τ' ∘ T` denote horizontal composites one of whose
    factors is an identity.  Those are the two whiskerings.

--------
** 胡须操作（Mac Lane §II.5，定义 1 的约定）

    Mac Lane 允许用函子符号表示其恒等变换，因此 `S' ∘ τ` 和 `τ' ∘ T` 表示水平复合，其中一个因子是恒等变换。这就是两种胡须操作。
*)

Definition twhisker_l {a b c : tcat} (g : b ~{tcat}~> c)
  {f f' : a ~{tcat}~> b} (α : tcell f f') : tcell (g ∘ f) (g ∘ f') :=
  thcomp (tid2 g) α.

Definition twhisker_r {a b c : tcat} {g g' : b ~{tcat}~> c}
  (β : tcell g g') (f : a ~{tcat}~> b) : tcell (g ∘ f) (g' ∘ f) :=
  thcomp β (tid2 f).

#[local] Instance twhisker_l_respects {a b c : tcat} (g : b ~{tcat}~> c)
  (f f' : a ~{tcat}~> b) :
  Proper (equiv ==> equiv) (@twhisker_l a b c g f f').
Proof.
  proper.
  unfold twhisker_l.
  now apply thcomp_respects.
Qed.

#[local] Instance twhisker_r_respects {a b c : tcat}
  (g g' : b ~{tcat}~> c) (f : a ~{tcat}~> b) :
  Proper (equiv ==> equiv) (fun β => @twhisker_r a b c g g' β f).
Proof.
  proper.
  unfold twhisker_r.
  now apply thcomp_respects.
Qed.

(*
Whiskering by an identity 1-cell is (after the boundary identification)
   the cell itself: the two unit laws restated in whiskering form.

--------
通过恒等 1-元胞的胡须操作是（在边界识别之后）元胞自身：以胡须操作形式重述的两个单位律。
*)
Lemma twhisker_l_id {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tunitl_cast (twhisker_l (@id tcat b) α) ≈ α.
Proof. apply thunit_left. Qed.

Lemma twhisker_r_id {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tunitr_cast (twhisker_r α (@id tcat a)) ≈ α.
Proof. apply thunit_right. Qed.

(*
Whiskering preserves identities and vertical composites: each whiskering
   is a functor between hom-categories, which is Mac Lane's remark that
   `S' ∘ (-)` and `(-) ∘ T` are functorial.

--------
胡须化保持了同一性和垂直复合：每个胡须化都是范畴之间的函子，这是 Mac Lane 的评论，即 `S' ∘ (-)` 和 `(-) ∘ T` 是函子性的。
*)
Lemma twhisker_l_ident {a b c : tcat} (g : b ~{tcat}~> c)
  (f : a ~{tcat}~> b) : twhisker_l g (tid2 f) ≈ tid2 (g ∘ f).
Proof. apply thcomp_id. Qed.

Lemma twhisker_r_ident {a b c : tcat} (g : b ~{tcat}~> c)
  (f : a ~{tcat}~> b) : twhisker_r (tid2 g) f ≈ tid2 (g ∘ f).
Proof. apply thcomp_id. Qed.

Lemma twhisker_l_vcomp {a b c : tcat} (g : b ~{tcat}~> c)
  {f f' f'' : a ~{tcat}~> b} (β : tcell f' f'') (α : tcell f f') :
  twhisker_l g (tvcomp β α) ≈ tvcomp (twhisker_l g β) (twhisker_l g α).
Proof.
  unfold twhisker_l.
  rewrite <- tinterchange.
  apply thcomp_respects; [| reflexivity ].
  now rewrite tvid_left.
Qed.

Lemma twhisker_r_vcomp {a b c : tcat} {g g' g'' : b ~{tcat}~> c}
  (δ : tcell g' g'') (γ : tcell g g') (f : a ~{tcat}~> b) :
  twhisker_r (tvcomp δ γ) f ≈ tvcomp (twhisker_r δ f) (twhisker_r γ f).
Proof.
  unfold twhisker_r.
  rewrite <- tinterchange.
  apply thcomp_respects; [ reflexivity |].
  now rewrite tvid_left.
Qed.

(**
** Mac Lane's display (3): a horizontal composite factors two ways

    `τ' ∘ τ = (T' ∘ τ) · (τ' ∘ S) = (τ' ∘ T) · (S' ∘ τ)`, the two diagonals
    of the naturality square of the Godement product.  Both are interchange
    with an identity plugged into one slot.

--------
** Mac Lane 的展示 (3)：一个水平复合可以两种方式分解

    `τ' ∘ τ = (T' ∘ τ) · (τ' ∘ S) = (τ' ∘ T) · (S' ∘ τ)`，自然性方格中 Godement 积的两条对角线。两者都可以与其中一个槽位插入的单位进行交换。
*)

Lemma thcomp_whisker_left {a b c : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} (β : tcell g g') (α : tcell f f') :
  thcomp β α ≈ tvcomp (twhisker_r β f') (twhisker_l g α).
Proof.
  unfold twhisker_l, twhisker_r.
  rewrite <- tinterchange.
  apply thcomp_respects.
  - now rewrite tvid_right.
  - now rewrite tvid_left.
Qed.

Lemma thcomp_whisker_right {a b c : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} (β : tcell g g') (α : tcell f f') :
  thcomp β α ≈ tvcomp (twhisker_l g' α) (twhisker_r β f).
Proof.
  unfold twhisker_l, twhisker_r.
  rewrite <- tinterchange.
  apply thcomp_respects.
  - now rewrite tvid_left.
  - now rewrite tvid_right.
Qed.

(*
Consequently the two factorisations agree: the Godement square commutes,
   which is Mac Lane's remark that the horizontal composite is the diagonal
   of a commuting square.

--------
因此这两个分解是一致的：Godement 方格是可交换的，这就是 Mac Lane 的评论，即水平复合是一个可交换方格的对角线。
*)
Corollary tgodement_square {a b c : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} (β : tcell g g') (α : tcell f f') :
  tvcomp (twhisker_r β f') (twhisker_l g α)
    ≈ tvcomp (twhisker_l g' α) (twhisker_r β f).
Proof.
  rewrite <- thcomp_whisker_left.
  apply thcomp_whisker_right.
Qed.

(**
** The boundary identifications carry identities to identities

    Not fields: each follows from the corresponding strictness law together
    with [thcomp_id].

--------
** 边界识别将恒等传递给恒等

    而不是字段：每个都与对应的严格性法则以及 [thcomp_id] 一起执行。
*)

Lemma tassoc_cast_id {a b c d : tcat} (f : a ~{tcat}~> b)
  (g : b ~{tcat}~> c) (h : c ~{tcat}~> d) :
  tassoc_cast (tid2 (h ∘ (g ∘ f))) ≈ tid2 ((h ∘ g) ∘ f).
Proof.
  rewrite <- (thcomp_id (g ∘ f) h).
  rewrite <- (thcomp_id f g).
  rewrite thassoc.
  now rewrite thcomp_id, thcomp_id.
Qed.

Lemma tunitl_cast_id {a b : tcat} (f : a ~{tcat}~> b) :
  tunitl_cast (tid2 (@id tcat b ∘ f)) ≈ tid2 f.
Proof.
  rewrite <- (thcomp_id f (@id tcat b)).
  apply thunit_left.
Qed.

Lemma tunitr_cast_id {a b : tcat} (f : a ~{tcat}~> b) :
  tunitr_cast (tid2 (f ∘ @id tcat a)) ≈ tid2 f.
Proof.
  rewrite <- (thcomp_id (@id tcat a) f).
  apply thunit_right.
Qed.

(**
** Mac Lane's def-3 condition in the globular presentation

    A 2-cell is a unit for vertical composition when composing with it
    changes nothing; it is a unit for horizontal composition when
    whiskering by it changes nothing, once the boundary identification is
    applied.  Both predicates are typed, and the second is only typeable at
    2-cells on an IDENTITY 1-cell — which is already Mac Lane's point: in
    the globular presentation the `∘`-identities sit among the
    `·`-identities by construction.

--------
** Mac Lane 在球状表示中的 def-3 条件

当与之进行垂直组合时，一个 2-胞是单位单元，如果与它组合不会改变任何东西；当进行水平组合时，如果通过它的拍打不改变任何东西（在应用边界识别后），它也是单位单元。两个谓词都是有类型的，并且第二个谓词仅在一个 IDENTITY 1-胞上的 2-胞上可类型化——这正是 Mac Lane 的观点：在球状表示中，`∘`-恒等元通过构造位于 `·`-恒等元之中。
*)

Definition IsVUnit {a b : tcat} {f : a ~{tcat}~> b} (u : tcell f f) : Type :=
  (∀ (g : a ~{tcat}~> b) (α : tcell f g), tvcomp α u ≈ α) ∧
  (∀ (g : a ~{tcat}~> b) (α : tcell g f), tvcomp u α ≈ α).

Definition IsHUnit {a : tcat} (u : tcell (@id tcat a) (@id tcat a)) : Type :=
  (∀ (b : tcat) (f f' : a ~{tcat}~> b) (α : tcell f f'),
     tunitr_cast (thcomp α u) ≈ α) ∧
  (∀ (b : tcat) (f f' : b ~{tcat}~> a) (α : tcell f f'),
     tunitl_cast (thcomp u α) ≈ α).

(*
Mac Lane §II.5 Theorem 1's closing clause, and the condition his def 3
   abstracts from it: the identity 2-cell on an identity 1-cell is a unit
   for BOTH compositions.

--------
Mac Lane §II.5 定理1的结尾条款，以及他的定义3从中抽象出的条件：一个单位1-胞上的恒等2-胞对于两种组合都是单位。
*)
Theorem twocategory_def3 (a : tcat) :
  IsVUnit (tid2 (@id tcat a)) ∧ IsHUnit (tid2 (@id tcat a)).
Proof.
  split.
  - split; intros g α.
    + apply tvid_right.
    + apply tvid_left.
  - split; intros b f f' α.
    + apply thunit_right.
    + apply thunit_left.
Qed.

(*
The inclusion is one-directional, which is why def 3 is a condition and
   not a symmetry: every [tid2 f] is a `·`-unit, whatever f is, while only
   those at an identity 1-cell are even typeable as `∘`-units.

--------
包含是单向的，这就是为什么定义 3 是一个条件而不是对称性：每个 [tid2 f] 都是 `·` 单元，无论 f 是什么，而只有那些在恒等 1-单元处的才有可能被称为 `∘` 单元。
*)
Theorem twocategory_tid2_vunit {a b : tcat} (f : a ~{tcat}~> b) :
  IsVUnit (tid2 f).
Proof.
  split; intros g α.
  - apply tvid_right.
  - apply tvid_left.
Qed.

End TwoCategoryLemmas.

Arguments IsVUnit {_ _ _ _} _.
Arguments IsHUnit {_ _} _.

(**
** The arrows-only presentation (Mac Lane §II.5 definitions 2 and 3)

    Mac Lane's double category is “a set which is the set of arrows for two
    different composition operations which together satisfy the interchange
    law”.  A composition operation on a set of arrows, in his sense, is
    exactly the data of Theory/Metacategory/General.v's [Metacategory]
    minus the arrow type: partial, given as the graph [mccomp] of a
    single-valued relation, with the two halves of axiom (i), axiom (ii),
    and axiom (iii) in the conjunctive form that file establishes as the
    correct one.  [MetaComp] is that data over a fixed setoid, so that two
    of them may be laid on ONE collection of cells.

--------
** 仅箭头的表述（Mac Lane §II.5 定义 2 和 3）

Mac Lane 的双重范畴是“一个集合，它是两种不同组合运算的箭头集合，这两种运算共同满足交换律”。在他的意义上，一个箭头集合上的组合运算，正是 Theory/Metacategory/General.v 中的 [Metacategory] 数据，去掉箭头类型：部分定义，通过图 [mccomp] 给出单值关系，其中包含公理 (i) 的两个部分、公理 (ii) 和公理 (iii)，以该文件确定的正确的合取形式表示。[MetaComp] 是固定集合上的这些数据，以便其中两个可以在同一集合的单元上叠加。
*)

Record MetaComp {A : Type} (S : Setoid A) : Type := {
  (* [mccomp g f h] reads “g∙f is defined, and equals h”. / [mccomp g f h] 读取“g∙f 已定义，并且等于 h”。 *)
  mccomp : A → A → A → Type;

  mcdefined (g f : A) := ∃ h, mccomp g f h;

  mccomp_respects {g g' f f' h h'} :
    @equiv _ S g g' → @equiv _ S f f' → @equiv _ S h h' →
    mccomp g f h → mccomp g' f' h';

  mccomp_unique {g f h h'} :
    mccomp g f h → mccomp g f h' → @equiv _ S h h';

  mccomp_assoc_l {k g f kg kgf} :
    mccomp k g kg → mccomp kg f kgf → ∃ gf, mccomp g f gf ∧ mccomp k gf kgf;

  mccomp_assoc_r {k g f gf kgf} :
    mccomp g f gf → mccomp k gf kgf → ∃ kg, mccomp k g kg ∧ mccomp kg f kgf;

  mccomp_match {k g f kg gf} :
    mccomp k g kg → mccomp g f gf → ∃ kgf, mccomp kg f kgf;

  mcident (u : A) :=
    (∀ f, mcdefined f u → mccomp f u f) ∧
    (∀ g, mcdefined u g → mccomp u g g);

  mcident_law (g : A) :
    ∃ u u', (mcident u ∧ mcident u') ∧ (mcdefined g u ∧ mcdefined u' g)
}.

Arguments mccomp {A S} _ _ _ _.
Arguments mcdefined {A S} _ _ _ /.
Arguments mccomp_respects {A S} _ {g g' f f' h h'} _ _ _ _.
Arguments mccomp_unique {A S} _ {g f h h'} _ _.
Arguments mccomp_assoc_l {A S} _ {k g f kg kgf} _ _.
Arguments mccomp_assoc_r {A S} _ {k g f gf kgf} _ _.
Arguments mccomp_match {A S} _ {k g f kg gf} _ _.
Arguments mcident {A S} _ _ /.
Arguments mcident_law {A S} _ _.

(*
The two packagings agree: a [MetaComp] over a setoid is a
   [Metacategory] on that setoid's carrier, and conversely.  Neither
   direction has any proof content — both are field-for-field
   repackagings — which is the point: the arrows-only classes below are
   Theory/Metacategory/General.v's notion, laid twice on one collection.

--------
这两种封装是一致的：一个集合上的 [MetaComp] 就是该集合载体上的 [Metacategory]，反之亦然。两个方向都没有任何证明内容——它们都是逐字段的重新封装——这正是重点：下面的仅箭头类是 Theory/Metacategory/General.v 的概念，在同一个集合上应用了两次。
*)

Definition Metacategory_of_MetaComp {A : Type} {S : Setoid A}
  (M : MetaComp S) : Metacategory := {|
  marr             := A;
  marr_setoid      := S;
  mcomp            := mccomp M;
  mcomp_respects   := @mccomp_respects _ _ M;
  mcomp_unique     := @mccomp_unique _ _ M;
  mcomp_assoc_l    := @mccomp_assoc_l _ _ M;
  mcomp_assoc_r    := @mccomp_assoc_r _ _ M;
  mcomp_match      := @mccomp_match _ _ M;
  mident_law       := @mcident_law _ _ M
|}.

Definition MetaComp_of_Metacategory (M : Metacategory) :
  MetaComp (marr_setoid M) := {|
  mccomp            := mcomp M;
  mccomp_respects   := @mcomp_respects M;
  mccomp_unique     := @mcomp_unique M;
  mccomp_assoc_l    := @mcomp_assoc_l M;
  mccomp_assoc_r    := @mcomp_assoc_r M;
  mccomp_match      := @mcomp_match M;
  mcident_law       := @mident_law M
|}.

(** *** Definition 2: a double category / *** 定义 2：一个双重范畴 *)

Record StrictDoubleCategory : Type := {
  (*
“a set which is the set of arrows for two different composition
     operations” — here a setoid of cells, since every collection in this
     library carries its own equality.

--------
“一个集合，它是两种不同组合操作的箭头集合”——这里是一个单元的集合，因为这个库中的每一个集合都有其自身的等式。
*)
  dcell : Type;
  dcell_setoid : Setoid dcell;

  dvert  : MetaComp dcell_setoid;       (* the first composition,  `·` / 第一篇作品，`·` *)
  dhoriz : MetaComp dcell_setoid;       (* the second composition, `∘` / 第二篇作品，`∘` *)

  (*
“which together satisfy the interchange law”: Mac Lane's display (5),
     `(τ' · σ') ∘ (τ · σ) = (τ' ∘ τ) · (σ' ∘ σ)`, stated for partial
     operations in the form of his remark 2 — the equation is asserted
     whenever the composites on both sides are defined.

--------
“它们共同满足交换律”：Mac Lane 在显示式 (5) 中，`(τ' · σ') ∘ (τ · σ) = (τ' ∘ τ) · (σ' ∘ σ)`，对于部分运算以他的备注 2 的形式说明——当两边的复合运算都已定义时，该方程被断言。
*)
  dinterchange {σ τ σ' τ' p q r s x y : dcell} :
    mccomp dvert τ σ p →                (* p = τ · σ / p = τ · σ *)
    mccomp dvert τ' σ' q →              (* q = τ' · σ' / q = τ' · σ' *)
    mccomp dhoriz q p x →               (* x = (τ' · σ') ∘ (τ · σ) / x = (τ' · σ') ∘ (τ · σ) *)
    mccomp dhoriz τ' τ r →              (* r = τ' ∘ τ / r = τ' ∘ τ *)
    mccomp dhoriz σ' σ s →              (* s = σ' ∘ σ / s = σ' ∘ σ *)
    mccomp dvert r s y →                (* y = (τ' ∘ τ) · (σ' ∘ σ) / y = (τ' ∘ τ) · (σ' ∘ σ) *)
    @equiv _ dcell_setoid x y
}.

#[export] Existing Instance dcell_setoid.

(*
The two compositions as metacategories, hence — through
   Theory/Metacategory/General.v's passage — as ordinary categories.  This
   is Mac Lane's Theorem 1 phrase “the arrow set of two different
   categories” made literal: [dvert_Category] has the 1-cells of one
   direction as its objects and [dhoriz_Category] those of the other.

--------
作为元范畴的两个组合，因此——通过 Theory/Metacategory/General.v 的段落——作为普通范畴。这是 Mac Lane 定理 1 中“两个不同范畴的箭头集合”的字面意义：[dvert_Category] 具有一个方向的 1-胞作为其对象，而 [dhoriz_Category] 具有另一个方向的 1-胞。
*)

Definition dvert_Meta (D : StrictDoubleCategory) : Metacategory :=
  Metacategory_of_MetaComp (dvert D).

Definition dhoriz_Meta (D : StrictDoubleCategory) : Metacategory :=
  Metacategory_of_MetaComp (dhoriz D).

Definition dvert_Category (D : StrictDoubleCategory) : Category :=
  Category_from_Metacategory (dvert_Meta D).

Definition dhoriz_Category (D : StrictDoubleCategory) : Category :=
  Category_from_Metacategory (dhoriz_Meta D).

(*
The two identity predicates, in Mac Lane's sense of an arrow that is a
   unit for a composition wherever that composition is defined.

--------
这两个同一性谓词，在麦克莱恩的意义上，是指一个箭头，它在组成定义的任何地方都是组合的单位。
*)

Definition dvident (D : StrictDoubleCategory) (u : dcell D) : Type :=
  mcident (dvert D) u.

Definition dhident (D : StrictDoubleCategory) (u : dcell D) : Type :=
  mcident (dhoriz D) u.

(**
*** Definition 3: a 2-category

    “A 2-category is a double category in which every identity arrow for the
    first composition is also an identity for the second.”  The orientation
    follows Theorem 1, whose closing clause reads “every arrow that is an
    identity for ∘ is also an identity for ·”: the HORIZONTAL identities are
    required to be vertical ones.  The converse is not asked for, and does
    not hold — [NatSq_vid_is_not_hid] below witnesses the asymmetry
    concretely, and [twocategory_tid2_vunit] is the globular half that
    DOES hold.

--------
*** 定义 3：二范畴

“二范畴是一个双范畴，其中第一合成的每一个恒等箭头也是第二合成的恒等箭头。” 方向遵循定理 1，其结尾条款写道“每一个对于 ∘ 是恒等的箭头也是对于 · 的恒等箭头”：水平恒等箭头需要是垂直恒等箭头。反之没有要求，并且不成立——下面的 [NatSq_vid_is_not_hid] 具体证明了这种不对称，而 [twocategory_tid2_vunit] 是成立的球面一半。
*)

Record StrictTwoCategory : Type := {
  s2double : StrictDoubleCategory;

  s2ident_coincide : ∀ u : dcell s2double,
    dhident s2double u → dvident s2double u
}.

Require Import Coq.micromega.Lia.

(**
** Mac Lane's negative example: commuting squares are not a 2-category

    §II.5's definition of a 2-category closes by recording that the
    commutative squares of Set form a double category which is not one.
    The witness below is the smallest faithful form of that example: the
    commuting squares of a ONE-OBJECT category, namely the delooping of the
    additive monoid of naturals.  One object is what keeps the arrows-only
    packaging honest — with several objects, composability of two cells
    would ask for an EQUATION between objects, the hypothesis
    Theory/Metacategory/General.v carries as ObjUIP — and it costs nothing,
    since the phenomenon at issue concerns the vertical arrows, not the
    objects.

    A square

        · --t--> ·                  is a quadruple (t, l, r, b) of naturals
        |        |                  subject to the commuting condition
        l        r                       b + l = r + t,
        v        v
        · --b--> ·                  composing by addition in each direction.

    Its two compositions are vertical pasting (matching bottom to top) and
    horizontal pasting (matching right to left); together they satisfy the
    interchange law, so this is a [StrictDoubleCategory].  It is not a
    [StrictTwoCategory]: the horizontal identity on the vertical arrow 1 is
    the square (0, 1, 1, 0), which is a unit for horizontal pasting but not
    for vertical pasting, since pasting it under itself doubles its
    vertical edges.  The same square is what Construction/Sq.v's model
    produces for an arbitrary base — there the horizontal identity on a
    vertical morphism [u] has vertical edges [u], while a vertical identity
    square has vertical edges [id] — and Instance/Cat/TwoCategory.v records
    that these cells ARE that model's squares.

--------
** Mac Lane 的负面例子：交换方不是 2-范畴

§II.5 对 2-范畴的定义以记录 Set 的交换方形形成一个不是双范畴的双范畴而告终。下面的例子是该例子的最小忠实形式：一个单对象范畴的交换方形，也就是自然数加法幺半群的去环绕。一个对象保证了仅箭头的包装保持诚实——如果有多个对象，两个单元的可组合性将要求对象之间存在一个等式，这在 Theory/Metacategory/General.v 中作为 ObjUIP 假设——而且这不会产生任何代价，因为讨论的现象涉及垂直箭头，而不是对象。

一个正方形

· --t--> ·                  是自然数的四元组 (t, l, r, b)
        |        |                  满足交换条件
        l        r                       b + l = r + t,
        v        v
        · --b--> ·                  在每个方向上通过加法进行组合。

它的两种组合方式是垂直粘贴（底对顶匹配）和水平粘贴（右对左匹配）；它们一起满足交换律，所以这是一个 [StrictDoubleCategory]。它不是一个 [StrictTwoCategory]：垂直箭头 1 上的水平单位是平方 (0, 1, 1, 0)，它是水平粘贴的单位，但不是垂直粘贴的单位，因为将它垂直粘贴到自身下方会使其垂直边加倍。对于任意基对象，Construction/Sq.v 的模型产生的正是同样的平方——在那里，垂直态射 [u] 上的水平单位具有垂直边 [u]，而垂直单位平方具有垂直边 [id]——而 Instance/Cat/TwoCategory.v 记录了这些单元确实是该模型的平方。
*)

Record NatSq : Type := {
  nsq_top   : nat;
  nsq_left  : nat;
  nsq_right : nat;
  nsq_bot   : nat;
  nsq_comm  : (nsq_bot + nsq_left = nsq_right + nsq_top)%nat
}.

Definition mkNatSq (t l r b : nat) (H : (b + l = r + t)%nat) : NatSq :=
  {| nsq_top   := t;
     nsq_left  := l;
     nsq_right := r;
     nsq_bot   := b;
     nsq_comm  := H |}.

(*
Two squares are the same when their four edges are; the commuting proof
   carries no information beyond them.

--------
当两个正方形的四条边相同时，它们是相同的；交换证明不包含超出这些边的信息。
*)
Definition NatSq_eq (x y : NatSq) : Type :=
  (nsq_top x = nsq_top y) ∧ (nsq_left x = nsq_left y) ∧
  (nsq_right x = nsq_right y) ∧ (nsq_bot x = nsq_bot y).

Program Definition NatSq_Setoid : Setoid NatSq := {|
  equiv := NatSq_eq
|}.
Next Obligation.
  constructor.
  - intros x; now repeat split.
  - intros x y [? [? [? ?]]]; now repeat split.
  - intros x y z [? [? [? ?]]] [? [? [? ?]]]; repeat split;
      etransitivity; eassumption.
Qed.

(* Vertical pasting: [f] on top, [g] below, matching along [f]'s bottom. / 垂直粘贴：[f] 在上方，[g] 在下方，与 [f] 的底部对齐。 *)
Definition NatSq_vcomp (g f h : NatSq) : Type :=
  (nsq_top g = nsq_bot f) ∧
  (nsq_top h = nsq_top f) ∧
  (nsq_bot h = nsq_bot g) ∧
  (nsq_left h = (nsq_left g + nsq_left f)%nat) ∧
  (nsq_right h = (nsq_right g + nsq_right f)%nat).

(*
Horizontal pasting: [f] on the left, [g] on the right, matching along
   [f]'s right edge.

--------
水平粘贴：[f] 在左边，[g] 在右边，沿 [f] 的右边缘对齐。
*)
Definition NatSq_hcomp (g f h : NatSq) : Type :=
  (nsq_left g = nsq_right f) ∧
  (nsq_left h = nsq_left f) ∧
  (nsq_right h = nsq_right g) ∧
  (nsq_top h = (nsq_top g + nsq_top f)%nat) ∧
  (nsq_bot h = (nsq_bot g + nsq_bot f)%nat).

Definition NatSq_vdefined (g f : NatSq) : Type := ∃ h, NatSq_vcomp g f h.
Definition NatSq_hdefined (g f : NatSq) : Type := ∃ h, NatSq_hcomp g f h.

Definition NatSq_vident (u : NatSq) : Type :=
  (∀ f, NatSq_vdefined f u → NatSq_vcomp f u f) ∧
  (∀ g, NatSq_vdefined u g → NatSq_vcomp u g g).

Definition NatSq_hident (u : NatSq) : Type :=
  (∀ f, NatSq_hdefined f u → NatSq_hcomp f u f) ∧
  (∀ g, NatSq_hdefined u g → NatSq_hcomp u g g).

(*
Every obligation below is arithmetic once the composition hypotheses are
   taken apart.  The edges are left as opaque projections — no square is
   ever destructed — so `lia` sees plain linear equations over atoms.

--------
一旦拆解组成假设，下面的每个义务都是算术的。边缘保持为不透明投影——没有方块会被销毁——因此 `lia` 会看到关于原子的普通线性方程。
*)
#[local] Ltac nsq_hyps :=
  simpl in *;
  repeat match goal with
  | [ H : NatSq_vcomp _ _ _  |- _ ] => destruct H as [? [? [? [? ?]]]]
  | [ H : NatSq_hcomp _ _ _  |- _ ] => destruct H as [? [? [? [? ?]]]]
  | [ H : NatSq_eq _ _       |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : NatSq_vdefined _ _ |- _ ] => destruct H as [? ?]
  | [ H : NatSq_hdefined _ _ |- _ ] => destruct H as [? ?]
  end; simpl in *.

(*
The pasted squares, with their commuting proofs.  Each is arithmetic:
   the two given conditions plus the matching equation give the third.

--------
粘贴的平方及其交换证明。每一个都是算术的：两个给定条件加上匹配的方程得到第三个条件。
*)

Lemma NatSq_vpaste_comm (g f : NatSq) (Hm : nsq_top g = nsq_bot f) :
  (nsq_bot g + (nsq_left g + nsq_left f)
     = (nsq_right g + nsq_right f) + nsq_top f)%nat.
Proof.
  pose proof (nsq_comm f); pose proof (nsq_comm g); lia.
Qed.

Definition NatSq_vpaste (g f : NatSq) (Hm : nsq_top g = nsq_bot f) : NatSq :=
  mkNatSq (nsq_top f) (nsq_left g + nsq_left f)
          (nsq_right g + nsq_right f) (nsq_bot g)
          (NatSq_vpaste_comm g f Hm).

Lemma NatSq_hpaste_comm (g f : NatSq) (Hm : nsq_left g = nsq_right f) :
  ((nsq_bot g + nsq_bot f) + nsq_left f
     = nsq_right g + (nsq_top g + nsq_top f))%nat.
Proof.
  pose proof (nsq_comm f); pose proof (nsq_comm g); lia.
Qed.

Definition NatSq_hpaste (g f : NatSq) (Hm : nsq_left g = nsq_right f)
  : NatSq :=
  mkNatSq (nsq_top g + nsq_top f) (nsq_left f)
          (nsq_right g) (nsq_bot g + nsq_bot f)
          (NatSq_hpaste_comm g f Hm).

Lemma NatSq_vcomp_total (g f : NatSq) (Hm : nsq_top g = nsq_bot f) :
  NatSq_vdefined g f.
Proof. exists (NatSq_vpaste g f Hm); now repeat split. Qed.

Lemma NatSq_hcomp_total (g f : NatSq) (Hm : nsq_left g = nsq_right f) :
  NatSq_hdefined g f.
Proof. exists (NatSq_hpaste g f Hm); now repeat split. Qed.

(*
The identity squares of each direction: a vertical identity has trivial
   vertical edges, a horizontal identity trivial horizontal edges.

--------
每个方向的单位方块：垂直单位具有平凡的垂直边，水平单位具有平凡的水平边。
*)

Lemma NatSq_vid_comm (t : nat) : (t + 0 = 0 + t)%nat.
Proof. lia. Qed.

Definition NatSq_vid (t : nat) : NatSq := mkNatSq t 0 0 t (NatSq_vid_comm t).

Lemma NatSq_hid_comm (c : nat) : (0 + c = c + 0)%nat.
Proof. lia. Qed.

Definition NatSq_hid (c : nat) : NatSq := mkNatSq 0 c c 0 (NatSq_hid_comm c).

Lemma NatSq_vid_ident (t : nat) : NatSq_vident (NatSq_vid t).
Proof.
  split; intros f Hd; nsq_hyps; repeat split; simpl; lia.
Qed.

Lemma NatSq_hid_ident (c : nat) : NatSq_hident (NatSq_hid c).
Proof.
  split; intros f Hd; nsq_hyps; repeat split; simpl; lia.
Qed.

(** *** The two compositions, as [MetaComp] structures / *** 这两种组合，作为 [MetaComp] 结构 *)

Program Definition NatSq_Vert : MetaComp NatSq_Setoid := {|
  mccomp := NatSq_vcomp
|}.
Next Obligation.                        (* respects / 尊重 *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* single-valued / 单值 *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* axiom (i), left to right / 公理 (i)，从左到右 *)
  nsq_hyps.
  assert (Hm : nsq_top g = nsq_bot f) by lia.
  exists (NatSq_vpaste g f Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (i), right to left / 公理 (i)，从右到左 *)
  nsq_hyps.
  assert (Hm : nsq_top k = nsq_bot g) by lia.
  exists (NatSq_vpaste k g Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (ii) / 公理（二） *)
  nsq_hyps.
  apply NatSq_vcomp_total; lia.
Qed.
Next Obligation.                        (* axiom (iii) / 公理（iii） *)
  exists (NatSq_vid (nsq_top g)), (NatSq_vid (nsq_bot g)).
  split; split.
  - apply NatSq_vid_ident.
  - apply NatSq_vid_ident.
  - apply NatSq_vcomp_total; now simpl.
  - apply NatSq_vcomp_total; now simpl.
Qed.

Program Definition NatSq_Horiz : MetaComp NatSq_Setoid := {|
  mccomp := NatSq_hcomp
|}.
Next Obligation.                        (* respects / 尊重 *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* single-valued / 单值 *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* axiom (i), left to right / 公理 (i)，从左到右 *)
  nsq_hyps.
  assert (Hm : nsq_left g = nsq_right f) by lia.
  exists (NatSq_hpaste g f Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (i), right to left / 公理 (i)，从右到左 *)
  nsq_hyps.
  assert (Hm : nsq_left k = nsq_right g) by lia.
  exists (NatSq_hpaste k g Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (ii) / 公理（二） *)
  nsq_hyps.
  apply NatSq_hcomp_total; lia.
Qed.
Next Obligation.                        (* axiom (iii) / 公理（iii） *)
  exists (NatSq_hid (nsq_left g)), (NatSq_hid (nsq_right g)).
  split; split.
  - apply NatSq_hid_ident.
  - apply NatSq_hid_ident.
  - apply NatSq_hcomp_total; now simpl.
  - apply NatSq_hcomp_total; now simpl.
Qed.

(** *** The double category, and the refutation of definition 3 / *** 双重范畴，以及对定义3的反驳 *)

Program Definition NatSq_Double : StrictDoubleCategory := {|
  dcell        := NatSq;
  dcell_setoid := NatSq_Setoid;
  dvert        := NatSq_Vert;
  dhoriz       := NatSq_Horiz
|}.
Next Obligation.                        (* the interchange law / 交换律 *)
  nsq_hyps; repeat split; lia.
Qed.

(* The offending cell: the horizontal identity on the vertical arrow 1. / 有问题的单元格：垂直箭头1上的水平同一性。 *)
Definition NatSq_bad : NatSq := NatSq_hid 1.

Lemma NatSq_bad_hident : dhident NatSq_Double NatSq_bad.
Proof. apply NatSq_hid_ident. Qed.

Lemma NatSq_bad_not_vident : dvident NatSq_Double NatSq_bad → False.
Proof.
  intros [Hsrc _].
  (*
Pasting the cell under itself is defined, its vertical edges being
     composable; were the cell a vertical identity, that pasting would
     return it unchanged, forcing 1 = 1 + 1.

--------
将单元格粘贴到自身之下是已定义的，其垂直边是可组合的；如果该单元格是垂直恒等，那么这种粘贴将返回其自身不变，从而强制 1 = 1 + 1。
*)
  assert (Hd : NatSq_vdefined NatSq_bad NatSq_bad)
    by (apply NatSq_vcomp_total; now simpl).
  destruct (Hsrc NatSq_bad Hd) as [? [? [? [Hl ?]]]].
  simpl in Hl.
  discriminate.
Qed.

(*
Mac Lane §II.5: the double category of commuting squares is not a
   2-category.  There is no way to equip [NatSq_Double] with a
   [StrictTwoCategory] structure, its def-3 condition being refutable.

--------
Mac Lane §II.5：交换方格的双范畴不是一个2-范畴。没有办法为 [NatSq_Double] 配备 [StrictTwoCategory] 结构，其 def-3 条件是可反驳的。
*)
Theorem NatSq_not_a_two_category :
  (∀ u : dcell NatSq_Double, dhident NatSq_Double u → dvident NatSq_Double u)
    → False.
Proof.
  intro H.
  exact (NatSq_bad_not_vident (H NatSq_bad NatSq_bad_hident)).
Qed.

Corollary NatSq_no_StrictTwoCategory
  (S : StrictTwoCategory) (H : s2double S = NatSq_Double) : False.
Proof.
  apply NatSq_not_a_two_category.
  rewrite <- H.
  apply s2ident_coincide.
Qed.

(*
Non-degeneracy: the model is not one in which everything collapses.
   Its two identity families are genuinely different
   ([NatSq_vid_is_not_hid] below proves a vertical identity that is no
   horizontal one; the full classification of the overlap is not
   recorded), and vertical pasting really adds.

--------
非退化性：该模型不是一个一切都崩溃的模型。它的两个同一性族是真正不同的（下面的 [NatSq_vid_is_not_hid] 证明了一个垂直同一性，而没有水平同一性；重叠的完整分类没有记录），并且垂直粘贴确实有增益。
*)

Example NatSq_vid_is_not_hid (t : nat) :
  NatSq_hident (NatSq_vid (S t)) → False.
Proof.
  intros [Hsrc _].
  assert (Hd : NatSq_hdefined (NatSq_vid (S t)) (NatSq_vid (S t)))
    by (apply NatSq_hcomp_total; now simpl).
  destruct (Hsrc _ Hd) as [? [? [? [Ht ?]]]].
  simpl in Ht.
  lia.
Qed.

Example NatSq_vpaste_computes :
  nsq_left (NatSq_vpaste NatSq_bad NatSq_bad eq_refl) = 2%nat := eq_refl.

(**
** The passage from the globular to the arrows-only presentation

    Mac Lane's definition 2 bundles ALL the cells into one collection, so
    composability of two of them becomes an EQUATION between their
    boundaries — between 0-cells, and between 1-cells.  In intensional type
    theory that comparison is an identity type, and the passage therefore
    needs the boundaries to form SETS.  This is exactly the situation
    Theory/Metacategory/General.v meets one dimension down: its [ToArrows]
    takes `obj_uip` as an explicit hypothesis and is the in-tree precedent
    followed here, name for name ([Arr]/[TwoArr], [Arr_eq]/[TwoArr_eq],
    [Arr_comp]/[TwoV]+[TwoH], [arr_crush]/[twoarr_crush]).

    [StrictBase] is the hypothesis pack, and it has three parts.  (i) The
    two UIP clauses, `sb_obj_uip` and `sb_hom_uip`, verbatim [ToArrows]'s
    hypothesis at the two levels a 2-cell's boundary occupies.  (ii) Three
    LEIBNIZ equations making the 1-cell layer a strict category — this is
    not decoration: Mac Lane's arrows-only structure is strict, its
    horizontal identity cells are units on the nose, and the cell equality
    [TwoArr_eq] compares 1-cells by `=`, so `f ∘ id = f` must hold as an
    identity and not merely up to `≈`.  (iii) Three clauses saying the
    class's own boundary identifications ARE the transports along those
    equations — that the chosen [tassoc_cast], [tunitl_cast],
    [tunitr_cast] are the canonical ones, which is what “strict” means at
    the level of 2-cells.

    WHAT THIS EXCLUDES, DISCLOSED.  At `Cat` the pack is not inhabitable
    by any means this library provides, for the reason round one
    established: `(H ◯ G) ◯ F` and `H ◯ (G ◯ F)`
    are not even convertible, and no Leibniz path between them is
    derivable, so `sb_assoc` is
    unavailable there.  That is the same limitation [ToArrows] carries —
    UIP on the objects of `Cat` is not available either — and it is
    intrinsic to the arrows-only style rather than an artifact of this
    encoding.  The pack IS satisfiable: [NatPlus_StrictBase] below
    inhabits it, so nothing here is vacuous.

    WHAT IS ACHIEVED, EXACTLY.  [TwoCategory_to_Strict] is the forward
    passage: a globular [TwoCategory] with a [StrictBase] yields a
    [StrictTwoCategory], Mac Lane's def-3 coincidence included and PROVED
    ([TwoArr_hident_is_vident]) rather than assumed.  The comparison is
    then measured in the shape [ToArrows_Functor] uses: the bundling is
    injective on 2-cells up to `≈` ([TwoArr_at_faithful], with
    [TwoArr_at_respects] the converse), surjective on cells
    ([TwoArr_at_surjective]), and carries [tvcomp] and [thcomp] to the two
    compositions ([TwoV_at], [TwoH_at], with [TwoV_at_unique] and
    [TwoH_at_unique] saying no other cell does).  It is NOT packaged as a
    functor: the source has no category of 2-cells to be functorial from,
    the two structures being related as a family to its bundling.

--------
** 从球状图到仅显示箭头的展示

Mac Lane 的定义 2 将所有单元捆绑到一个集合中，因此两个单元的可组合性变成它们边界之间的一个方程——0-单元之间，以及1-单元之间。在内涵类型理论中，这种比较是一个等同类型，因此这个过程需要边界形成集合。这正是 Theory/Metacategory/General.v 在下一个维度遇到的情况：它的 [ToArrows] 将 `obj_uip` 作为一个显式假设，并且是这里遵循的树内前例，按名称对应（[Arr]/[TwoArr], [Arr_eq]/[TwoArr_eq], [Arr_comp]/[TwoV]+[TwoH], [arr_crush]/[twoarr_crush]）。

[StrictBase] 是假设包，它有三部分。 (i) 两个 UIP 条款，`sb_obj_uip` 和 `sb_hom_uip`，逐字重复了 [ToArrows] 在 2-胞边界的两个层级上的假设。 (ii) 三个 LEIBNIZ 方程使 1-胞层成为严格范畴——这不是装饰：Mac Lane 的仅箭头结构是严格的，它的水平单位胞是完全的单位，并且胞等 [TwoArr_eq] 通过 `=` 比较 1-胞，因此 `f ∘ id = f` 必须作为单位成立，而不仅仅是基于 `≈`。 (iii) 三个条款表明该类自身的边界识别就是沿这些方程的传输——即选定的 [tassoc_cast]、[tunitl_cast]、[tunitr_cast] 是规范的，这就是 2-胞层级上“严格”的含义。

排除的内容，已披露。在 `Cat` 中，该包无法通过本库提供的任何手段被占用，这是第一轮确立的原因：`(H ◯ G) ◯ F` 和 `H ◯ (G ◯ F)` 甚至无法互相转换，并且无法从它们之间推导出任何 Leibniz 路径，因此 `sb_assoc` 在那里不可用。这与 [ToArrows] 的限制相同——`Cat` 对象上的 UIP 也不可用——这是箭头唯一路径风格的内在特性，而不是这种编码的产物。该包是可满足的：下述 [NatPlus_StrictBase] 占据了它，因此这里没有任何内容是空的。

究竟实现了什么。[TwoCategory_to_Strict] 是前向传递：一个球形的 [TwoCategory] 与一个 [StrictBase] 产生一个 [StrictTwoCategory]，其中包含 Mac Lane 的 def-3 重合，并且是经过证明的 ([TwoArr_hident_is_vident]) 而非假设的。然后按 [ToArrows_Functor] 使用的形状进行比较：捆绑在 2-胞上是单射的，直到 `≈` ([TwoArr_at_faithful], 其 [TwoArr_at_respects] 是逆)，在胞上是满射的 ([TwoArr_at_surjective])，并且将 [tvcomp] 和 [thcomp] 映射到两个组合上 ([TwoV_at], [TwoH_at], 其中 [TwoV_at_unique] 和 [TwoH_at_unique] 说明没有其他胞)。它不是以函子方式打包的：源没有 2-胞的范畴可以从中获得函子性，这两种结构作为一个族与其捆绑相关联。
*)

From Coq Require Import Eqdep_dec.

Section ToStrict.

Context {K : TwoCategory}.

(*
Transporting a 1-cell along an equality of its source or target, and a
   2-cell along either of those or along an equality of its own boundary
   1-cells.  Each is [ToArrows]'s [tsrc]/[ttgt] one dimension up.

--------
沿着其源或目标的等式运输一个 1 细胞，以及沿着这些或沿着其自身边界 1 细胞的等式运输一个 2 细胞。每个都是 [ToArrows] 的 [tsrc]/[ttgt] 在一个维度上的提升。
*)

Definition tr1_src {x y : tcat} (f : x ~{tcat}~> y) {x'} (p : x = x')
  : x' ~{tcat}~> y := eq_rect x (fun s => s ~{tcat}~> y) f x' p.

Definition tr1_tgt {x y : tcat} (f : x ~{tcat}~> y) {y'} (q : y = y')
  : x ~{tcat}~> y' := eq_rect y (fun t => x ~{tcat}~> t) f y' q.

Definition tr2_src {x y : tcat} {f g : x ~{tcat}~> y} {x'} (p : x = x')
  (α : tcell f g) : tcell (tr1_src f p) (tr1_src g p).
Proof. destruct p; exact α. Defined.

Definition tr2_tgt {x y : tcat} {f g : x ~{tcat}~> y} {y'} (q : y = y')
  (α : tcell f g) : tcell (tr1_tgt f q) (tr1_tgt g q).
Proof. destruct q; exact α. Defined.

Definition tr2_cast {x y : tcat} {f f' g g' : x ~{tcat}~> y}
  (ed : f = f') (ec : g = g') (α : tcell f g) : tcell f' g'.
Proof. destruct ed, ec; exact α. Defined.

Lemma tr2_cast_sym {x y : tcat} {f f' g g' : x ~{tcat}~> y}
  (ed : f = f') (ec : g = g') (α : tcell f g) :
  tr2_cast (eq_sym ed) (eq_sym ec) (tr2_cast ed ec α) = α.
Proof using Type. destruct ed, ec; reflexivity. Qed.

Lemma tr2_cast_respects {x y : tcat} {f f' g g' : x ~{tcat}~> y}
  (ed : f = f') (ec : g = g') (α β : tcell f g) :
  α ≈ β → tr2_cast ed ec α ≈ tr2_cast ed ec β.
Proof using Type. destruct ed, ec; intro H; exact H. Qed.

(*
A cell of the bundled structure: a 2-cell together with the whole of
   its boundary.  [Arr] of [ToArrows], one dimension up.

--------
捆绑结构的一个单元：一个2-单元连同其整个边界。[Arr]的[ToArrows]，高一维。
*)
Record TwoArr : Type := {
  t0src : tcat;
  t0tgt : tcat;
  t1dom : t0src ~{tcat}~> t0tgt;
  t1cod : t0src ~{tcat}~> t0tgt;
  t2cell : tcell t1dom t1cod
}.

Definition TwoArr_at {x y : tcat} {f g : x ~{tcat}~> y} (α : tcell f g)
  : TwoArr :=
  {| t0src := x; t0tgt := y; t1dom := f; t1cod := g; t2cell := α |}.

Definition TwoArr_eq (a b : TwoArr) : Type :=
  ∃ (p : t0src a = t0src b) (q : t0tgt a = t0tgt b)
    (ed : tr1_tgt (tr1_src (t1dom a) p) q = t1dom b)
    (ec : tr1_tgt (tr1_src (t1cod a) p) q = t1cod b),
    tr2_cast ed ec (tr2_tgt q (tr2_src p (t2cell a))) ≈ t2cell b.

(* The hypothesis pack; see the discussion above. / 假设包；参见上文讨论。 *)
Record StrictBase : Type := {
  sb_obj_uip : ∀ (x y : @tcat K) (p q : x = y), p = q;
  sb_hom_uip : ∀ (a b : @tcat K) (f g : a ~{tcat}~> b) (p q : f = g), p = q;

  sb_id_left : ∀ {a b : @tcat K} (f : a ~{tcat}~> b), @id tcat b ∘ f = f;
  sb_id_right : ∀ {a b : @tcat K} (f : a ~{tcat}~> b), f ∘ @id tcat a = f;
  sb_assoc : ∀ {a b c d : @tcat K} (h : c ~{tcat}~> d) (g : b ~{tcat}~> c)
               (f : a ~{tcat}~> b), h ∘ (g ∘ f) = (h ∘ g) ∘ f;

  sb_assoc_cast : ∀ {a b c d : @tcat K} {f f' : a ~{tcat}~> b}
                    {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d}
                    (s : tcell (h ∘ (g ∘ f)) (h' ∘ (g' ∘ f'))),
    tassoc_cast s ≈ tr2_cast (sb_assoc h g f) (sb_assoc h' g' f') s;

  sb_unitl_cast : ∀ {a b : @tcat K} {f f' : a ~{tcat}~> b}
                    (s : tcell (@id tcat b ∘ f) (@id tcat b ∘ f')),
    tunitl_cast s ≈ tr2_cast (sb_id_left f) (sb_id_left f') s;

  sb_unitr_cast : ∀ {a b : @tcat K} {f f' : a ~{tcat}~> b}
                    (s : tcell (f ∘ @id tcat a) (f' ∘ @id tcat a)),
    tunitr_cast s ≈ tr2_cast (sb_id_right f) (sb_id_right f') s
}.

Context (SB : StrictBase).

Definition TwoV (a b c : TwoArr) : Type :=
  ∃ (p : t0src b = t0src a) (q : t0tgt b = t0tgt a)
    (e : tr1_tgt (tr1_src (t1cod b) p) q = t1dom a),
    TwoArr_eq (TwoArr_at (tvcomp (t2cell a)
              (tr2_cast eq_refl e (tr2_tgt q (tr2_src p (t2cell b)))))) c.

Definition TwoH (a b c : TwoArr) : Type :=
  ∃ (p : t0tgt b = t0src a),
    TwoArr_eq (TwoArr_at (thcomp (t2cell a) (tr2_tgt p (t2cell b)))) c.

Definition TwoV_defined (a b : TwoArr) : Type := ∃ c, TwoV a b c.
Definition TwoH_defined (a b : TwoArr) : Type := ∃ c, TwoH a b c.

Definition TwoV_ident (u : TwoArr) : Type :=
  (∀ f, TwoV_defined f u → TwoV f u f) ∧ (∀ g, TwoV_defined u g → TwoV u g g).

Definition TwoH_ident (u : TwoArr) : Type :=
  (∀ f, TwoH_defined f u → TwoH f u f) ∧ (∀ g, TwoH_defined u g → TwoH u g g).

Ltac twoarr_crush :=
  repeat (match goal with
  | [ a : TwoArr |- _ ] => destruct a
  | [ H : TwoV_defined _ _ |- _ ] => destruct H as [? ?]
  | [ H : TwoH_defined _ _ |- _ ] => destruct H as [? ?]
  | [ H : TwoV _ _ _ |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : TwoH _ _ _ |- _ ] => destruct H as [? ?]
  | [ H : TwoArr_eq _ _ |- _ ] => destruct H as [? [? [? [? ?]]]]
  | [ p : @eq (@obj (@tcat K)) ?x ?x |- _ ] =>
    let H := fresh "Huip" in
    assert (H : p = eq_refl) by apply (sb_obj_uip SB); subst p
  | [ p : @eq (@obj (@tcat K)) _ _ |- _ ] => destruct p
  | [ p : @eq (@hom (@tcat K) ?x ?y) ?f ?f |- _ ] =>
    let H := fresh "Huip" in
    assert (H : p = eq_refl) by apply (sb_hom_uip SB); subst p
  | [ p : @eq (@hom (@tcat K) ?x ?y) _ _ |- _ ] => destruct p
  end; simpl in * ).

Lemma TwoArr_eq_equivalence : Equivalence TwoArr_eq.
Proof.
  constructor.
  - intros a; exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
  - intros a b H; twoarr_crush.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; symmetry; assumption.
  - intros a b c H1 H2; twoarr_crush.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    etransitivity; eassumption.
Qed.

Definition TwoArr_Setoid : Setoid TwoArr :=
  {| equiv := TwoArr_eq; setoid_equiv := TwoArr_eq_equivalence |}.

#[local] Existing Instance TwoArr_eq_equivalence.

Ltac twoarr_finish :=
  repeat match goal with
  | [ H : ?x ≈ ?y |- _ ] => is_var x; rewrite H in *; clear H
  end;
  solve [ assumption | reflexivity
        | (symmetry; assumption)
        | (etransitivity; eassumption)
        | (etransitivity; [ symmetry; eassumption | eassumption ])
        | (etransitivity; [ eassumption | symmetry; eassumption ])
        | (symmetry; etransitivity; eassumption)
        | (symmetry; etransitivity;
           [ symmetry; eassumption | eassumption ]) ].

Lemma TwoV_respects {a a' b b' c c'} :
  TwoArr_eq a a' → TwoArr_eq b b' → TwoArr_eq c c' →
  TwoV a b c → TwoV a' b' c'.
Proof using K.
  intros Ha Hb Hc H; twoarr_crush.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma TwoH_respects {a a' b b' c c'} :
  TwoArr_eq a a' → TwoArr_eq b b' → TwoArr_eq c c' →
  TwoH a b c → TwoH a' b' c'.
Proof using K.
  intros Ha Hb Hc H; twoarr_crush.
  exists eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma TwoV_unique {a b c c'} : TwoV a b c → TwoV a b c' → TwoArr_eq c c'.
Proof using K SB.
  intros H1 H2; twoarr_crush.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma TwoH_unique {a b c c'} : TwoH a b c → TwoH a b c' → TwoArr_eq c c'.
Proof using K SB.
  intros H1 H2; twoarr_crush.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma thassoc_sym {a b c d : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d}
  (γ : tcell h h') (β : tcell g g') (α : tcell f f') :
  tr2_cast (eq_sym (sb_assoc SB h g f)) (eq_sym (sb_assoc SB h' g' f'))
         (thcomp (thcomp γ β) α)
    ≈ thcomp γ (thcomp β α).
Proof using K SB.
  etransitivity.
  - apply tr2_cast_respects.
    etransitivity; [ symmetry; apply thassoc |].
    apply (sb_assoc_cast SB).
  - rewrite tr2_cast_sym; reflexivity.
Qed.

Lemma TwoV_assoc_l {k g f kg kgf} :
  TwoV k g kg → TwoV kg f kgf → ∃ gf, TwoV g f gf ∧ TwoV k gf kgf.
Proof using K.
  intros [p1 [q1 [e1 E1]]] [p2 [q2 [e2 E2]]].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (tvcomp _ _)); split.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    rewrite tvassoc, EE1; exact EE2.
Qed.

Lemma TwoV_assoc_r {k g f gf kgf} :
  TwoV g f gf → TwoV k gf kgf → ∃ kg, TwoV k g kg ∧ TwoV kg f kgf.
Proof using K.
  intros [p1 [q1 [e1 E1]]] [p2 [q2 [e2 E2]]].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (tvcomp _ _)); split.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    rewrite <- tvassoc, EE1; exact EE2.
Qed.

Lemma TwoV_match {k g f kg gf} :
  TwoV k g kg → TwoV g f gf → ∃ kgf, TwoV kg f kgf.
Proof using K.
  intros [p1 [q1 [e1 E1]]] [p2 [q2 [e2 E2]]].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (tvcomp _ _)).
  exists eq_refl, eq_refl, eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma TwoH_assoc_l {k g f kg kgf} :
  TwoH k g kg → TwoH kg f kgf → ∃ gf, TwoH g f gf ∧ TwoH k gf kgf.
Proof using K SB.
  intros [p1 E1] [p2 E2].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (thcomp _ _)); split.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, (sb_assoc SB _ _ _), (sb_assoc SB _ _ _); simpl.
    etransitivity; [ symmetry; apply (sb_assoc_cast SB) |].
    rewrite thassoc, EE1; exact EE2.
Qed.

Lemma TwoH_assoc_r {k g f gf kgf} :
  TwoH g f gf → TwoH k gf kgf → ∃ kg, TwoH k g kg ∧ TwoH kg f kgf.
Proof using K SB.
  intros [p1 E1] [p2 E2].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (thcomp _ _)); split.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, (eq_sym (sb_assoc SB _ _ _)),
           (eq_sym (sb_assoc SB _ _ _)); simpl.
    rewrite thassoc_sym, EE1; exact EE2.
Qed.

Lemma TwoH_match {k g f kg gf} :
  TwoH k g kg → TwoH g f gf → ∃ kgf, TwoH kg f kgf.
Proof using K.
  intros [p1 E1] [p2 E2].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (thcomp _ _)).
  exists eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma thunit_right_cast {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tr2_cast (sb_id_right SB f) (sb_id_right SB f')
         (thcomp α (tid2 (@id tcat a))) ≈ α.
Proof using K SB.
  etransitivity; [ symmetry; apply (sb_unitr_cast SB) |].
  apply thunit_right.
Qed.

Lemma thunit_left_cast {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tr2_cast (sb_id_left SB f) (sb_id_left SB f')
         (thcomp (tid2 (@id tcat b)) α) ≈ α.
Proof using K SB.
  etransitivity; [ symmetry; apply (sb_unitl_cast SB) |].
  apply thunit_left.
Qed.

Lemma TwoV_ident_id {x y : tcat} (f : x ~{tcat}~> y) :
  TwoV_ident (TwoArr_at (tid2 f)).
Proof using K.
  split; intros a Ha.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p [q [e _]]]; simpl in p, q, e.
    exists p, q, e; destruct p, q; simpl in e; destruct e; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    apply tvid_right.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p [q [e _]]]; simpl in p, q, e.
    exists p, q, e; destruct p, q; simpl in e; destruct e; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    apply tvid_left.
Qed.

Lemma TwoV_ident_law (a : TwoArr) :
  ∃ u u', (TwoV_ident u ∧ TwoV_ident u')
        ∧ (TwoV_defined a u ∧ TwoV_defined u' a).
Proof using K SB.
  exists (TwoArr_at (tid2 (t1dom a))), (TwoArr_at (tid2 (t1cod a))).
  split; split.
  - apply TwoV_ident_id.
  - apply TwoV_ident_id.
  - eexists; exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - eexists; exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma TwoH_ident_id (x : tcat) : TwoH_ident (TwoArr_at (tid2 (@id tcat x))).
Proof using K SB.
  split; intros a Ha.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p _]; simpl in p.
    exists p; destruct p; simpl.
    exists eq_refl, eq_refl, (sb_id_right SB af), (sb_id_right SB ag); simpl.
    apply thunit_right_cast.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p _]; simpl in p.
    exists p; destruct p; simpl.
    exists eq_refl, eq_refl, (sb_id_left SB af), (sb_id_left SB ag); simpl.
    apply thunit_left_cast.
Qed.

Lemma TwoH_ident_law (a : TwoArr) :
  ∃ u u', (TwoH_ident u ∧ TwoH_ident u')
        ∧ (TwoH_defined a u ∧ TwoH_defined u' a).
Proof using K SB.
  exists (TwoArr_at (tid2 (@id tcat (t0src a)))),
         (TwoArr_at (tid2 (@id tcat (t0tgt a)))).
  split; split.
  - apply TwoH_ident_id.
  - apply TwoH_ident_id.
  - eexists; exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - eexists; exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma TwoArr_interchange {σ τ σ' τ' pp qq rr ss xx yy} :
  TwoV τ σ pp → TwoV τ' σ' qq → TwoH qq pp xx →
  TwoH τ' τ rr → TwoH σ' σ ss → TwoV rr ss yy → TwoArr_eq xx yy.
Proof using K SB.
  intros [a1 [a2 [a3 A]]] [b1 [b2 [b3 B]]] [c1 C] [d1 D] [e1 E]
         [f1 [f2 [f3 F]]].
  destruct A as [? [? [? [? AA]]]].
  destruct B as [? [? [? [? BB]]]].
  destruct C as [? [? [? [? CC]]]].
  destruct D as [? [? [? [? DD]]]].
  destruct E as [? [? [? [? EE]]]].
  destruct F as [? [? [? [? FF]]]].
  twoarr_crush.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  rewrite <- CC, <- AA, <- BB, tinterchange, DD, EE; exact FF.
Qed.

(*
Every identity for the horizontal composition is one for the vertical
   composition — Mac Lane's def-3 condition, proved for the bundling.  A
   `∘`-identity is forced by uniqueness of composites to agree with the
   canonical one on the identity 1-cell, and THAT is a `·`-identity by
   [TwoV_ident_id], which holds for the identity 2-cell on ANY 1-cell.

--------
水平组合的每个单位都是垂直组合的单位 —— Mac Lane 的 def-3 条件，已对捆绑证明。`∘` 单位由于复合的唯一性被强制与单位 1-胞的典型单位一致，而那个则是 `·` 单位，依据 [TwoV_ident_id]，对于任意 1-胞的单位 2-胞都成立。
*)
Lemma TwoV_ident_respects {u u'} :
  TwoArr_eq u u' → TwoV_ident u → TwoV_ident u'.
Proof using K SB.
  intros Hu [H1 H2]; split.
  - intros f Hf.
    assert (Hf' : TwoV_defined f u).
    { destruct Hf as [c Hc]; exists c.
      exact (TwoV_respects (reflexivity f) (symmetry Hu) (reflexivity c) Hc). }
    exact (TwoV_respects (reflexivity f) Hu (reflexivity f) (H1 f Hf')).
  - intros g Hg.
    assert (Hg' : TwoV_defined u g).
    { destruct Hg as [c Hc]; exists c.
      exact (TwoV_respects (symmetry Hu) (reflexivity g) (reflexivity c) Hc). }
    exact (TwoV_respects Hu (reflexivity g) (reflexivity g) (H2 g Hg')).
Qed.

(*
Mac Lane's definition 3, for the bundled structure: every identity for
   the horizontal composition is an identity for the vertical one.

--------
Mac Lane 对捆绑结构的定义 3：水平复合的每一个恒等式都是垂直复合的恒等式。
*)
Lemma TwoArr_hident_is_vident (u : TwoArr) : TwoH_ident u → TwoV_ident u.
Proof using K SB.
  intros Hu.
  assert (Hd : TwoH_defined (TwoArr_at (tid2 (@id tcat (t0tgt u)))) u).
  { eexists; exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity. }
  pose proof (fst Hu _ Hd) as H1.
  pose proof (snd (TwoH_ident_id (t0tgt u)) u Hd) as H2.
  exact (TwoV_ident_respects (TwoH_unique H1 H2)
           (TwoV_ident_id (@id tcat (t0tgt u)))).
Qed.

(** ** The passage / ** 那段文字 *)

Definition TwoArr_Vert : MetaComp TwoArr_Setoid.
Proof using K SB.
  unshelve refine {| mccomp := TwoV |}.
  - exact (@TwoV_respects).
  - exact (@TwoV_unique).
  - exact (@TwoV_assoc_l).
  - exact (@TwoV_assoc_r).
  - exact (@TwoV_match).
  - exact TwoV_ident_law.
Defined.

Definition TwoArr_Horiz : MetaComp TwoArr_Setoid.
Proof using K SB.
  unshelve refine {| mccomp := TwoH |}.
  - exact (@TwoH_respects).
  - exact (@TwoH_unique).
  - exact (@TwoH_assoc_l).
  - exact (@TwoH_assoc_r).
  - exact (@TwoH_match).
  - exact TwoH_ident_law.
Defined.

Definition TwoArr_Double : StrictDoubleCategory := {|
  dcell        := TwoArr;
  dcell_setoid := TwoArr_Setoid;
  dvert        := TwoArr_Vert;
  dhoriz       := TwoArr_Horiz;
  dinterchange := @TwoArr_interchange
|}.

Definition TwoCategory_to_Strict : StrictTwoCategory := {|
  s2double         := TwoArr_Double;
  s2ident_coincide := TwoArr_hident_is_vident
|}.

(** ** What the passage preserves / ** 这段文字所保留的内容 *)

Lemma TwoArr_at_respects {x y : tcat} {f g : x ~{tcat}~> y} (α β : tcell f g) :
  α ≈ β → TwoArr_eq (TwoArr_at α) (TwoArr_at β).
Proof using Type.
  intro H; exists eq_refl, eq_refl, eq_refl, eq_refl; exact H.
Qed.

Lemma TwoArr_at_faithful {x y : tcat} {f g : x ~{tcat}~> y} (α β : tcell f g) :
  TwoArr_eq (TwoArr_at α) (TwoArr_at β) → α ≈ β.
Proof using K SB. intro H; twoarr_crush; assumption. Qed.

Lemma TwoArr_at_surjective (a : TwoArr) : TwoArr_eq (TwoArr_at (t2cell a)) a.
Proof using Type.
  destruct a; exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
Qed.

Lemma TwoV_at {x y : tcat} {f g h : x ~{tcat}~> y}
  (β : tcell g h) (α : tcell f g) :
  TwoV (TwoArr_at β) (TwoArr_at α) (TwoArr_at (tvcomp β α)).
Proof using Type.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
Qed.

Lemma TwoH_at {x y z : tcat} {f f' : x ~{tcat}~> y} {g g' : y ~{tcat}~> z}
  (β : tcell g g') (α : tcell f f') :
  TwoH (TwoArr_at β) (TwoArr_at α) (TwoArr_at (thcomp β α)).
Proof using Type.
  exists eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
Qed.

Lemma TwoV_at_unique {x y : tcat} {f g h : x ~{tcat}~> y}
  (β : tcell g h) (α : tcell f g) (c : TwoArr) :
  TwoV (TwoArr_at β) (TwoArr_at α) c → TwoArr_eq (TwoArr_at (tvcomp β α)) c.
Proof using K SB. intro H; exact (TwoV_unique (TwoV_at β α) H). Qed.

Lemma TwoH_at_unique {x y z : tcat} {f f' : x ~{tcat}~> y}
  {g g' : y ~{tcat}~> z} (β : tcell g g') (α : tcell f f') (c : TwoArr) :
  TwoH (TwoArr_at β) (TwoArr_at α) c → TwoArr_eq (TwoArr_at (thcomp β α)) c.
Proof using K SB. intro H; exact (TwoH_unique (TwoH_at β α) H). Qed.

End ToStrict.

(**
** The converse passage, and precisely what it still needs

    Extraction in the other direction — reading a globular [TwoCategory]
    off an arrows-only [StrictTwoCategory] — is NOT delivered.  What it
    needs is available in two parts, and it is worth being exact about
    which.  The 0-cells are the `∘`-identities, the 1-cells the
    `·`-identities, and the 2-cells over a prescribed vertical boundary are
    carved out as a sub-setoid; that is precisely the [mobject]/[mmorphism]
    machinery of Theory/Metacategory/General.v's
    [Category_from_Metacategory], which would have to be run at both
    levels and then interlocked.  The genuinely two-dimensional ingredient
    is different: horizontal composition of 2-cells must lie over
    horizontal composition of their 1-cell boundaries.  The lemma below
    proves the two-dimensional GERM of that from the interchange law
    alone, by a single instantiation: the horizontal composite of two
    vertical units acts as a vertical unit ON THE GIVEN horizontal
    composite (one instance — its [mcident]-hood in full is NOT proved
    here).  Mac Lane's definition 2 does not state even this instance.
    The remaining obstruction to the converse is the pair of interlocked
    sub-setoid constructions PLUS upgrading this instance to a unit
    everywhere it composes; ledgered, not hidden.

--------
** 相反的段落，以及它仍然所需要的东西

在相反方向的提取——从仅含箭头的 [StrictTwoCategory] 中读取球体状的 [TwoCategory]——并未提供。它所需的内容分为两个部分，并且准确区分哪一部分很重要。0-胞是 `∘`-同一元，1-胞是 `·`-同一元，而在规定的垂直边界上的 2-胞被划分为一个子等族；这正是 Theory/Metacategory/General.v 中 [mobject]/[mmorphism] 机制的 [Category_from_Metacategory]，必须在两个层次上运行然后再互锁。真正的二维成分是不同的：2-胞的水平组合必须位于其 1-胞边界的水平组合之上。
下面的引理仅通过一次实例化就证明了二维GERM来源于交换律：两个垂直单位的水平复合在给定的水平复合上充当垂直单位（一个实例——其[mcident]-性质的完整性在此未被证明）。Mac Lane 的定义2甚至没有说明这个实例。剩余阻碍逆命题的是一对交错的子子集结构，并且还需要将此实例升级为在所有组合中都是单位；这是记录在案的，并非隐藏的。
*)

Lemma dvert_unit_hcomp (D : StrictDoubleCategory) {u v w x y z t : dcell D} :
  mccomp (dvert D) x u x →      (* u is a vertical unit for x / u 是 x 的垂直单位 *)
  mccomp (dvert D) y v y →      (* v is a vertical unit for y / v 是 y 的垂直单位 *)
  mccomp (dhoriz D) y x z →     (* z is the horizontal composite of y, x / z 是 y 和 x 的水平组合 *)
  mccomp (dhoriz D) v u w →     (* w is the horizontal composite of v, u / w 是 v 和 u 的水平合成 *)
  mccomp (dvert D) z w t →      (* t is the vertical composite of z, w / 它是 z 和 w 的纵向组合 *)
  @equiv _ (dcell_setoid D) z t.
Proof.
  intros H1 H2 H3 H4 H5.
  exact (dinterchange D H1 H2 H3 H3 H4 H5).
Qed.

(**
** The hypothesis pack is satisfiable

    Nothing above is vacuous.  The witness is the CHAOTIC 2-category on the
    delooping of the additive monoid of naturals: one 0-cell, a 1-cell for
    each natural, and exactly one 2-cell between any parallel pair.  Its
    1-cell layer is strict on the nose (`0 + f` reduces to `f`, and the
    other two laws are `Nat.add_0_r` and `Nat.add_assoc`), and its 0-cells
    and 1-cells have decidable equality, so both UIP clauses come from the
    axiom-free [UIP_dec] rather than from an assumption.  The 2-cells are
    degenerate, which is the point: what is being witnessed is that the
    PACK is inhabited, not that the passage is interesting at this model.
    The bundled structure is nonetheless not collapsed —
    [ChaoticTwoCat_cells_separate] exhibits two cells its equality keeps
    apart.

--------
** 假设包是可满足的

上述内容没有空洞。见证者是加性自然数幺半群的解环上的CHAOTIC 2-范畴：一个0-胞，一个对应每个自然数的1-胞，以及任意一对平行胞之间恰好有一个2-胞。它的一胞层严格满足（`0 + f`简化为`f`，另外两个定律是`Nat.add_0_r`和`Nat.add_assoc`），而其0-胞和1-胞具有可判定的等式，因此两条UIP条款来自无公理的[UIP_dec]，而不是假设。2-胞是退化的，这正是重点：所见证的是PACK是有元素的，而不是这个模型下传递是有趣的。捆绑的结构仍然没有塌陷——[ChaoticTwoCat_cells_separate]展示了两个其等式保持分开的胞。
*)

Definition poly_unit_dec (x y : poly_unit) : {x = y} + {x <> y}.
Proof. left; destruct x, y; reflexivity. Defined.

Program Definition chaotic_setoid (A : Type) : Setoid A := {|
  equiv := fun _ _ => True
|}.

#[local] Obligation Tactic :=
  simpl; intros; try apply eq_equivalence; repeat intro; simpl in *; lia.

Program Definition NatPlusCat : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => nat;
  homset  := fun _ _ => {| equiv := @eq nat |};
  id      := fun _ => 0%nat;
  compose := fun _ _ _ f g => (f + g)%nat
|}.

#[local] Obligation Tactic := simpl; intros; repeat intro; exact I.

Program Definition ChaoticTwoCat : TwoCategory := {|
  tcat         := NatPlusCat;
  tcell        := fun _ _ _ _ => poly_unit;
  tcell_setoid := fun _ _ _ _ => chaotic_setoid poly_unit;
  tid2         := fun _ _ _ => ttt;
  tvcomp       := fun _ _ _ _ _ _ _ => ttt;
  thcomp       := fun _ _ _ _ _ _ _ _ _ => ttt;
  tassoc_cast  := fun _ _ _ _ _ _ _ _ _ _ _ => ttt;
  tunitl_cast  := fun _ _ _ _ _ => ttt;
  tunitr_cast  := fun _ _ _ _ _ => ttt
|}.

#[local] Obligation Tactic := simpl; intros; exact I.

Program Definition NatPlus_StrictBase : @StrictBase ChaoticTwoCat := {|
  sb_obj_uip  := UIP_dec poly_unit_dec;
  sb_hom_uip  := fun a b => UIP_dec PeanoNat.Nat.eq_dec;
  sb_id_left  := fun a b f => eq_refl;
  sb_id_right := fun a b f => PeanoNat.Nat.add_0_r f;
  sb_assoc    := fun a b c d h g f => PeanoNat.Nat.add_assoc h g f
|}.

Definition ChaoticTwoCat_Strict : StrictTwoCategory :=
  TwoCategory_to_Strict NatPlus_StrictBase.

Example ChaoticTwoCat_cells_separate :
  @TwoArr_eq ChaoticTwoCat (@TwoArr_at ChaoticTwoCat ttt ttt 0%nat 0%nat ttt)
                    (@TwoArr_at ChaoticTwoCat ttt ttt 1%nat 1%nat ttt) → False.
Proof.
  intros [p [q [ed [ec _]]]].
  rewrite (UIP_dec poly_unit_dec p eq_refl) in ed.
  rewrite (UIP_dec poly_unit_dec q eq_refl) in ed.
  simpl in ed; discriminate.
Qed.
