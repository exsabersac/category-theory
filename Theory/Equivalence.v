Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   An equivalence of categories is a functor F : C ⟶ D together with a
   quasi-inverse G : D ⟶ C whose composites with F are naturally isomorphic
   to the identity functors.  It is the standard weakening of isomorphism of
   categories, and the right notion of "sameness" for categories: it
   preserves and reflects all categorical structure.

   In this library the equivalence [≈] on functors ([Functor_Setoid],
   Theory/Functor.v) is *bundled natural isomorphism*: a family of
   isomorphisms [∀ x, F x ≅ G x] together with the conjugation coherence
   condition on morphisms.  The two comparison cells of an equivalence are
   therefore stated with [≈] directly:

     equivalence_counit : F ◯ quasi_inverse ≈ Id[D]
     equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F

   and, since the hom-setoid of [Cat] (Instance/Cat.v) is exactly
   [Functor_Setoid], an isomorphism in Cat *is* an equivalence of
   categories; the bridge [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence]
   below repacks the data definitionally in both directions (witnessed up
   to [≈] by the two round-trip corollaries).  The bundled [≅[Fun]] forms
   of the two cells are recovered through [Functor_Setoid_Nat_Iso]
   (Instance/Fun.v): see [equivalence_counit_iso]/[equivalence_unit_iso]
   one way and [Nat_Isos_to_Equivalence] the other way.

   [EssentiallySurjective] is stated in the split, choice-carrying house
   style (compare [Full]'s chosen section [prefmap] in Theory/Functor.v and
   the split [surjective] class of Lib/Setoid.v): a chosen preimage object
   [eso_obj d] for every [d : D], together with a witnessing isomorphism
   [eso_iso d].  The classical characterization — full + faithful +
   essentially surjective is the same as being an equivalence — lives in
   Theory/Equivalence/FullFaithful.v; adjoint equivalences are developed in
   Theory/Equivalence/Adjoint.v; preservation, reflection and creation of
   limits along equivalences in Theory/Equivalence/Limit.v; the bundled
   notion [C ≃ D] in Theory/Equivalence/Bundled.v.

   NOTHING in this file is registered for instance resolution: a
   quasi-inverse is a choice, and must never be conjured by typeclass
   search (the [Monoidal_op] convention of Construction/Opposite/
   Monoidal.v).  All constructions below are plain Definitions, passed
   explicitly at use sites.  This also keeps the Cat-level universe
   constraints of the bridge conversions local to the places that actually
   use them.

--------
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
维基百科: https://en.wikipedia.org/wiki/Equivalence_of_categories

范畴的等价是一个函子 F : C ⟶ D 以及一个准逆函子 G : D ⟶ C，使得它们与 F 的复合函子自然同构于恒等函子。这是范畴同构的标准弱化形式，也是范畴的“相同”的正确概念：它保持并反映所有的范畴结构。

在这个库中，函子上的等价 [≈]（[Functor_Setoid]，Theory/Functor.v）是*捆绑的自然同构*：一族同构 [∀ x, F x ≅ G x] 以及在态射上的共轭一致性条件。因此，一个等价的两个比较单元直接使用 [≈] 来表述：

equivalence_counit : F ◯ quasi_inverse ≈ Id[D]
equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F

并且，由于 [Cat] (Instance/Cat.v) 的同态集合恰好是 [Functor_Setoid], Cat 中的同构 *就是* 范畴的等价；下面的桥 [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence] 在两个方向上按定义重新打包了数据（通过两个往返推论在 [≈] 之下得到证明）。两个单元的捆绑 [≅[Fun]] 形式通过 [Functor_Setoid_Nat_Iso] (Instance/Fun.v) 得以恢复：参见 [equivalence_counit_iso]/[equivalence_unit_iso] 一方面以及 [Nat_Isos_to_Equivalence] 另一方面。

[EssentiallySurjective] 被表述在分裂的、带选择的房子风格中（比较 [Full] 的选定部分 [prefmap] 在 Theory/Functor.v 中，以及 Lib/Setoid.v 中的分裂 [surjective] 类）：对于每个 [d : D]，有一个选定的原像对象 [eso_obj d]，以及一个见证同构 [eso_iso d]。经典的表征——完全 + 忠实 + 本质上满射 与成为等价是相同的——位于 Theory/Equivalence/FullFaithful.v；伴随等价在 Theory/Equivalence/Adjoint.v 中展开；沿等价对极限的保持、反射和创建在 Theory/Equivalence/Limit.v 中；捆绑概念 [C ≃ D] 在 Theory/Equivalence/Bundled.v 中。

此文件中的内容没有注册用于实例解析：一个准逆是一个选择，绝不能通过类型类搜索来生成（Construction/Opposite/Monoidal.v 的 [Monoidal_op] 约定）。下面的所有构造都是普通定义，在使用时显式传递。这也将桥接转换的范畴级宇宙约束限制在实际使用它们的地方。
*)

(*
Where equivalence came from, and what it is for

   nLab: https://ncatlab.org/nlab/show/T%C3%B4hoku
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence
   nLab: https://ncatlab.org/nlab/show/skeleton+of+a+category
   SEP:  https://plato.stanford.edu/entries/category-theory/

   The notion is younger than category theory itself.  The founding
   paper (Eilenberg, Mac Lane, "General Theory of Natural Equivalences",
   Transactions of the AMS 58, 1945) treats the category as "essentially
   an auxiliary" concept, the basic notions being functor and natural
   transformation (Marquis, "Category Theory", Stanford Encyclopedia of
   Philosophy).  Equivalence of categories is introduced for the first
   time in Grothendieck's Tôhoku paper (Grothendieck, "Sur quelques
   points d'algèbre homologique", Tôhoku Mathematical Journal (2) 9,
   1957), and in the adjoint form — unit, counit, triangle identities —
   slightly before Kan isolated adjoint functors in general (nLab,
   "Tôhoku").  Within a year, Morita had made equivalence of module
   categories the definition of an equivalence relation on rings
   (Morita, "Duality for modules and its applications to the theory of
   rings with minimum condition", Science Reports of the Tokyo Kyoiku
   Daigaku A 6, 1958): the Morita invariants of a ring are exactly the
   properties that transport along R-Mod ≃ S-Mod.

   Strict isomorphism of categories — composites Leibniz-equal to the
   identity functors — is the sameness Cat supports as a mere
   1-category, and it is too strong: objects are only ever determined up
   to isomorphism, so comparing them by equality separates categories
   that no categorical property can tell apart.  Finite-dimensional
   vector spaces over a field are equivalent, never isomorphic, to the
   small category of natural numbers and matrices (nLab, "equivalence of
   categories").  Equivalence is instead exactly the sameness
   categorical language respects — monos, epis, limits and colimits,
   cartesian closure, being a topos all transport across it — and the
   properties it does not preserve are the ones the principle of
   equivalence brands "evil".  Skeletons measure the cost of
   strictifying anyway: every category is equivalent to each of its
   skeletons, yet the EXISTENCE claim — that every category has one —
   is itself equivalent to the axiom of choice, skeletality is not
   equivalence-invariant, and even a skeletal category has no product
   on the nose (nLab, "skeleton of a category").  The library
   accordingly states every law up to ≈ and never asserts that
   existence: Theory/Skeleton.v carries the [Skeletal] predicate and
   packages "A is a skeleton of C" as DATA — a full subcategory with a
   chosen representative and its uniqueness — so that everything true
   of a GIVEN skeleton is proved there, choice-free
   ([skeleton_inclusion_is_equivalence], [skeletons_are_isomorphic]),
   while no [Skeleton C] is ever produced for an arbitrary C.  That
   skeletality is not equivalence-invariant is itself a theorem
   ([skeletality_is_not_equivalence_invariant] of
   Theory/Skeleton/Separation.v, separating [1] from the indiscrete
   category on [bool]), complemented by [Skeletal_StrictCat_invariant],
   which shows the predicate IS invariant under isomorphism of
   categories.  The concrete instances remain the computing witnesses:
   Instance/FinSet.v, proved skeletal in Instance/FinSet/Skeleton.v,
   where positional objects let the [FinSet_Topos] examples compute by
   eq_refl (Instance/FinSet/Topos.v).

   The choice content of the classical characterization dictates the
   split shape of [EssentiallySurjective].  That every fully faithful,
   essentially surjective functor is an equivalence is logically
   equivalent to the axiom of choice: a quasi-inverse must pick a
   preimage for every object at once (Yorgey, "AC and equivalence of
   categories", 2014).  Makkai repaired this with anafunctors, functors
   defined only up to isomorphism (Makkai, "Avoiding the axiom of choice
   in general category theory", Journal of Pure and Applied Algebra
   108(2), 1996); univalent foundations dissolve it, since for univalent
   categories the characterization needs no choice at all (Ahrens,
   Kapulkin, Shulman, "Univalent categories and the Rezk completion",
   2015).  This file keeps the constructive kernel of that result in
   setoid form, following the HoTT Book (chapter 9, 2013): [eso_obj]
   computes the chosen preimage, [eso_iso] is a data-level witness,
   "there exists a preimage" becomes "here is one", and [FF_ESO_Equivalence]
   in Theory/Equivalence/FullFaithful.v invokes no choice principle.

   Equivalence is also the form in which mathematics states its
   classical dualities: Boolean algebras against Stone spaces (Stone,
   "The Theory of Representations for Boolean Algebras", Transactions of
   the AMS 40, 1936), commutative C*-algebras against compact Hausdorff
   spaces (Gelfand, Naimark, Mat. Sbornik 12, 1943), and, conjecturally,
   the two sides of mirror symmetry as an equivalence of derived
   categories (Kontsevich, "Homological algebra of mirror symmetry",
   1994).  Inside the library the pattern recurs: [Monadic] in
   Monad/Comparison.v is defined as [EquivalenceOfCategories] at the
   Eilenberg–Moore comparison, Cauchy completeness makes the Karoubi
   embedding an equivalence (Construction/Karoubi/Universal.v), the
   fibred/indexed correspondence concludes with [RoundTrip_Equivalence]
   (Construction/Grothendieck/RoundTrip.v), and the algebras of an
   idempotent monad recover its reflective subcategory through
   [Idempotent_EM_Equivalence] (Construction/Reflective/Idempotent.v).
   A theorem of this genre is a completed classification: whatever is
   categorical on one side transports, without loss, to the other.

--------
nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   nLab: https://ncatlab.org/nlab/show/essentially+surjective+functor
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   范畴等价 (equivalence of categories) 是函子 F : C ⟶ D 连同拟逆 G : D ⟶ C，
   其与 F 的复合自然同构于恒等函子。它是范畴同构的标准弱化，也是范畴「相同性」的
   正确概念：保持并反射一切范畴结构。

   本库中函子上的等价 [≈]（[Functor_Setoid]，Theory/Functor.v）是*捆绑的自然同构*：
   一族同构 [∀ x, F x ≅ G x] 加上态射上的共轭连贯条件。等价的两个比较胞因此直接用 [≈]
   陈述：

     equivalence_counit : F ◯ quasi_inverse ≈ Id[D]
     equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F

   又因 [Cat]（Instance/Cat.v）的 hom-setoid 恰是 [Functor_Setoid]，Cat 中的同构*就是*
   范畴等价；下文桥 [Equivalence_to_Cat_Iso]/[Cat_Iso_to_Equivalence] 在两方向定义性
   重打包数据（由两往返推论在 [≈] 下见证）。两胞的捆绑 [≅[Fun]] 形式经
   [Functor_Setoid_Nat_Iso]（Instance/Fun.v）恢复：见一方向的
   [equivalence_counit_iso]/[equivalence_unit_iso] 与另一方向的 [Nat_Isos_to_Equivalence]。

   [EssentiallySurjective] 以分裂、携带选择的风格陈述（比较 Theory/Functor.v 中 [Full]
   的选定截面 [prefmap] 与 Lib/Setoid.v 的分裂 [surjective] 类）：对每个 [d : D] 选定
   原像对象 [eso_obj d]，并带见证同构 [eso_iso d]。经典刻画——满 + 忠实 + 本质满射
   等同于等价——在 Theory/Equivalence/FullFaithful.v；伴随等价在 Theory/Equivalence/Adjoint.v；
   沿等价的极限保持、反射与创造在 Theory/Equivalence/Limit.v；捆绑概念 [C ≃ D] 在
   Theory/Equivalence/Bundled.v。

   本文件*没有任何*内容注册供实例解析：拟逆是选择，绝不可由类型类搜索凭空产生
   （Construction/Opposite/Monoidal.v 的 [Monoidal_op] 约定）。下文所有构造都是普通
   Definition，在使用点显式传入。这也使桥转换的 Cat 层宇宙约束局部于实际使用处。
*)

(*
F is essentially surjective (on objects) when every object of the target
   category is isomorphic to the image of some object of the source.  The
   witness is split: [eso_obj] chooses a preimage object and [eso_iso]
   exhibits the isomorphism.

--------
当目标范畴的每个对象都同构于某个源对象的像时，F 在对象上本质上是满射的。证明是分裂的：[eso_obj] 选择一个前像对象，[eso_iso] 展示该同构。
*)

(*
   【Class EquivalenceOfCategories 语法与字段展开】/ Syntax & field walkthrough
   （口吻对齐 Category/Functor；「范畴相同」的正确弱化）

   1) 这是什么 / What this is
      F 是范畴等价 ⇔ 有拟逆 G，使 F◯G ≈ Id、Id ≈ G◯F（≈ = Functor_Setoid = 自然同构）。
      Equivalence = quasi-inverse up to natural isomorphism (not Leibniz =).
      Haskell 无直接对应；想成「可逆字典，允许同构误差」。
      No close Haskell class; think “invertible dictionary up to iso”.

   2) 重要约定 / Important convention
      本文件**不**把这些 Class 注册进类型类搜索：拟逆是选择，不可自动凭空产生。
      Not registered for instance search: a quasi-inverse is a choice.

   3) EssentiallySurjective（先读这个小 Class）
      - eso_obj : D → C — 选定原像
      - eso_iso d : F (eso_obj d) ≅ d — 见证同构（分裂/计算相关）

   4) EquivalenceOfCategories 字段 / Fields
      - quasi_inverse : D ⟶ C
      - equivalence_counit : F ◯ quasi_inverse ≈ Id[D]
      - equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F
      方向对齐伴随的 counit/unit（见 Theory/Equivalence/Adjoint.v）。

   5) 邻近 / Nearby
      Cat 中同构 ⟺ 范畴等价（桥 Definition，非 Instance）。
      Full+Faithful+ESO 刻画见 Equivalence/FullFaithful.v。

   阅读顺序：Functor 的 ≈ → ESO → quasi_inverse → unit/counit 两胞。
   Reading order: functor ≈ → ESO → quasi_inverse → two cells.
*)

Class EssentiallySurjective {C D : Category} (F : C ⟶ D) := {
  eso_obj : D → C;                     (* chosen preimage object / 已选择的原像对象 *)
  eso_iso (d : D) : F (eso_obj d) ≅ d  (* its image is isomorphic to d / 它的像与 d 同构 *)
}.

(*
F is an equivalence of categories when it has a quasi-inverse.  Both
   cells are natural isomorphisms, because [≈] on functors is
   [Functor_Setoid].  The orientation matches the adjunction every
   equivalence refines to (counit F ◯ G ⟹ Id[D], unit Id[C] ⟹ G ◯ F; see
   Theory/Equivalence/Adjoint.v).

--------
当一个函子 F 有准逆时，它是范畴的一个等价。两个单元都是自然同构，因为函子上的 [≈] 是 [Functor_Setoid]。其方向与每个等价所精炼的伴随相匹配（counit F ◯ G ⟹ Id[D]，unit Id[C] ⟹ G ◯ F；参见 Theory/Equivalence/Adjoint.v）。
*)
Class EquivalenceOfCategories {C D : Category} (F : C ⟶ D) := {
  quasi_inverse : D ⟶ C;
  equivalence_counit : F ◯ quasi_inverse ≈ Id[D];
  equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F
}.

(*
An equivalence of categories IS an isomorphism in Cat: Cat's hom-setoid
   is [Functor_Setoid], so the two inverse laws of the isomorphism are
   exactly the counit and unit cells.  This is kept as a Definition — never
   an Instance — both by the no-inferable-quasi-inverses rule and because
   it mentions [Cat], one universe level above C and D; as a Definition the
   extra constraints stay local to its use sites.

--------
范畴等价是 Cat 中的一个同构：Cat 的同态集合是 [Functor_Setoid]，因此同构的两个逆律正好是余单位和单位元胞。这被保留为一个定义——从不作为实例——既因为没有可推导的准逆规则，也因为它提到了 [Cat]，比 C 和 D 高一个宇宙层级；作为一个定义，额外的约束保持在其使用位置的局部范围内。
*)
Definition Equivalence_to_Cat_Iso {C D : Category} {F : C ⟶ D}
  (E : EquivalenceOfCategories F) : C ≅[Cat] D :=
  @Build_Isomorphism Cat C D F (@quasi_inverse C D F E)
    (@equivalence_counit C D F E)
    (symmetry (@equivalence_unit C D F E)).

(*
... and conversely: a Cat-isomorphism repacks definitionally as an
   equivalence of categories carried by its [to] functor, quasi-inverted by
   its [from] functor.

--------
... 反之亦然：一个 Cat-同构在定义上可以重新打包为由其 [to] 函数承载的范畴等价，由其 [from] 函数准逆转。
*)
Definition Cat_Iso_to_Equivalence {C D : Category} (iso : C ≅[Cat] D) :
  EquivalenceOfCategories (to iso) :=
  @Build_EquivalenceOfCategories C D (to iso) (from iso)
    (iso_to_from iso)
    (symmetry (iso_from_to iso)).

(*
The two bridges compose to the identity, on the nose for the functor
   data (both corollaries hold by [reflexivity] on the components); the
   isomorphism-level statement is up to [≈] of isos in Cat, which compares
   exactly the [to]/[from] components.

--------
这两个桥组合成恒等变换，正好对应于函子 data（两个推论都通过 [reflexivity] 在各个分量上成立）；同构级别的陈述到 Cat 中的 [≈] 同构，它精确地比较了 [to]/[from] 分量。
*)
Corollary Cat_Iso_to_Equivalence_to_Cat_Iso {C D : Category}
  (iso : C ≅[Cat] D) :
  Equivalence_to_Cat_Iso (Cat_Iso_to_Equivalence iso) ≈ iso.
Proof. split; reflexivity. Qed.

Corollary Equivalence_to_Cat_Iso_to_Equivalence {C D : Category}
  {F : C ⟶ D} (E : EquivalenceOfCategories F) :
  @quasi_inverse C D F (Cat_Iso_to_Equivalence (Equivalence_to_Cat_Iso E))
    ≈ @quasi_inverse C D F E.
Proof. reflexivity. Qed.

Section QuasiInverse.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context `{E : @EquivalenceOfCategories C D F}.

(*
The counit and unit as bundled natural isomorphisms in the functor
   category — the [≈] to [≅[Fun]] direction of the round trip provided by
   [Functor_Setoid_Nat_Iso].

--------
的单位在并作为调的调在调平等地位 不用了在调在调在 当我在均须在在在调在调 不会在调 你到底的如何能够在调
的案例
的在落实中将能够
*)
Definition equivalence_counit_iso : F ◯ quasi_inverse ≅[Fun] Id[D] :=
  equiv_iso equivalence_counit.

Definition equivalence_unit_iso : Id[C] ≅[Fun] quasi_inverse ◯ F :=
  equiv_iso equivalence_unit.

(*
Componentwise accessors: the pointwise isomorphism families carried by
   the two cells (their `1 projections).

--------
分量式访问器：由两个单元携带的逐点同构族（它们的 `1 投影）。
*)
Definition equivalence_counit_at (d : D) : F (quasi_inverse d) ≅ d :=
  `1 equivalence_counit d.

Definition equivalence_unit_at (x : C) : x ≅ quasi_inverse (F x) :=
  `1 equivalence_unit x.

(*
Naturality of the unit and counit components, extracted from the
   conjugation coherence carried by [Functor_Setoid]'s ≈ (the helpers
   [fun_equiv_to_fmap]/[fun_equiv_fmap_from] of Theory/Functor.v).

--------
单元和余单元分量的自然性，由 [Functor_Setoid] 的 ≈ 所携带的伴随一致性抽取（即 Theory/Functor.v 中的辅助 [fun_equiv_to_fmap]/[fun_equiv_fmap_from]）。
*)

Lemma equivalence_unit_to_natural {x y : C} (f : x ~> y) :
  to (equivalence_unit_at y) ∘ f
    ≈ fmap[quasi_inverse] (fmap[F] f) ∘ to (equivalence_unit_at x).
Proof. exact (fun_equiv_to_fmap equivalence_unit x y f). Qed.

Lemma equivalence_unit_from_natural {x y : C} (f : x ~> y) :
  f ∘ from (equivalence_unit_at x)
    ≈ from (equivalence_unit_at y) ∘ fmap[quasi_inverse] (fmap[F] f).
Proof. exact (fun_equiv_fmap_from equivalence_unit x y f). Qed.

Lemma equivalence_counit_to_natural {x y : D} (g : x ~> y) :
  to (equivalence_counit_at y) ∘ fmap[F] (fmap[quasi_inverse] g)
    ≈ g ∘ to (equivalence_counit_at x).
Proof. exact (fun_equiv_to_fmap equivalence_counit x y g). Qed.

Lemma equivalence_counit_from_natural {x y : D} (g : x ~> y) :
  fmap[F] (fmap[quasi_inverse] g) ∘ from (equivalence_counit_at x)
    ≈ from (equivalence_counit_at y) ∘ g.
Proof. exact (fun_equiv_fmap_from equivalence_counit x y g). Qed.

(*
The conjugation form of unit naturality: the composite functor
   [quasi_inverse ◯ F] acts on morphisms by conjugation with the unit
   components.

--------
Teresa. 单位自然从一开始就是指混合的ử 听我说
从一开始就,公正地,,,
协调一致地说说,建立起并作为,在 我们去撰,”.鳕,說到筹划蕴,說 我们得的說撰說,說說,說說在委员会,說說說,說說授课是否能的一个重要组成部分,說說說說,說說,說說說說 怎麼了說直接向荫了, 42. 我们会說,說說說增强其說,說說的出版物, 说真的說說ỡ說,說說說 說說說 蓓說,,载明 就是說說, silk說 說
*)
Lemma equivalence_unit_conjugate {x y : C} (f : x ~> y) :
  fmap[quasi_inverse] (fmap[F] f)
    ≈ to (equivalence_unit_at y) ∘ f ∘ from (equivalence_unit_at x).
Proof.
  rewrite equivalence_unit_to_natural.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(*
Symmetry: the quasi-inverse is itself an equivalence of categories,
   quasi-inverted by F.  The two cells swap roles, with their orientations
   flipped by symmetry of [≈].

--------
对称性：拟逆本身是范畴的等价，由 F 拟逆。两个单元交换角色，其方向由 [≈] 的对称性翻转。
*)
Definition EquivalenceOfCategories_sym :
  EquivalenceOfCategories quasi_inverse :=
  @Build_EquivalenceOfCategories D C quasi_inverse F
    (symmetry equivalence_unit)
    (symmetry equivalence_counit).

End QuasiInverse.

(*
Packaging from bundled natural isomorphisms: a functor equipped with
   natural isomorphisms F ◯ G ≅ Id[D] and Id[C] ≅ G ◯ F in the functor
   category is an equivalence — the [≅[Fun]] to [≈] direction of the
   [Functor_Setoid_Nat_Iso] round trip.

--------
从捆绑的自然同构中打包：一个函子配备了自然同构 F ◯ G ≅ Id[D] 和 Id[C] ≅ G ◯ F，在函子范畴中是一个等价——[≅[Fun] 到 [≈] 方向的 [Functor_Setoid_Nat_Iso] 往返。
*)
Definition Nat_Isos_to_Equivalence {C D : Category} (F : C ⟶ D) (G : D ⟶ C)
  (counit_iso : F ◯ G ≅[Fun] Id[D]) (unit_iso : Id[C] ≅[Fun] G ◯ F) :
  EquivalenceOfCategories F :=
  @Build_EquivalenceOfCategories C D F G
    (Category.Instance.Fun.iso_equiv counit_iso)
    (Category.Instance.Fun.iso_equiv unit_iso).

(* The identity functor is an equivalence, quasi-inverse itself. / 恒等函子是一个等价，自身就是拟逆函子。 *)
Definition EquivalenceOfCategories_Id {C : Category} :
  EquivalenceOfCategories Id[C] :=
  @Build_EquivalenceOfCategories C C Id[C] Id[C]
    (fun_equiv_id_left Id[C])
    (symmetry (fun_equiv_id_left Id[C])).

(*
Essential surjectivity is closed under composition.

   Book: Riehl, "Category Theory in Context", Dover 2016, §1.5,
         Exercise 1.5.vi(i), printed p. 38

   This is the third clause of that exercise, alongside the closure of
   fullness and of faithfulness ([Full_Compose] and [Faithful_Compose],
   Theory/Functor.v).  Given e : E, pull it back twice — first along F, then
   along G — and paste the two witnessing isomorphisms: F carries G's
   isomorphism forward (functors preserve isomorphisms, [fobj_iso]) to land at
   F applied to F's own chosen preimage of e, from where F's own isomorphism
   finishes the trip to e.  The
   choices compose because [EssentiallySurjective] is the split form, carrying
   a chosen preimage rather than a bare existence statement.

   Stated at the end of the file rather than beside the class so that the two
   class definitions above stay adjacent.

--------
本质满射在复合下是封闭的。

书籍：Riehl，《Category Theory in Context》，Dover 2016，第1.5节，
练习 1.5.vi(i)，印刷页 38

这是该练习的第三条款，与满性和信性闭合（[Full_Compose] 和 [Faithful_Compose]，Theory/Functor.v）并列。给定 e : E，先沿 F 拉回一次，再沿 G 拉回一次，然后拼接两个见证同构：F 将 G 的同构向前传递（函子保持同构，[fobj_iso]）以到达 F 应用于 F 自己选定的 e 的前像，从 F 自己的同构完成到 e 的旅程。

这些选择可以组合，因为 [EssentiallySurjective] 是分裂形式，携带一个选定的前像，而不是仅仅存在性声明。

在文件末尾陈述，而不是放在类旁边，以便上面的两个类定义保持相邻。
*)

#[export] Program Instance EssentiallySurjective_Compose
  {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  `{@EssentiallySurjective D E F} `{@EssentiallySurjective C D G} :
  EssentiallySurjective (F ◯ G) := {|
  eso_obj := fun e => eso_obj (F:=G) (eso_obj (F:=F) e)
|}.
Next Obligation.
  exact (iso_compose (eso_iso (F:=F) d)
           (fobj_iso F _ _ (eso_iso (F:=G) (eso_obj (F:=F) d)))).
Defined.
