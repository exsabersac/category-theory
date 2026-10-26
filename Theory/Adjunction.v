Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction F ⊣ U between F : D ⟶ C (the left adjoint) and U : C ⟶ D
   (the right adjoint) is given here in hom-set form: a family of isomorphisms
   adj {x y} : (F x ~{C}~> y) ≊ (x ~{D}~> U y) in the category of setoids,
   natural in both arguments. Writing ⌊f⌋ := to adj f and ⌈f⌉ := from adj f
   for the two transposes, naturality is recorded by [to_adj_nat_l],
   [to_adj_nat_r] (and the inverse-direction [from_adj_nat_l],
   [from_adj_nat_r]). The unit η := ⌊id⌋ : x ~> U (F x) and counit
   ε := ⌈id⌉ : F (U x) ~> x are the transposes of the identities, and the
   triangle (zig-zag) identities ε ∘ fmap[F] η ≈ id[F x] (counit_fmap_unit)
   and fmap[U] ε ∘ η ≈ id[U x] (fmap_counit_unit) hold as derived corollaries.

--------
nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   F : D ⟶ C（左伴随）与 U : C ⟶ D（右伴随）之间的伴随 F ⊣ U 此处以 hom 集形式给出：
   setoid 范畴中一族同构 adj {x y} : (F x ~{C}~> y) ≊ (x ~{D}~> U y)，对两变元自然。
   写 ⌊f⌋ := to adj f、⌈f⌉ := from adj f 为两个转置，自然性由 [to_adj_nat_l]、
   [to_adj_nat_r]（及反向 [from_adj_nat_l]、[from_adj_nat_r]）记录。单位
   η := ⌊id⌋ : x ~> U (F x) 与余单位 ε := ⌈id⌉ : F (U x) ~> x 是恒等的转置，
   三角（之字形）恒等式 ε ∘ fmap[F] η ≈ id[F x]（counit_fmap_unit）与
   fmap[U] ε ∘ η ≈ id[U x]（fmap_counit_unit）作为派生推论成立。
*)

(*
Origins, ubiquity, and the uses of adjunction

   nLab:  https://ncatlab.org/nlab/show/adjoint+functor
   Paper: Kan, “Adjoint functors”, Transactions of the American
          Mathematical Society 87(2), 1958
   Paper: Lawvere, “Adjointness in Foundations”, Dialectica 23(3/4), 1969;
          reprinted as TAC Reprints 16, 2006

   Adjoint functors were introduced by Daniel Kan — a homotopy theorist and
   doctoral student of Eilenberg — in the 1958 paper cited above.  The
   concept was suggested by the needs of homological algebra, where natural
   bijections of the shape Hom(F x, y) ≅ Hom(x, U y) had long been in
   working use, the paradigm case being the tensor-hom adjunction
   − ⊗ A ⊣ Hom(A, −) on abelian groups.  The name records an analogy with
   adjoint linear operators on a Hilbert space, ⟨L x, y⟩ = ⟨x, R y⟩; the
   nLab describes the categorical notion as a kind of categorification of
   that older one.  Mac Lane states the standard assessment in the preface
   of Categories for the Working Mathematician (Springer, 1971): “Adjoint
   functors arise everywhere”, and the middle of that book presents
   universal constructions, limits, and free objects as so many faces of
   adjunction.

   Three presentations of the concept are equivalent, and the library
   formalizes each.  This file takes Kan's hom-set form as primitive: the
   natural family of setoid isomorphisms [adj].  The unit/counit form —
   η and ε subject to the two triangle identities, which appear here as the
   derived corollaries [counit_fmap_unit] and [fmap_counit_unit] — is the
   class [Adjunction_Transform] of Adjunction/Natural/Transformation.v,
   with the round trip between the two forms in
   Adjunction/Natural/Transformation/Universal.v.  The universal-arrow form
   is Theory/Universal/Arrow.v, whose [AdjunctionFromUniversalArrows]
   assembles an adjunction from a pointwise family of universal solutions
   and is the engine behind the adjoint functor theorems of
   Adjunction/GAFT.v.  An adjunction is weaker than an isomorphism or an
   equivalence of categories, yet strong enough to transport structure:
   adjoints are unique up to natural isomorphism ([right_adjoint_iso] and
   [left_adjoint_iso] below), right adjoints preserve limits and left
   adjoints colimits (Adjunction/Continuity.v, anticipated by the note
   ending this file), and every adjunction induces a monad.  The last
   observation is Huber's (“Homotopy theory in general categories”,
   Mathematische Annalen 144, 1961), realized here as [Adjunction_Monad] in
   Monad/Adjunction.v; its converse — every monad so arises — was proved
   twice in 1965, by Kleisli (“Every standard construction is induced by a
   pair of adjoint functors”, Proceedings of the AMS 16(3), 1965) with the
   initial resolution and by Eilenberg and Moore (“Adjoint functors and
   triples”, 1965) with the terminal one, both in-tree as
   Monad/Kleisli/Adjunction.v and Monad/Eilenberg/Moore/Adjunction.v.

   Lawvere's “Adjointness in Foundations” argues that adjointness, first
   isolated and named in category theory, also pervades logic: cartesian
   closed structure is entirely given by adjunctions — currying is
   − × a ⊣ (−)^a — and the quantifiers form the adjoint triple
   ∃ ⊣ substitution ⊣ ∀ over the fibres of a hyperdoctrine, a triple that
   reappears as dependent sum and product in type theory and as base
   change in geometry.  Between posets, an adjunction is exactly a Galois
   connection -- proved both ways at Instance/Proset/Galois.v, where the
   coherence fields of this class are also shown to be vacuous over a thin
   target while the hom-set iso is not ([succ_not_self_adjoint]) -- whose
   antitone variant recovers classical Galois theory;
   on this special case rests abstract interpretation (Cousot and Cousot,
   “Abstract interpretation: a unified lattice model for static analysis
   of programs by construction or approximation of fixpoints”, POPL 1977),
   where a connection α ⊣ γ between concrete and abstract domains —
   c ⊑ γ(a) ⟺ α(c) ≼ a — is the soundness discipline of static
   analyzers, and such connections compose, so stages of approximation
   stack.

   For the functional programmer (Milewski, “Adjunctions”, 2016), the
   transposes ⌊-⌋ and ⌈-⌉ are the leftAdjunct and rightAdjunct of
   Haskell's Adjunction class, while [unit] and [counit] specialize to
   return and extract.  The product type is right adjoint to the diagonal
   functor — concretely [Diagonal_Product_Adjunction] in
   Adjunction/Diagonal/Product.v — and the function type arises from
   − × a ⊣ (−)^a with eval as counit.  The free/forgetful reading of the
   next comment block, witnessed in-tree by [FreeForgetfulAdjunction] in
   Construction/Free/Quiver.v, is the historically central family of
   examples, though not the whole story: limits and Kan extensions are
   themselves adjoints, to the diagonal and restriction functors.

--------
伴随的起源、无处不在与用途

   nLab:  https://ncatlab.org/nlab/show/adjoint+functor
   Paper: Kan, “Adjoint functors”, Transactions of the American
          Mathematical Society 87(2), 1958
   Paper: Lawvere, “Adjointness in Foundations”, Dialectica 23(3/4), 1969;
          reprinted as TAC Reprints 16, 2006

   伴随函子由 Daniel Kan——同伦理论家、Eilenberg 的博士生——在上述 1958 论文中引入。
   概念由同调代数的需要所提示，彼处形如 Hom(F x, y) ≅ Hom(x, U y) 的自然双射早已常用，
   典范情形是阿贝尔群上的张量-hom 伴随 − ⊗ A ⊣ Hom(A, −)。名称记录与 Hilbert 空间上
   伴随线性算子 ⟨L x, y⟩ = ⟨x, R y⟩ 的类比；nLab 把范畴概念描述为对那一更老概念的
   某种范畴化。Mac Lane 在《Categories for the Working Mathematician》（Springer, 1971）
   序言中给出标准评价：「伴随函子无处不在」，该书中部把普遍构造、极限与自由对象
   呈现为伴随的诸多面孔。

   概念的三种呈现等价，本库均形式化。本文件以 Kan 的 hom 集形式为原始：自然的
   setoid 同构族 [adj]。单位/余单位形式——η 与 ε 服从两条三角恒等式，此处作为派生推论
   [counit_fmap_unit] 与 [fmap_counit_unit] 出现——是 Adjunction/Natural/Transformation.v
   的类 [Adjunction_Transform]，两种形式的往返在
   Adjunction/Natural/Transformation/Universal.v。普遍箭头形式是 Theory/Universal/Arrow.v，
   其 [AdjunctionFromUniversalArrows] 从逐点普遍解族组装伴随，是 Adjunction/GAFT.v
   伴随函子定理背后的引擎。伴随弱于范畴同构或等价，但足以运送结构：伴随在自然同构
   下唯一（下文 [right_adjoint_iso]、[left_adjoint_iso]），右伴随保持极限、左伴随保持
   余极限（Adjunction/Continuity.v，本文件末注记已预示），且每个伴随诱导单子。后者是
   Huber 的观察（“Homotopy theory in general categories”, Mathematische Annalen 144, 1961），
   此处实现为 Monad/Adjunction.v 的 [Adjunction_Monad]；其逆——每个单子都如此产生——
   在 1965 年被证明两次：Kleisli（“Every standard construction is induced by a pair of
   adjoint functors”, Proceedings of the AMS 16(3), 1965）给出初始分解，Eilenberg 与
   Moore（“Adjoint functors and triples”, 1965）给出终结分解，树内分别为
   Monad/Kleisli/Adjunction.v 与 Monad/Eilenberg/Moore/Adjunction.v。

   Lawvere 的 “Adjointness in Foundations” 主张：首先在范畴论中分离并命名的伴随性
   也遍及逻辑——笛卡尔闭结构完全由伴随给出，curry 是 − × a ⊣ (−)^a——量词形成伴随三元组
   ∃ ⊣ 替换 ⊣ ∀（在 hyperdoctrine 纤维上），该三元组在类型论中再现为依赖和与积、在几何中
   为基变换。在偏序之间，伴随恰是 Galois 联络——在 Instance/Proset/Galois.v 双向证明，
   且证明本类的连贯性字段在薄目标上空虚而 hom 集同构则否（[succ_not_self_adjoint]）——
   其反变变体恢复经典 Galois 理论；抽象解释（Cousot and Cousot, POPL 1977）建立在此特殊情形上，
   具体域与抽象域之间的联络 α ⊣ γ——c ⊑ γ(a) ⟺ α(c) ≼ a——是静态分析器的可靠性纪律，
   且此类联络可复合，故近似阶段可堆叠。

   对函数式程序员（Milewski, “Adjunctions”, 2016），转置 ⌊-⌋ 与 ⌈-⌉ 是 Haskell Adjunction
   类的 leftAdjunct 与 rightAdjunct，而 [unit] 与 [counit] 特殊化为 return 与 extract。
   积类型是对角函子的右伴随——具体见 Adjunction/Diagonal/Product.v 的
   [Diagonal_Product_Adjunction]——函数类型来自 − × a ⊣ (−)^a，以 eval 为余单位。
   下一块注释的自由/遗忘读法，树内由 Construction/Free/Quiver.v 的 [FreeForgetfulAdjunction]
   见证，是历史上中心的例子族，但并非全部：极限与 Kan 扩张本身也是伴随（分别对对角与限制函子）。
*)

(*
Adjunctions relate two functors that map between the same two categories
  (though in opposite directions), in a manner that is weaker than isomorphism
  or equivalence, but still quite informative. In general, one functor is
  forgetful, and maps constructions from a more expressive domain into one
  that captures only the essence of that structure; while the other is free,
  and maps essential constructions into the fuller setting.

  As an example: the category of ASTs may be mapped forgetfully to the
  category of interpretated objects, which themselves map freely to some
  “canonical” representation of each such object. So, “3”, “1 + 2”, and “2 +
  1” all mean 3, while 3 is canonically represented by the constant “3”. The
  forgetful functor is the evaluator, and the free functor a parser, giving
  rise to the following isomorphism (in the category of Sets, whose objects
  may be hom-sets):

      AST x ~{category of syntax or ASTs}~> y
        ≅ x ~{category of semantics or denotations}~> Denote y

--------
伴随涉及两个函子，它们在相同的两个范畴之间映射（尽管方向相反），这种关系比同构或等价要弱，但仍然非常有信息量。通常，一个函子是遗忘的，将来自更具表达力的领域的构造映射到仅捕捉该结构本质的领域；而另一个函子是自由的，将本质构造映射到更完整的环境中。

例如：AST 的范畴可以通过遗忘映射到解释对象的范畴，而这些解释对象本身又可以自由地映射到每个此类对象的某种“规范”表示。因此，“3”、“1 + 2”和“2 + 1”都表示 3，而 3 的规范表示是常量“3”。遗忘函子是求值器，自由函子是解析器，从而产生以下同构（在集合的范畴中，其对象可以是同态集）：

AST x ~{语法或抽象语法树的范畴}~> y ≅ x ~{语义或表示的范畴}~> 表示 y
*)

Section Adjunction.

Universes o1 h1 p1 o2 h2 p2.
Context {C : Category@{o1 h1 p1}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Reserved Notation "⌊ f ⌋".
Reserved Notation "⌈ f ⌉".

(* o3 p3 are universes larger than either C or D. / o3 p3 是比 C 或 D 更大的宇宙。 *)

(*
   【Class Adjunction 语法与字段展开】/ Syntax & field walkthrough
   （口吻对齐 Category/Functor；本文件取 Kan 的 hom-集形式）

   1) 这是什么 / What this is
      F ⊣ U：自然的 Hom 同构 (F x ~> y) ≊ (x ~> U y)，比范畴同构/等价更弱。
      Hom-set adjunction: a natural iso of homs, weaker than equivalence.
      Haskell 对照（一次）：Adjunction 的 leftAdjunct/rightAdjunct ≈ ⌊-⌋/⌈-⌉；
      unit/counit 特殊化常作 return/extract（单位/余单位在本 Class 外导出）。
      Haskell analogy (once): leftAdjunct/rightAdjunct ≈ ⌊-⌋/⌈-⌉.

   2) 头与宇宙 / Header & universes
      Context：F : D ⟶ C（左），U : C ⟶ D（右）。
      Class Adjunction@{o3 p3 so sh sp} — 额外宇宙给 Sets 里的 Hom-同构。
      Extra universes host the Sets-level isomorphism of hom-setoids.

   3) 数据字段 / Data
      - adj {x y} : Isomorphism (在 Sets) 之间的两个 Hom-setoid
        where ⌊f⌋ := to adj f，⌈f⌉ := from adj f（转置）。
        / the two transposes via where-notation.

   4) 自然性定律（均对 ≈）/ Naturality laws (up to ≈)
      to_adj_nat_l / to_adj_nat_r：⌊-⌋ 对两变元自然；
      from_adj_nat_l / from_adj_nat_r：⌈-⌉ 的对偶形（可推但留下便于对偶）。
      这些是证明义务；单位 η=⌊id⌋、余单位 ε=⌈id⌉ 与三角恒等式见后文推论。

   5) 邻近 / Nearby
      单位/余单位形见 Adjunction/Natural/Transformation.v；
      普遍箭头形见 Theory/Universal/Arrow.v。

   阅读顺序：谁是 F/U → adj 同构 → ⌊⌋/⌈⌉ → 四条 nat → 后文 unit/counit。
   Reading order: F/U roles → adj → transposes → four nat laws → unit/counit.
*)

Class Adjunction@{o3 p3 so sh sp} := {
  (* adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y / adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y *)
  adj {x y} :
    @Isomorphism@{so sh p3} Sets@{o3 so}
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |}
    where "⌊ f ⌋" := (to   adj f)
      and "⌈ f ⌉" := (from adj f);

  (*
Naturality of the iso in both arguments, stated for the forward transpose
     ⌊-⌋ = to adj (naturality in x, via F) and ...

--------
在两个论域中同态性的 iso，自前向转置中声明 ⌊-⌋ = 转为 adj（在 x 中的同态性，通过 F）以及 ...
*)
  to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) :
    ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  (* ... naturality in y, via U. / ... 在 y 中的自然性，通过 U。 *)
  to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) :
    ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;

  (*
The dual (_sym) statements for the inverse transpose ⌈-⌉ = from adj;
     derivable from the above, but kept as fields so that opposite-side proofs
     are available by reflexivity-of-duality without re-deriving them.

--------
逆转置 ⌈-⌉ 的对偶 (_sym) 语句来自伴随；可从上述推导，但保持为字段，以便通过对偶的自反性可以获得对侧证明，而无需重新推导它们。
*)
  from_adj_nat_l {x y z} (f : y ~> U z) (g : x ~> y) :
    ⌈f ∘ g⌉ ≈ ⌈f⌉ ∘ fmap[F] g;
  from_adj_nat_r {x y z} (f : y ~> z) (g : x ~> U y) :
    ⌈fmap[U] f ∘ g⌉ ≈ f ∘ ⌈g⌉
}.

Definition Build_Adjunction'
  (adj : forall x y,
    @Isomorphism Sets
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |})
  (to_adj_nat_l : forall x y z (f : F y ~> z) (g : x ~> y),
      (to (adj _ _)  (f ∘ fmap[F] g) ≈ (to (adj _ _) f) ∘ g))
  (to_adj_nat_r : forall x y z (f : y ~> z) (g : F x ~> y),
      (to (adj _ _) (f ∘ g) ≈ fmap[U] f ∘ (to (adj _ _) g)))
  : Adjunction.
Proof.
  unshelve eapply Build_Adjunction.
  + apply to_adj_nat_l.
  + apply to_adj_nat_r.
  + intros x y z f g.
    set (f' := from (adj y z) f).
    apply ((snd (@injectivity_is_monic _ _ (adj x z))) _).
    change (to (adj x z) (from (adj x z) _)) with
      (((adj x z) ∘ (from (adj x z))) (f ∘ g)).
    rewrite ((iso_to_from (adj x z)) (f ∘ g)); simpl;
    rewrite to_adj_nat_l.
    refine (compose_respects _ _ _ g _ (Equivalence_Reflexive _)).
    unfold f'; symmetry.
    exact ((iso_to_from (adj y z)) f).
  + intros x y z f g.
    set (g' :=  from (adj x y) g).
    apply ((snd (@injectivity_is_monic _ _ (adj x z))) _).
    rewrite (iso_to_from (adj x z) (fmap[U] f ∘ g)); simpl.
    rewrite to_adj_nat_r.
    apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _)).
    unfold g'; symmetry;
      apply (iso_to_from (adj x y) g).
Defined.

Context `{@Adjunction}.

Notation "⌊ f ⌋" := (to adj f).
Notation "⌈ f ⌉" := (from adj f).

Corollary adj_univ `(f : F x ~> y) (g : x ~> U y) :
  f ≈ ⌈g⌉ ↔ ⌊f⌋ ≈ g.
Proof.
  split; intros.
  - rewrite X.
    sapply (@iso_to_from Sets _ _ (@adj _ x y)).
  - rewrite <- X.
    symmetry.
    sapply (@iso_from_to Sets _ _ (@adj _ x y)).
Qed.

Corollary to_adj_comp_law {x y} (f : F x ~> y) :
  ⌈⌊f⌋⌉ ≈ f.
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x y) f). Qed.

Corollary from_adj_comp_law {x y} (f : x ~> U y) :
  ⌊⌈f⌉⌋ ≈ f.
Proof. sapply (@iso_to_from Sets _ _ (@adj _ x y) f). Qed.

Definition unit   {x : D} : x ~> U (F x) := ⌊id⌋.
Definition counit {x : C} : F (U x) ~> x := ⌈id⌉.

Notation "'η'" := unit.
Notation "'ε'" := counit.

Corollary from_adj_unit {x} :
  ⌈η⌉ ≈ id[F x].
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x (F x))). Qed.

Corollary to_adj_counit {x} :
  ⌊ε⌋ ≈ id[U x].
Proof. sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)). Qed.

Corollary counit_comp {x y} (f : F x ~> y) :
  ε ∘ fmap[F] (fmap[U] f) ≈ f ∘ ε.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Corollary unit_comp {x y} (f : x ~> U y) :
  fmap[U] (fmap[F] f) ∘ η ≈ η ∘ f.
Proof.
  unfold unit.
  rewrite <- to_adj_nat_l.
  rewrite <- to_adj_nat_r.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Corollary adj_univ_impl {x y} (f : F x ~> y) (g : x ~> U y) :
  f ≈ ε ∘ fmap[F] g ↔ ⌊f⌋ ≈ g.
Proof.
  unfold counit.
  split; intros.
  - rewrite X; clear X.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    apply from_adj_comp_law.
  - rewrite <- X; clear X.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    symmetry.
    apply to_adj_comp_law.
Qed.

Corollary to_adj_unit {x y} (f : F x ~> y) :
  ⌊f⌋ ≈ fmap[U] f ∘ η.
Proof.
  rewrite <- (id_right f).
  rewrite to_adj_nat_r.
  rewrite fmap_comp; cat.
Qed.

Corollary from_adj_counit {x y} (f : x ~> U y) :
  ⌈f⌉ ≈ ε ∘ fmap[F] f.
Proof.
  rewrite <- (id_left f).
  rewrite from_adj_nat_l.
  rewrite fmap_comp; cat.
Qed.

Corollary counit_fmap_unit  {x} :
  ε ∘ fmap[F] η ≈ id[F x].
Proof.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  sapply (@iso_from_to Sets _ _ (@adj _ x (F x))).
Qed.

Corollary fmap_counit_unit  {x} :
  fmap[U] ε ∘ η ≈ id[U x].
Proof.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)).
Qed.

Corollary fmap_from_adj_unit {x y} (f : x ~{D}~> y) : fmap[F] f ≈ ⌈η ∘ f⌉.
Proof.
  unfold unit.
  rewrite from_adj_nat_l.
  rewrite to_adj_comp_law; cat.
Qed.

Corollary fmap_to_adj_counit {x y} (f : x ~{C}~> y) : fmap[U] f ≈ ⌊f ∘ ε⌋.
Proof.
  unfold counit.
  rewrite to_adj_nat_r.
  rewrite from_adj_comp_law; cat.
Qed.

(* If F is a faithful functor, and f is monic, then adj f is monic. / 如果 F 是忠实函子，并且 f 是单态的，那么 adj f 也是单态的。 *)
Theorem adj_monic  {x y} (f : F x ~> y) c (g h : c ~> x) :
  Faithful F → Monic f ->
    ⌊f⌋ ∘ g ≈ ⌊f⌋ ∘ h → g ≈ h.
Proof.
  intros.
  rewrite <- !to_adj_nat_l in X1.
  assert
    (Proper
       (@equiv _ unit_setoid ==> equiv)
       (λ _ : unit_setoid_object, f ∘ fmap[F] g)) as XA by proper.
  assert
    (Proper
       (@equiv _ unit_setoid ==> equiv)
       (λ _ : unit_setoid_object, f ∘ fmap[F] h)) as XB by proper.
  pose proof
       (monic (Monic:=@iso_to_monic Sets
                                    {| is_setoid := homset (fobj[F] c) y |}
                                    {| is_setoid := homset c (fobj[U] y) |}
                                    (@adj H c y))
              unit_setoid_object
              {| morphism  := λ _ : unit_setoid_object, f ∘ fmap[F] g |}
              {| morphism  := λ _ : unit_setoid_object, f ∘ fmap[F] h |}) as X2.
  simpl in X2.
  now apply X, X0, X2.
Qed.

Corollary to_adj_respects {x y} (f g : F x ~{C}~> y) :
  f ≈ g → ⌊f⌋ ≈ ⌊g⌋.
Proof. intros; now rewrites. Qed.

Corollary from_adj_respects {x y} (f g : x ~{D}~> U y) :
  f ≈ g → ⌈f⌉ ≈ ⌈g⌉.
Proof. intros; now rewrites. Qed.

End Adjunction.

Arguments Adjunction {C D} F%_functor U%_functor.

Declare Scope adjunction_scope.
Declare Scope adjunction_type_scope.
Bind Scope adjunction_scope with Adjunction.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 59) : category_scope.
Notation "adj[ A ]" := (@adj _ _ _ _ A _ _)
  (at level 9, format "adj[ A ]") : morphism_scope.

(*
Wikipedia: “If the functor F : C ← D has two right adjoints G and G', then
   G and G' are naturally isomorphic. The same is true for left adjoints.”

--------
维基百科：“如果函子 F : C ← D 有两个右伴随 G 和 G'，那么 G 和 G' 在自然意义下是同构的。左伴随也同样成立。”
*)

Theorem right_adjoint_iso `(F : C ⟶ D) (G G' : D ⟶ C) :
  F ⊣ G → F ⊣ G' → G ≈ G'.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply adj; simpl.
      apply X; simpl.
      exact id.
    + apply adj; simpl.
      apply X0; simpl.
      exact id.
    + simpl.
      rewrite <- to_adj_nat_l.
      rewrite <- from_adj_nat_l.
      rewrite id_left.
      rewrite to_adj_comp_law.
      rewrite from_adj_comp_law.
      reflexivity.
    + simpl.
      rewrite <- to_adj_nat_l.
      rewrite <- from_adj_nat_l.
      rewrite id_left.
      rewrite to_adj_comp_law.
      rewrite from_adj_comp_law.
      reflexivity.
  - simpl.
    rewrite <- to_adj_nat_l.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    rewrite <- to_adj_nat_l.
    rewrite <- from_adj_nat_l.
    rewrite <- to_adj_nat_r.
    rewrite <- from_adj_nat_r.
    rewrite id_right.
    rewrite to_adj_comp_law.
    rewrite from_adj_comp_law.
    reflexivity.
Qed.

Theorem left_adjoint_iso `(G : D ⟶ C) (F F' : C ⟶ D) :
  F ⊣ G → F' ⊣ G → F ≈ F'.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply adj; simpl.
      apply X0; simpl.
      exact id.
    + apply adj; simpl.
      apply X; simpl.
      exact id.
    + simpl.
      rewrite <- from_adj_nat_r.
      rewrite <- to_adj_nat_r.
      rewrite id_right.
      rewrite from_adj_comp_law.
      rewrite to_adj_comp_law.
      reflexivity.
    + simpl.
      rewrite <- from_adj_nat_r.
      rewrite <- to_adj_nat_r.
      rewrite id_right.
      rewrite from_adj_comp_law.
      rewrite to_adj_comp_law.
      reflexivity.
  - simpl.
    rewrite <- from_adj_nat_r.
    rewrite <- to_adj_nat_r.
    rewrite id_right.
    rewrite <- from_adj_nat_l.
    rewrite <- to_adj_nat_l.
    rewrite id_left.
    rewrite from_adj_comp_law.
    rewrite to_adj_comp_law.
    reflexivity.
Qed.

(*
Future direction (no scaffolding here yet):

   “The most important property of adjoints is their continuity: every
    functor that has a left adjoint (and therefore is a right adjoint) is
    continuous (i.e. commutes with limits in the category theoretical
    sense); every functor that has a right adjoint (and therefore is a
    left adjoint) is cocontinuous (i.e. commutes with colimits).”
                                                              -- Wikipedia

   These theorems are formalized in Adjunction/Continuity.v:
   [right_adjoint_preserves_limits] (RAPL, proved directly by transposing
   cones through the hom-setoid isomorphism) and
   [left_adjoint_preserves_colimits] (LAPC, by duality via
   Adjunction/Opposite.v), phrased with the preservation vocabulary of
   Structure/Limit/Preservation.v.

--------
未来方向（这里还没有脚手架）：

“伴随最重要的性质是它们的连续性：每一个有左伴随的函子（因此是右伴随）是连续的（即在范畴理论的意义下与极限交换）；每一个有右伴随的函子（因此是左伴随）是共连续的（即与余极限交换）。”
                                                              -- 维基百科

这些定理在 Adjunction/Continuity.v 中形式化：[right_adjoint_preserves_limits]（RAPL，通过通过同值集同构转置锥直接证明）和 [left_adjoint_preserves_colimits]（LAPC，通过 Adjunction/Opposite.v 的对偶性），使用 Structure/Limit/Preservation.v 的保持词汇来表述。
*)

(** ** Transporting an adjunction along an isomorphism of left adjoints / ** 沿着左伴随的同构传输伴随 *)

(*
A functor naturally isomorphic to a left adjoint is a left adjoint,
   with the SAME right adjoint.  [right_adjoint_iso] and [left_adjoint_iso]
   above run the other way (from two adjunctions to an isomorphism),
   Theory/Equivalence/Adjunction.v transports along an EQUIVALENCE OF
   CATEGORIES rather than along a 2-cell, and Theory/Functor.v's
   [transport_adjunction] is a Type-level transport of a relation along
   an equality of indices, not an adjunction at all.  Built for
   Instance/Mod/Bimodule.v's part (c) (#401), which declared it there as
   its first consumer, and moved here verbatim by #431, whose
   functor-category remark is its second; [adjunction_along_left_iso]
   stays [Defined] and load-bearing (Bimodule.v's
   [btba_to_is_transposed], and [aali_to_is_transpose] below, reduce
   through it).

--------
一个函子自然同构于一个左伴随，则它也是一个左伴随，
   并且具有相同的右伴随。上面的 [right_adjoint_iso] 和 [left_adjoint_iso]
   运行方向相反（从两个伴随到一个同构），
   Theory/Equivalence/Adjunction.v 是沿着范畴的等价进行搬运，而不是沿着 2-胞箭，
   Theory/Functor.v 的 [transport_adjunction] 是沿索引相等的关系在类型层面的搬运，
   并不是一个伴随。它是为 Instance/Mod/Bimodule.v 的部分 (c) (#401) 构建的，
   那里声明它为其第一个使用者，并被 #431 原封不动地移动到这里，
   其函子-范畴的备注是第二个使用者；[adjunction_along_left_iso] 保持 [Defined] 并具有承重作用
   （Bimodule.v 中的 [btba_to_is_transposed] 和下面的 [aali_to_is_transpose] 通过它进行化简）。
*)

Section AdjunctionAlongIso.

#[local] Obligation Tactic := idtac.

Context {C D : Category}.
Context {F F' : D ⟶ C}.
Context {G : C ⟶ D}.
Context (Hiso : F ≈ F').
Context (A : F' ⊣ G).

Definition aali_cell (x : D) : F x ≅ F' x := projT1 Hiso x.

Lemma aali_natural {x y : D} (g : x ~> y) :
  fmap[F] g ∘ from (aali_cell x) ≈ from (aali_cell y) ∘ fmap[F'] g.
Proof.
  rewrite (projT2 Hiso x y g).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (aali_cell x)).
  now rewrite id_right.
Qed.

Definition aali_to (x : D) (y : C) (f : F x ~> y) : x ~> G y :=
  to (@adj C D F' G A x y) (f ∘ from (aali_cell x)).

Definition aali_from (x : D) (y : C) (g : x ~> G y) : F x ~> y :=
  from (@adj C D F' G A x y) g ∘ to (aali_cell x).

Lemma aali_to_from (x : D) (y : C) (g : x ~> G y) :
  aali_to x y (aali_from x y g) ≈ g.
Proof.
  unfold aali_to, aali_from.
  rewrite <- comp_assoc.
  rewrite (iso_to_from (aali_cell x)).
  rewrite id_right.
  exact (@from_adj_comp_law C D F' G A x y g).
Qed.

Lemma aali_from_to (x : D) (y : C) (f : F x ~> y) :
  aali_from x y (aali_to x y f) ≈ f.
Proof.
  unfold aali_to, aali_from.
  rewrite (@to_adj_comp_law C D F' G A x y (f ∘ from (aali_cell x))).
  rewrite <- comp_assoc.
  rewrite (iso_from_to (aali_cell x)).
  now rewrite id_right.
Qed.

Program Definition aali_iso (x : D) (y : C) :
  @Isomorphism Sets
    {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
    {| carrier := @hom D x (G y); is_setoid := @homset D x (G y) |} := {|
  to   := {| morphism := aali_to x y |};
  from := {| morphism := aali_from x y |}
|}.
Next Obligation.
  intros x y f f' Hf; unfold aali_to.
  now rewrite Hf.
Qed.
Next Obligation.
  intros x y g g' Hg; unfold aali_from.
  now rewrite Hg.
Qed.
Next Obligation. intros x y g; exact (aali_to_from x y g). Qed.
Next Obligation. intros x y f; exact (aali_from_to x y f). Qed.

Definition adjunction_along_left_iso : F ⊣ G.
Proof using A C D F F' G Hiso.
  unshelve eapply (@Build_Adjunction' C D F G aali_iso).
  - intros x y z f g; simpl; unfold aali_to.
    rewrite <- comp_assoc.
    rewrite (aali_natural g).
    rewrite comp_assoc.
    exact (@to_adj_nat_l C D F' G A x y z (f ∘ from (aali_cell y)) g).
  - intros x y z f g; simpl; unfold aali_to.
    rewrite <- comp_assoc.
    exact (@to_adj_nat_r C D F' G A x y z f (g ∘ from (aali_cell x))).
Defined.

Example aali_to_is_transpose (x : D) (y : C) (f : F x ~> y) :
  to (@adj C D F G adjunction_along_left_iso x y) f
    = to (@adj C D F' G A x y) (f ∘ from (aali_cell x)) := eq_refl.

End AdjunctionAlongIso.

Arguments aali_cell {C D F F'} Hiso x.
Arguments adjunction_along_left_iso {C D F F' G} Hiso A.
