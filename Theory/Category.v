Require Import Category.Lib.

Generalizable All Variables.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

(*
nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   A category C consists of a collection of objects, a hom `x ~> y` of
   morphisms for each pair of objects, an identity `id : x ~> x` for each
   object, and a composition `f ∘ g : x ~> z` for `g : x ~> y` and
   `f : y ~> z`, subject to the unit laws `id ∘ f ≈ f` and `f ∘ id ≈ f` and
   the associativity law `f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h`. Here the hom is a
   setoid (a hom-setoid) rather than a bare set, so morphism equality is the
   chosen equivalence `≈` rather than Coq's `=`.

   The objects of a category are all of some `Type`.

  Morphisms, or arrows, are also of type `Type`, but always in a universe
  above objects. All of the library has `Universe Polymorphism` enabled,
  allowing categories whose objects are categories, etc.

  The morphisms identified by `A ~> B` form a hom-set, except that in this
  library it is a hom-setoid, requiring the meaning of (computationally
  relevant) equivalence between morphisms to be given. This makes it a
  quotient category C/R over the equivalence relation R, but since this is
  almost always needed (since equality is very restrictive in Coq's type
  theory), we call it a [Category] here, and assume the existence of some
  other category using only equality, with a functor from that category to
  this.

  Categories (as distinct from Category/~) are identified by [homset :=
  Morphism_equality].

--------
nLab：https://ncatlab.org/nlab/show/category
维基百科：https://en.wikipedia.org/wiki/Category_(mathematics)

一个范畴 C 由一个对象集合、每对对象的态射 Hom、每个对象的恒等映射以及对于 `g : x ~> y` 和 `f : y ~> z` 的复合构成，且遵循单位律 `id ∘ f ≈ f` 和 `f ∘ id ≈ f` 以及结合律 `f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h`。这里的 Hom 是一个集合等价类（一个 Hom-集合等价类），而不是普通集合，因此态射的相等性是所选的等价关系 `≈`，而不是 Coq 的 `=`。

一个范畴的对象都是某些 `Type`。

态射或箭头也是 `Type` 类型，但总是在对象之上的范畴中。整个库都启用了 `Universe Polymorphism`，允许对象本身是范畴的范畴，等等。

由 `A ~> B` 识别的态射形成一个同态集合，然而在这个库中，它是一个同态集合体（hom-setoid），需要给出态射之间（计算上相关的）等价的含义。这使得它成为一个在等价关系 R 下的商范畴 C/R，但由于这几乎总是需要的（因为在 Coq 的类型理论中，等式非常严格），我们在这里称之为 [Category]，并假设存在某个仅使用等式的其他范畴，以及一个从该范畴到此范畴的函子。

范畴（与 Category/~ 不同）由 [homset := Morphism_equality] 识别。
*)

(*
Where categories come from, and what the definition is for

   SEP:   https://plato.stanford.edu/entries/category-theory/
   nLab:  https://ncatlab.org/nlab/show/E-category
   nLab:  https://ncatlab.org/nlab/show/Yoneda+lemma
   Paper: Eilenberg, Mac Lane, “General theory of natural equivalences”,
          Transactions of the American Mathematical Society 58, 1945

   Categories, functors, and natural transformations entered mathematics
   together, in Eilenberg and Mac Lane's “General theory of natural
   equivalences” (1945) — the abstraction, so the Stanford Encyclopedia
   recounts, of their “Group Extensions and Homology” (Annals of
   Mathematics 43, 1942), where particular functors and natural
   transformations were already at work among groups.  The motivation ran
   backwards through the definitions: the aim was to make “natural”
   precise, which required functors, which in turn required categories.
   In their own words, “the whole concept of a category is essentially an
   auxiliary one; our basic concepts are essentially those of a functor
   and of a natural transformation”.  Even the names are borrowed — per
   the same Encyclopedia entry, “functor” from Carnap, “category” from
   Aristotle, Kant, and Peirce.

   What the auxiliary concept isolates is the least structure in which
   composition makes sense: objects, morphisms, identities, an
   associative composition, and nothing else.  Milewski's preface to
   “Category Theory for Programmers” (2014) places composition “at the
   very root of category theory”.  Yet the definition never asks what an
   object is; every property must be phrased through the morphisms into
   and out of it, and the Yoneda lemma shows the discipline loses
   nothing — per the nLab, probes by the other objects of C suffice to
   distinguish the objects of C.  The reward is altitude: “Category
   theory takes a bird's eye view of mathematics.  From high in the sky,
   details become invisible, but we can spot patterns that were
   impossible to detect from ground level” (Leinster, “Basic Category
   Theory”, CUP 2014).

   The subsequent history reads as a map of this library.  Grothendieck
   made categories intrinsic to homological algebra (“Sur quelques
   points d'algèbre homologique”, Tôhoku Math. J. 9, 1957); Kan isolated
   adjoint functors (“Adjoint Functors”, TAMS 87, 1958), the subject of
   Theory/Adjunction.v; Lawvere turned algebraic theories into
   categories and their models into functors (“Functorial Semantics of
   Algebraic Theories”, PNAS 50, 1963), realized here in
   Theory/Lawvere.v, and axiomatized the category of sets (PNAS 52,
   1964); Lambek read categories as deductive systems and cartesian
   closed categories as typed lambda calculus, the bridge behind
   Structure/Closed.v and Instance/Lambda/.  Baez and Stay extend the
   same dictionary to physics and topology, with closed symmetric
   monoidal categories as the common language (“Physics, Topology,
   Logic and Computation: A Rosetta Stone”, arXiv:0903.0340, 2009).

   The class below is what the nLab calls an E-category: a category
   enriched in setoids, taking a specified equivalence relation rather
   than the identity type as the equality of morphisms — each hom
   carries a chosen equivalence and composition carries the
   extensionality witness [compose_respects].  Coq's intensional type
   theory has no quotient types, so a hom cannot be quotiented after
   the fact; the relation must travel with the hom.  The choice is what
   lets the library run on zero axioms: Instance/Sets.v identifies two
   setoid maps whenever they agree pointwise up to the codomain's ≈, so
   functions are extensional without the functional extensionality
   axiom, and a quotient category is merely another choice of [homset]
   over the same homs (compare the hom-congruence quotients of
   Construction/Quotient.v).  The price is a standing obligation: every
   operation on morphisms must be shown Proper, and rewriting proceeds
   through Coq's generalized setoid rewriting.  One further field is
   deliberate: [comp_assoc_sym] restates associativity in the mirrored
   orientation so that Construction/Opposite.v can simply exchange the
   two fields, making C^op^op = C hold by reflexivity;
   [Build_Category'] then recovers the redundant field for instance
   authors.  Nearly every file in the library requires this one,
   directly or through its immediate consumers Theory/Functor.v and
   Theory/Isomorphism.v.

--------
范畴从何而来，以及定义为何

   SEP:   https://plato.stanford.edu/entries/category-theory/
   nLab:  https://ncatlab.org/nlab/show/E-category
   nLab:  https://ncatlab.org/nlab/show/Yoneda+lemma
   Paper: Eilenberg, Mac Lane, “General theory of natural equivalences”,
          Transactions of the American Mathematical Society 58, 1945

   范畴、函子与自然变换一同进入数学，见于 Eilenberg 与 Mac Lane 的
   “General theory of natural equivalences”（1945）——据 Stanford Encyclopedia，
   这是他们 “Group Extensions and Homology”（Annals of Mathematics 43, 1942）
   的抽象，彼处特定函子与自然变换已在群之间运作。动机沿定义反向推进：
   目标是使「自然」精确，这需要函子，进而需要范畴。用他们自己的话说，
   「范畴的整个概念本质上是辅助性的；我们的基本概念本质上是函子与自然变换」。
   甚至名称也是借用的——据同一 Encyclopedia 条目，「函子」来自 Carnap，
   「范畴」来自 Aristotle、Kant 与 Peirce。

   该辅助概念所隔离的，是使复合有意义的最小结构：对象、态射、恒等、
   结合的复合，别无其他。Milewski《Category Theory for Programmers》(2014)
   序言把复合放在「范畴论的根基」。然而定义从不追问对象是什么；每一性质
   都必须通过出入它的态射表述，而 Yoneda 引理表明这套纪律毫无损失——
   据 nLab，用 C 的其他对象探测足以区分 C 的对象。回报是高度：「范畴论
   对数学取鸟瞰视角。从高空细节不可见，但我们能发现地面上不可能察觉的
   模式」（Leinster, “Basic Category Theory”, CUP 2014）。

   其后历史可读作本库的地图。Grothendieck 使范畴成为同调代数的内在部分
   （“Sur quelques points d'algèbre homologique”, Tôhoku Math. J. 9, 1957）；
   Kan 分离出伴随函子（“Adjoint Functors”, TAMS 87, 1958），即 Theory/Adjunction.v
   的主题；Lawvere 把代数理论变成范畴、把模型变成函子（“Functorial Semantics
   of Algebraic Theories”, PNAS 50, 1963），此处实现于 Theory/Lawvere.v，并公理化
   集合范畴（PNAS 52, 1964）；Lambek 把范畴读作演绎系统、把笛卡尔闭范畴读作
   带类型 λ 演算，即 Structure/Closed.v 与 Instance/Lambda/ 背后的桥梁。Baez 与
   Stay 把同一词典扩展到物理与拓扑，以闭对称幺半范畴为共同语言
   （“Physics, Topology, Logic and Computation: A Rosetta Stone”, arXiv:0903.0340, 2009）。

   下方的类即 nLab 所称 E-category：在 setoid 中充实的范畴，以指定等价关系
   而非恒等类型作为态射相等——每个 hom 携带选定等价，复合携带外延性见证
   [compose_respects]。Coq 的内涵类型论没有商类型，故不能事后对 hom 取商；
   关系必须与 hom 同行。这一选择使库能在零公理上运行：Instance/Sets.v 在
   逐点按陪域 ≈ 一致时把两个 setoid 映射视为同一，故函数外延无需函数外延公理，
   商范畴只是在同一批 hom 上另选 [homset]（比较 Construction/Quotient.v 的
   hom-合同商）。代价是持续义务：态射上每个运算都必须证明 Proper，重写经
   Coq 的广义 setoid rewriting 进行。另有一字段是刻意的：[comp_assoc_sym]
   以镜像方向重述结合律，使 Construction/Opposite.v 只需交换两字段，从而
   C^op^op = C 由 reflexivity 成立；[Build_Category'] 再为实例作者恢复冗余字段。
   库中几乎每个文件都直接或经其直接消费者 Theory/Functor.v 与
   Theory/Isomorphism.v  Require 本文件。
*)


(*
   【Class Category 语法与字段展开】/ Syntax & field walkthrough

   1) Class 是 Coq 命令（与 Record / Inductive 同级），声明类型类；
      Instance 填实现。Class ≈ Haskell class，Instance ≈ instance；
      差别是定律也写成字段，须交证明，并参与类型类搜索。
      [Class] is a vernacular command (alongside Record/Inductive).
      Class ≈ Haskell class; Instance ≈ instance. Laws are fields
      (proofs required) and take part in typeclass search.

   2) Record 是单构造子 Inductive 的糖（命名字段+投影）；Class 在
      Record 上再加实例搜索。多构造子形状用 Inductive；捆字段用
      Record/Class。
      Record ≈ single-constructor Inductive with projections; Class
      adds instance search. Use Inductive for variants; Record/Class
      to bundle fields.

   3) 宇宙头 / Universe header
        Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)}
      - o : 对象 [obj] 所在宇宙 / universe of objects
      - h : 态射载体 [uhom]/[hom] 所在宇宙 / universe of hom carriers
      - p : Setoid 等价关系的命题宇宙，约束 h <= p
            / universe of equivalence proofs, with h <= p
      类本身落在更高一层，避免自指。
      The class lives one level above to avoid self-membership.

   4) 数据字段 / Data fields
      - obj : 对象集合 / collection of objects
      - uhom : Hom setoid 的宇宙别名 / universe alias for hom-setoids
      - hom / where “a ~> b” : 态射类型与局部记法
        / morphism type and local notation
      - homset : 每个 Hom 是 Setoid@{h p}，相等是 ≈ 而非定义相等 =
        / each Hom is a Setoid; equality is ≈, not definitional =

   5) 运算 / Operations
      - id {x} : 恒等；{x} 为隐式参数 / identity; {x} implicit
      - compose {x y z} f g / “f ∘ g” : 先 g 后 f（数学常见顺序）
        / apply g then f (usual mathematical order)

   6) 尊重等价 / Respect for equivalence
      compose_respects : Proper (equiv ==> equiv ==> equiv) compose
      f≈f' 且 g≈g' ⇒ f∘g ≈ f'∘g'。否则无法对复合做 setoid 改写。
      Without this, setoid rewriting through compose is illegitimate.

   7) 公理（均对 ≈）/ Laws (all up to ≈)
      id_left / id_right : 左右单位 / unit laws
      comp_assoc / comp_assoc_sym : 结合律两个方向（后者便于对偶与 rewrite）
      / associativity both ways (sym helps duality & rewrite)

   8) dom / cod : 由态射类型推出的源/靶缩写，非额外数据。
      / domain/codomain abbreviations derived from the morphism type.

   阅读顺序建议：obj → hom/homset → id/compose → Proper → 四条律。
   Suggested reading order: obj → hom/homset → id/compose → Proper → laws.
*)

Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};                       (* collection of objects / 对象的集合 *)

  uhom := Type@{h} : Type@{h+1};        (* universe of hom-setoids / 同态集合的宇宙 *)
  hom : obj → obj → uhom where "a ~> b" := (hom a b);  (* morphisms x ~> y / 态射 x ~> y *)
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);  (* hom is a setoid; equality is ≈ / hom 是一个集合等价结构；相等性是 ≈ *)

  id {x} : x ~> x;                      (* identity morphism on x / x上的恒等态射 *)
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);     (* composition f ∘ g / 组合 f ∘ g *)

  compose_respects {x y z} :            (* compose respects ≈ (bifunctorial Proper) / 组成 respects ≈（双函子 Proper） *)
    Proper@{h p} (respectful@{h p h p h p} equiv
                    (respectful@{h p h p h p} equiv equiv))
      (@compose x y z);

  dom {x y} (f : x ~> y) := x;          (* domain (source) of a morphism / 一个态射的定义域（来源） *)
  cod {x y} (f : x ~> y) := y;          (* codomain (target) of a morphism / 一个态射的陪域（目标） *)

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;  (* left unit law / 左单位律 *)
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;  (* right unit law / 右单位律 *)

  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;         (* associativity / 结合性 *)
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)          (* associativity, dual form (built-in duality) / 结合性，双重形式（内置二重性） *)
}.
#[export] Existing Instance homset.
#[export] Existing Instance compose_respects.

Declare Scope category_scope.
Declare Scope object_scope.
Declare Scope homset_scope.
Declare Scope morphism_scope.

Bind Scope category_scope with Category.
Bind Scope object_scope with obj.
Bind Scope homset_scope with hom.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope homset_scope with homset.
Delimit Scope morphism_scope with morphism.

Arguments dom {_%_category _%_object _%_object} _%_morphism.
Arguments cod {_%_category _%_object _%_object} _%_morphism.

Notation "obj[ C ]" := (@obj C%category)
  (at level 0, format "obj[ C ]") : type_scope.
Notation "hom[ C ]" := (@hom C%category)
  (at level 0, format "hom[ C ]") : type_scope.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.
Notation "x ~{ C }~> y" := (@hom C%category x%object y%object)
  (at level 90) : homset_scope.

Notation "x <~ y" := (@hom _%category y%object x%object)
  (at level 90, right associativity, only parsing) : homset_scope.
Notation "x <~{ C }~ y" := (@hom C%category y%object x%object)
  (at level 90, only parsing) : homset_scope.

Notation "id[ x ]" := (@id _%category x%object)
  (at level 9, format "id[ x ]") : morphism_scope.

Notation "id{ C }" := (@id C%category _%object)
  (at level 9, format "id{ C }") : morphism_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.
Notation "f ∘[ C ] g" :=
  (@compose C%category _%object _%object _%object f%morphism g%morphism)
  (at level 40, only parsing) : morphism_scope.

Notation "f ≈[ C ] g" :=
  (@equiv _ (@homset C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.
Notation "f ≈[ C ] g" :=
  (@equiv _ (@homset C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.

Notation "f << A ~~> B >> g" :=
  (@equiv (A%object ~> B%object)%homset _ f%morphism g%morphism)
  (at level 99, A at next level, B at next level, only parsing) : category_theory_scope.

Coercion obj : Category >-> Sortclass.

#[export] Hint Rewrite @id_left : categories.
#[export] Hint Rewrite @id_right : categories.

(*
[Build_Category'] is a custom constructor that automatically provides the
   definition of [comp_assoc_sym] from [comp_assoc] by symmetry. It is intended
   to be used with the [refine] tactic, such as in the example below.

--------
[Build_Category'] 是一个自定义构造函数，它通过对称性自动提供 [comp_assoc] 的 [comp_assoc_sym] 定义。它旨在与 [refine] 策略一起使用，例如下例所示。
*)
Definition Build_Category'
           {obj} hom {homset} id compose
           {compose_respects}
           {id_left id_right comp_assoc} :=
  {| obj              := obj;
     hom              := hom;
     homset           := homset;
     id               := id;
     compose          := compose;
     compose_respects := compose_respects;
     id_left          := id_left;
     id_right         := id_right;
     comp_assoc       := comp_assoc;
     comp_assoc_sym   :=
       fun _ _ _ _ _ _ _ => symmetry (@comp_assoc _ _ _ _ _ _ _);
  |}.

Example Build_Category'_Coq : Category.
Proof.
  unshelve refine (Build_Category' (@Basics.arrow)
                                   (@Datatypes.id) (@Basics.compose));
  intros; try reflexivity.
  - refine {| equiv := fun f g => ∀ x, f x = g x |}.
    equivalence.
    now transitivity (y x0).
  - proper.
    now rewrite X, X0.
Defined.

Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope morphism_scope.

(*
The hom-setoid whose equivalence is Coq's strict equality `eq`. Equipping a
   hom with this `Setoid` recovers the classical (non-quotient) notion of a
   category, where two morphisms are equal only when definitionally equal.

--------
同态集族，其等价关系是 Coq 的严格相等 `eq`。为一个同态配备这个 `Setoid` 可以恢复经典（非商）范畴的概念，其中两个态射仅在定义上相等时才相等。
*)
Program Definition Morphism_equality@{o h p}
  {ob : Type@{o}} {hom : ob → ob → Type@{h}}
  (x y : ob) : Setoid@{h p} (hom x y) := {|
  equiv := eq
|}.
Arguments Morphism_equality {_ _} _ _ /.

Section Category.

Context {C : Category}.

Corollary dom_id {x : C} : dom (@id C x) = x.
Proof. auto. Qed.

Corollary cod_id {x : C} : cod (@id C x) = x.
Proof. auto. Qed.

Corollary dom_comp {x y z : C} (g : y ~> z) (f : x ~> y) :
  dom g = cod f ↔ dom (g ∘ f) = dom f.
Proof. split; auto. Qed.

Corollary cod_comp {x y z : C} (g : y ~> z) (f : x ~> y) :
  dom g = cod f ↔ cod (g ∘ f) = cod g.
Proof. split; auto. Qed.

(*
Riehl, “Category Theory in Context”, §1.1: the identity at an object is
   unique. An endomorphism that is a two-sided unit is [id] — and either half
   of that hypothesis already suffices, since testing it against [id] itself
   collapses it to a unit law.

--------
Riehl，《语境中的范畴论》，§1.1：一个对象的恒等映射是唯一的。一个作为双边单位的自同态是[id] —— 仅凭假设的一半就足够了，因为将其与[id]本身进行测试会将其归约为单位律。
*)
Corollary id_unique_left {x : C} (u : x ~> x) :
  (∀ (y : C) (f : x ~> y), f ∘ u ≈ f) → u ≈ id.
Proof. intro H; rewrite <- (id_left u); apply H. Qed.

Corollary id_unique_right {x : C} (u : x ~> x) :
  (∀ (y : C) (f : y ~> x), u ∘ f ≈ f) → u ≈ id.
Proof. intro H; rewrite <- (id_right u); apply H. Qed.

Corollary id_unique {x : C} (u : x ~> x) :
  ((∀ (y : C) (f : x ~> y), f ∘ u ≈ f) ∧ (∀ (y : C) (f : y ~> x), u ∘ f ≈ f)) →
  u ≈ id.
Proof. intros [H _]; now apply id_unique_left. Qed.

End Category.

Arguments dom {_%_category _%_object _%_object} _%_morphism.
Arguments cod {_%_category _%_object _%_object} _%_morphism.
Arguments id_left {_%_category _%_object _%_object} _%_morphism.
Arguments id_right {_%_category _%_object _%_object} _%_morphism.
Arguments comp_assoc {_%_category _%_object _%_object _%_object _%_object}
  _%_morphism _%_morphism _%_morphism.

(*
The hom relation of any category is a preorder on objects: reflexivity is
   witnessed by `id` and transitivity by composition (note the order: `g ∘ f`
   for `f : x ~> y` and `g : y ~> z`). This is the standard observation that a
   category has an underlying preorder of objects (a preorder is exactly a thin
   category).

--------
任意范畴的 Hom 关系是对象上的一个预序关系：自反性由 `id` 体现，传递性由复合体现（注意顺序：`g ∘ f` 对于 `f : x ~> y` 和 `g : y ~> z`）。这是一个标准观察，即一个范畴具有对象的底层预序关系（预序正好是一个稀薄范畴）。
*)
#[export]
Program Instance hom_preorder {C : Category} : PreOrder (@hom C) := {
  PreOrder_Reflexive  := fun _ => id;
  PreOrder_Transitive := fun _ _ _ f g => g ∘ f
}.

Ltac comp_left :=
  try rewrite <- !comp_assoc;
  apply compose_respects; [reflexivity|].

Ltac comp_right :=
  try rewrite !comp_assoc;
  apply compose_respects; [|reflexivity].

#[export] Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) =>
  apply compose_respects; auto : category_laws.
#[export] Hint Extern 10 (?X ∘ (?Y ∘ ?Z) ≈ ?W) =>
  apply comp_assoc : category_laws.

Ltac rewrites :=
  repeat match goal with
  | [ H : ?X ≈ ?Y                      |- context[?X] ] => rewrite !H; clear H
  | [ H : ?X ≈ ?Y                      |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?X] ] => srewrite H; clear H

  | [ H : ?X ≈ ?Y                      |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ?X ≈ ?Y                      |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?Y] ] => srewrite_r H; clear H
  end.
