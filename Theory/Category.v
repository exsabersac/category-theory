Require Import Category.Lib.

Generalizable All Variables.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

(* 范畴从何而来，以及定义为何

   SEP:   https://plato.stanford.edu/entries/category-theory/
   nLab:  https://ncatlab.org/nlab/show/E-category
   nLab:  https://ncatlab.org/nlab/show/Yoneda+lemma
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
          Transactions of the American Mathematical Society 58, 1945

   范畴、函子与自然变换一同进入数学，见于 Eilenberg 与 Mac Lane 的
   "General theory of natural equivalences"（1945）——据 Stanford Encyclopedia，
   这是他们 "Group Extensions and Homology"（Annals of Mathematics 43, 1942）
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
   模式」（Leinster, "Basic Category Theory", CUP 2014）。

   其后历史可读作本库的地图。Grothendieck 使范畴成为同调代数的内在部分
   （"Sur quelques points d'algèbre homologique", Tôhoku Math. J. 9, 1957）；
   Kan 分离出伴随函子（"Adjoint Functors", TAMS 87, 1958），即 Theory/Adjunction.v
   的主题；Lawvere 把代数理论变成范畴、把模型变成函子（"Functorial Semantics
   of Algebraic Theories", PNAS 50, 1963），此处实现于 Theory/Lawvere.v，并公理化
   集合范畴（PNAS 52, 1964）；Lambek 把范畴读作演绎系统、把笛卡尔闭范畴读作
   带类型 λ 演算，即 Structure/Closed.v 与 Instance/Lambda/ 背后的桥梁。Baez 与
   Stay 把同一词典扩展到物理与拓扑，以闭对称幺半范畴为共同语言
   （"Physics, Topology, Logic and Computation: A Rosetta Stone", arXiv:0903.0340, 2009）。

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
   Theory/Isomorphism.v  Require 本文件。 *)

(* Where categories come from, and what the definition is for

   SEP:   https://plato.stanford.edu/entries/category-theory/
   nLab:  https://ncatlab.org/nlab/show/E-category
   nLab:  https://ncatlab.org/nlab/show/Yoneda+lemma
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
          Transactions of the American Mathematical Society 58, 1945

   Categories, functors, and natural transformations entered mathematics
   together, in Eilenberg and Mac Lane's "General theory of natural
   equivalences" (1945) — the abstraction, so the Stanford Encyclopedia
   recounts, of their "Group Extensions and Homology" (Annals of
   Mathematics 43, 1942), where particular functors and natural
   transformations were already at work among groups.  The motivation ran
   backwards through the definitions: the aim was to make "natural"
   precise, which required functors, which in turn required categories.
   In their own words, "the whole concept of a category is essentially an
   auxiliary one; our basic concepts are essentially those of a functor
   and of a natural transformation".  Even the names are borrowed — per
   the same Encyclopedia entry, "functor" from Carnap, "category" from
   Aristotle, Kant, and Peirce.

   What the auxiliary concept isolates is the least structure in which
   composition makes sense: objects, morphisms, identities, an
   associative composition, and nothing else.  Milewski's preface to
   "Category Theory for Programmers" (2014) places composition "at the
   very root of category theory".  Yet the definition never asks what an
   object is; every property must be phrased through the morphisms into
   and out of it, and the Yoneda lemma shows the discipline loses
   nothing — per the nLab, probes by the other objects of C suffice to
   distinguish the objects of C.  The reward is altitude: "Category
   theory takes a bird's eye view of mathematics.  From high in the sky,
   details become invisible, but we can spot patterns that were
   impossible to detect from ground level" (Leinster, "Basic Category
   Theory", CUP 2014).

   The subsequent history reads as a map of this library.  Grothendieck
   made categories intrinsic to homological algebra ("Sur quelques
   points d'algèbre homologique", Tôhoku Math. J. 9, 1957); Kan isolated
   adjoint functors ("Adjoint Functors", TAMS 87, 1958), the subject of
   Theory/Adjunction.v; Lawvere turned algebraic theories into
   categories and their models into functors ("Functorial Semantics of
   Algebraic Theories", PNAS 50, 1963), realized here in
   Theory/Lawvere.v, and axiomatized the category of sets (PNAS 52,
   1964); Lambek read categories as deductive systems and cartesian
   closed categories as typed lambda calculus, the bridge behind
   Structure/Closed.v and Instance/Lambda/.  Baez and Stay extend the
   same dictionary to physics and topology, with closed symmetric
   monoidal categories as the common language ("Physics, Topology,
   Logic and Computation: A Rosetta Stone", arXiv:0903.0340, 2009).

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
   Theory/Isomorphism.v. *)

Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};                       (* collection of objects *)

  uhom := Type@{h} : Type@{h+1};        (* universe of hom-setoids *)
  hom : obj → obj → uhom where "a ~> b" := (hom a b);  (* morphisms x ~> y *)
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);  (* hom is a setoid; equality is ≈ *)

  id {x} : x ~> x;                      (* identity morphism on x *)
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);     (* composition f ∘ g *)

  compose_respects {x y z} :            (* compose respects ≈ (bifunctorial Proper) *)
    Proper@{h p} (respectful@{h p h p h p} equiv
                    (respectful@{h p h p h p} equiv equiv))
      (@compose x y z);

  dom {x y} (f : x ~> y) := x;          (* domain (source) of a morphism *)
  cod {x y} (f : x ~> y) := y;          (* codomain (target) of a morphism *)

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;  (* left unit law *)
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;  (* right unit law *)

  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;         (* associativity *)
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)          (* associativity, dual form (built-in duality) *)
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

(* [Build_Category'] is a custom constructor that automatically provides the
   definition of [comp_assoc_sym] from [comp_assoc] by symmetry. It is intended
   to be used with the [refine] tactic, such as in the example below. *)
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

(* The hom-setoid whose equivalence is Coq's strict equality `eq`. Equipping a
   hom with this `Setoid` recovers the classical (non-quotient) notion of a
   category, where two morphisms are equal only when definitionally equal. *)
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

(* Riehl, "Category Theory in Context", §1.1: the identity at an object is
   unique. An endomorphism that is a two-sided unit is [id] — and either half
   of that hypothesis already suffices, since testing it against [id] itself
   collapses it to a unit law. *)
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

(* The hom relation of any category is a preorder on objects: reflexivity is
   witnessed by `id` and transitivity by composition (note the order: `g ∘ f`
   for `f : x ~> y` and `g : y ~> z`). This is the standard observation that a
   category has an underlying preorder of objects (a preorder is exactly a thin
   category). *)
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
