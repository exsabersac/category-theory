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

(*
   关于范畴的来源与用途

   SEP:   https://plato.stanford.edu/entries/category-theory/
   nLab:  https://ncatlab.org/nlab/show/E-category
   nLab:  https://ncatlab.org/nlab/show/Yoneda+lemma
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",

   本节说明自然变换、函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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

(*
   本节说明 Category 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
   本节说明hom、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
   本节说明 Category 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
