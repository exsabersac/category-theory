Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Thin 范畴, hom-preorder 范畴 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/preorder
   Wikipedia: https://en.wikipedia.org/wiki/Preorder
   Book:      Mac Lane, "Categories for the Working Mathematician",
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.2
   Book:      Fong and Spivak, "Seven Sketches in Compositionality",

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~{C}~> y), f ≈ g.

(* Thinness is self-对偶: reversing arrows neither creates nor merges parallel
 pairs. Both directions hold nose because Construction/Opposite.v
 defines hom[C^op] x y as hom[C] y x reuses same hom-setoid.（已译） *)

Lemma Thin_Opposite {C : Category} : Thin C → Thin (C^op).
Proof. intros T x y f g; exact (T y x f g). Qed.

Lemma Opposite_Thin {C : Category} : Thin (C^op) → Thin C.
Proof. intros T x y f g; exact (T y x f g). Qed.

(* In thin 范畴 every 态射 is both monic epic (the classes at
 Theory/Morphisms.v), because both cancellation laws conclude
 equation between parallel 态射. The converse does not hold: being
 bimorphism everywhere is far weaker than thinness.（已译） *)

Lemma thin_Monic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Monic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

Lemma thin_Epic {C : Category} (T : Thin C) {x y : C} (f : x ~> y) : Epic f.
Proof. constructor; intros z g1 g2 _; apply T. Qed.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition thin_iso {C : Category} (T : Thin C) {x y : C}
  (f : x ~> y) (g : y ~> x) : x ≅ y :=
  {| to          := f
   ; from        := g
   ; iso_to_from := T y y (f ∘ g) id
   ; iso_from_to := T x x (g ∘ f) id |}.

(* * ** The hom-preorder 范畴 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition thin_preorder (C : Category) : relation (obj[C]) :=
  fun x y => inhabited (x ~{C}~> y).

(* It preorder: reflexivity 恒等箭头, transitivity is
 复合. The [inhabited] witnesses may eliminated here because the
 goal itself Prop. （已译） *)
Definition thin_PreOrder (C : Category) : PreOrder (thin_preorder C).
Proof.
  constructor.
  - intro x; exact (inhabits (@id C x)).
  - intros x y z Hxy Hyz.
    destruct Hxy as [f], Hyz as [g].
    exact (inhabits (g ∘ f)).
Defined.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_preorder_op (C : Category) (x y : obj[C]) :
  thin_preorder (C^op) x y = Basics.flip (thin_preorder C) x y.
Proof. reflexivity. Qed.

(*
   本节说明 Thin 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition HomChoice (C : Category) : Type :=
  ∀ (x y : obj[C]), thin_preorder C x y → x ~{C}~> y.

(* 相关说明。 （已译） *)

#[local] Obligation Tactic := idtac.

(* Products thin 范畴 thin: parallel pairs componentwise
 parallel. Instance/Proset/Closure.v instantiates at preorders. （已译） *)
Lemma Thin_Product {C D : Category} :
  Thin C → Thin D → Thin (C ∏ D).
Proof.
  intros TC TD [a b] [c d] [f g] [f' g']; split.
  - exact (TC a c f f').
  - exact (TD b d g g').
Qed.

(* Into thin target, any component family is natural — both 自然性
 squares are equations between parallel 态射. Functors into thin
 范畴 are therefore compared their 对象 actions alone.（已译） *)
Program Definition thin_natural {C D : Category} (TD : Thin D)
  (F G : C ⟶ D) (η : ∀ x : C, F x ~> G x) : F ⟹ G := {|
  transform := η
|}.
Next Obligation.
  intros C D TD F G η x y f.
  exact (TD _ _ _ _).
Qed.
Next Obligation.
  intros C D TD F G η x y f.
  exact (TD _ _ _ _).
Qed.

(* Parallel natural transformations into thin target agree pointwise:
 their components are parallel. (The 函子-范畴 packaging of
 this — 函子 范畴 into thin target is thin — lives in
 Instance/Proset/Closure.v, where [Fun] is available.)（已译） *)
Lemma Thin_Transform {C D : Category} (TD : Thin D)
  (F G : C ⟶ D) (σ τ : F ⟹ G) :
  ∀ x : C, transform σ x ≈ transform τ x.
Proof.
  intro x.
  exact (TD _ _ _ _).
Qed.
