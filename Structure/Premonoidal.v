Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    Wikipedia: https://en.wikipedia.org/wiki/Premonoidal_category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/premonoidal+category
   nLab:  https://ncatlab.org/nlab/show/Freyd+category
   Paper: Moggi, "Notions of computation and monads", Information and
   Paper: Power, Robinson, "Premonoidal categories and notions of

   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Premonoidal.

Context {C : Category}.
Context `{@Binoidal C}.

(*
   本节说明 Premonoidal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Notation "x ⊗ y" := (tensor x y)
  (at level 30, right associativity).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma premon_square_from {a b c d : C} (i : a ≅ b) (j : c ≅ d)
      (f : a ~> c) (g : b ~> d) :
  g ∘ to i ≈ to j ∘ f →
  f ∘ from i ≈ from j ∘ g.
Proof.
  intros sq.
  symmetry.
  rewrite <- (id_right g).
  rewrite <- (iso_to_from i).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (from j) g (to i)).
  rewrite sq.
  rewrite (comp_assoc (from j) (to j) f).
  rewrite (iso_from_to j).
  now rewrite id_left.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Premonoidal := {
  premon_I : C;

  premon_unit_left  {x} : premon_I ⊗ x ≅ x;                 (* lambda *)
  premon_unit_right {x} : x ⊗ premon_I ≅ x;                 (* rho *)
  premon_assoc {x y z} : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z);         (* alpha *)

  (* The forward structural maps are central; the from-directions are
     derived below via [central_iso_from]. *)
  premon_unit_left_central  {x} : central (to (@premon_unit_left x));
  premon_unit_right_central {x} : central (to (@premon_unit_right x));
  premon_assoc_central {x y z} : central (to (@premon_assoc x y z));

  (* Naturality, one variable at a time.  For the unitors there is a single
     variable; for the associator there are three squares, one for each
     tensor position. *)
  premon_unit_left_natural {x y} (g : x ~> y) :
    g ∘ to premon_unit_left
      << premon_I ⊗ x ~~> y >>
    to premon_unit_left ∘ (premon_I ⋊ g);

  premon_unit_right_natural {x y} (g : x ~> y) :
    g ∘ to premon_unit_right
      << x ⊗ premon_I ~~> y >>
    to premon_unit_right ∘ (g ⋉ premon_I);

  premon_assoc_natural_left {x y z w} (g : x ~> y) :
    (g ⋉ (z ⊗ w)) ∘ to premon_assoc
      << (x ⊗ z) ⊗ w ~~> y ⊗ (z ⊗ w) >>
    to premon_assoc ∘ ((g ⋉ z) ⋉ w);

  premon_assoc_natural_middle {x z w y} (h : z ~> w) :
    (x ⋊ (h ⋉ y)) ∘ to premon_assoc
      << (x ⊗ z) ⊗ y ~~> x ⊗ (w ⊗ y) >>
    to premon_assoc ∘ ((x ⋊ h) ⋉ y);

  premon_assoc_natural_right {x y z w} (i : z ~> w) :
    (x ⋊ (y ⋊ i)) ∘ to premon_assoc
      << (x ⊗ y) ⊗ z ~~> x ⊗ (y ⊗ w) >>
    to premon_assoc ∘ ((x ⊗ y) ⋊ i);

  (* Coherence: triangle (unitors against the associator, across the unit)
     and pentagon (the two reassociations of a fourfold tensor agree). *)
  premon_triangle {x y} :
    to premon_unit_right ⋉ y
      << (x ⊗ premon_I) ⊗ y ~~> x ⊗ y >>
    (x ⋊ to premon_unit_left) ∘ to premon_assoc;

  premon_pentagon {x y z w} :
    (x ⋊ to premon_assoc) ∘ to premon_assoc ∘ (to premon_assoc ⋉ w)
      << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
    to premon_assoc ∘ to premon_assoc
}.

Context `{Premonoidal}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma premon_unit_left_central_from {x} :
  central (from (@premon_unit_left _ x)).
Proof. apply central_iso_from, premon_unit_left_central. Qed.

Lemma premon_unit_right_central_from {x} :
  central (from (@premon_unit_right _ x)).
Proof. apply central_iso_from, premon_unit_right_central. Qed.

Lemma premon_assoc_central_from {x y z} :
  central (from (@premon_assoc _ x y z)).
Proof. apply central_iso_from, premon_assoc_central. Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma premon_unit_left_natural_from {x y} (g : x ~> y) :
  (premon_I ⋊ g) ∘ from premon_unit_left
    << x ~~> premon_I ⊗ y >>
  from premon_unit_left ∘ g.
Proof. apply premon_square_from, premon_unit_left_natural. Qed.

Lemma premon_unit_right_natural_from {x y} (g : x ~> y) :
  (g ⋉ premon_I) ∘ from premon_unit_right
    << x ~~> y ⊗ premon_I >>
  from premon_unit_right ∘ g.
Proof. apply premon_square_from, premon_unit_right_natural. Qed.

Lemma premon_assoc_natural_left_from {x y z w} (g : x ~> y) :
  ((g ⋉ z) ⋉ w) ∘ from premon_assoc
    << x ⊗ (z ⊗ w) ~~> (y ⊗ z) ⊗ w >>
  from premon_assoc ∘ (g ⋉ (z ⊗ w)).
Proof. apply premon_square_from, premon_assoc_natural_left. Qed.

Lemma premon_assoc_natural_middle_from {x z w y} (h : z ~> w) :
  ((x ⋊ h) ⋉ y) ∘ from premon_assoc
    << x ⊗ (z ⊗ y) ~~> (x ⊗ w) ⊗ y >>
  from premon_assoc ∘ (x ⋊ (h ⋉ y)).
Proof. apply premon_square_from, premon_assoc_natural_middle. Qed.

Lemma premon_assoc_natural_right_from {x y z w} (i : z ~> w) :
  ((x ⊗ y) ⋊ i) ∘ from premon_assoc
    << x ⊗ (y ⊗ z) ~~> (x ⊗ y) ⊗ w >>
  from premon_assoc ∘ (x ⋊ (y ⋊ i)).
Proof. apply premon_square_from, premon_assoc_natural_right. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma premon_joint_assoc_natural {x y z w u v}
      (g : x ~> y) (h : z ~> w) (i : u ~> v) :
  composite_ff' g (composite_ff' h i) ∘ to premon_assoc
    << (x ⊗ z) ⊗ u ~~> y ⊗ (w ⊗ v) >>
  to premon_assoc ∘ composite_ff' (composite_ff' g h) i.
Proof.
  unfold composite_ff'.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  (* left-position square: (g ⋉ (z ⊗ u)) ∘ alpha ≈ alpha ∘ ((g ⋉ z) ⋉ u) *)
  transitivity
    ((y ⋊ (w ⋊ i))
       ∘ ((y ⋊ (h ⋉ u)) ∘ (to premon_assoc ∘ ((g ⋉ z) ⋉ u)))).
  { apply compose_respects; [reflexivity|].
    apply compose_respects; [reflexivity|].
    apply premon_assoc_natural_left. }
  (* middle-position square: (y ⋊ (h ⋉ u)) ∘ alpha ≈ alpha ∘ ((y ⋊ h) ⋉ u) *)
  transitivity
    ((y ⋊ (w ⋊ i))
       ∘ (to premon_assoc ∘ (((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u)))).
  { apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply compose_respects; [|reflexivity].
    apply premon_assoc_natural_middle. }
  (* right-position square: (y ⋊ (w ⋊ i)) ∘ alpha ≈ alpha ∘ ((y ⊗ w) ⋊ i) *)
  rewrite comp_assoc.
  transitivity
    ((to premon_assoc ∘ ((y ⊗ w) ⋊ i))
       ∘ (((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u))).
  { apply compose_respects; [|reflexivity].
    apply premon_assoc_natural_right. }
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma premon_joint_assoc_natural_from {x y z w u v}
      (g : x ~> y) (h : z ~> w) (i : u ~> v) :
  composite_ff' (composite_ff' g h) i ∘ from premon_assoc
    << x ⊗ (z ⊗ u) ~~> (y ⊗ w) ⊗ v >>
  from premon_assoc ∘ composite_ff' g (composite_ff' h i).
Proof. apply premon_square_from, premon_joint_assoc_natural. Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma premon_unit_left_natural_ff' {x y} (g : x ~> y) :
  g ∘ to premon_unit_left
    << premon_I ⊗ x ~~> y >>
  to premon_unit_left ∘ composite_ff' (id[premon_I]) g.
Proof.
  rewrite composite_id_left.
  apply premon_unit_left_natural.
Qed.

Lemma premon_unit_right_natural_ff' {x y} (g : x ~> y) :
  g ∘ to premon_unit_right
    << x ⊗ premon_I ~~> y >>
  to premon_unit_right ∘ composite_ff' g (id[premon_I]).
Proof.
  rewrite composite_id_right.
  apply premon_unit_right_natural.
Qed.

Lemma premon_unit_left_natural_from_ff' {x y} (g : x ~> y) :
  composite_ff' (id[premon_I]) g ∘ from premon_unit_left
    << x ~~> premon_I ⊗ y >>
  from premon_unit_left ∘ g.
Proof.
  rewrite composite_id_left.
  apply premon_unit_left_natural_from.
Qed.

Lemma premon_unit_right_natural_from_ff' {x y} (g : x ~> y) :
  composite_ff' g (id[premon_I]) ∘ from premon_unit_right
    << x ~~> y ⊗ premon_I >>
  from premon_unit_right ∘ g.
Proof.
  rewrite composite_id_right.
  apply premon_unit_right_natural_from.
Qed.

Lemma premon_triangle_ff' {x y} :
  composite_ff' (to premon_unit_right) (id[y])
    << (x ⊗ premon_I) ⊗ y ~~> x ⊗ y >>
  composite_ff' (id[x]) (to premon_unit_left) ∘ to premon_assoc.
Proof.
  rewrite composite_id_left, composite_id_right.
  apply premon_triangle.
Qed.

Lemma premon_pentagon_ff' {x y z w} :
  composite_ff' (id[x]) (to premon_assoc)
      ∘ to premon_assoc
      ∘ composite_ff' (to premon_assoc) (id[w])
    << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
  to premon_assoc ∘ to premon_assoc.
Proof.
  rewrite composite_id_left, composite_id_right.
  apply premon_pentagon.
Qed.

End Premonoidal.
