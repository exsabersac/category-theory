Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Binoidal.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
    nLab: https://ncatlab.org/nlab/show/premonoidal+category

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CentralKit.

Context {C : Category}.
Context `{@Binoidal C}.

(* * ** Closure properties 中心性 （已译） *)

(* 相关说明。 （已译） *)
Lemma central_id {x : C} : central (@id C x).
Proof.
  intros x' y' f'; split.
  - rewrite !fmap_id; cat.
  - rewrite !fmap_id; cat.
Qed.

(* Centrality is a property of the ≈-class of a morphism: both defining
   squares mention [f] only through [fmap], which respects ≈. *)
Lemma central_respects {x y : C} {f g : x ~> y} :
  f ≈ g → central f → central g.
Proof.
  intros E cf x' y' f'.
  destruct (cf x' y' f') as [sq1 sq2].
  split.
  - rewrite <- E; exact sq1.
  - rewrite <- E; exact sq2.
Qed.

(* Central 态射 compose: expand [fmap] over composite with
 [fmap_comp], then paste [g]'s square followed [f]'s square. Each
 conjunct is single-level pasting two commuting squares.（已译） *)
Lemma central_comp {x y z : C} {f : y ~> z} {g : x ~> y} :
  central f → central g → central (f ∘ g).
Proof.
  intros cf cg x' y' f'.
  destruct (cf x' y' f') as [f1 f2].
  destruct (cg x' y' f') as [g1 g2].
  split.
  - rewrite !fmap_comp.
    rewrite !comp_assoc_sym.
    rewrite g1.
    rewrite !comp_assoc.
    now rewrite f1.
  - rewrite !fmap_comp.
    rewrite !comp_assoc.
    rewrite f2.
    rewrite !comp_assoc_sym.
    now rewrite g2.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma central_iso_from {x y : C} (i : x ≅ y) :
  central (to i) → central (from i).
Proof.
  intros ci x' y' f'.
  destruct (ci x' y' f') as [sq1 sq2].
  split.
  - assert (E : fmap[inj_right y] f'
                  ≈ fmap[inj_left y'] (to i)
                      ∘ (fmap[inj_right x] f' ∘ fmap[inj_left x'] (from i))).
    { rewrite !comp_assoc.
      rewrite sq1.
      rewrite !comp_assoc_sym.
      rewrite <- (fmap_comp (to i) (from i)).
      rewrite iso_to_from.
      rewrite fmap_id.
      now rewrite id_right. }
    rewrite E.
    rewrite !comp_assoc.
    rewrite <- (fmap_comp (from i) (to i)).
    rewrite iso_from_to.
    rewrite fmap_id.
    now rewrite id_left.
  - assert (E : fmap[inj_left y] f'
                  ≈ fmap[inj_right y'] (to i)
                      ∘ (fmap[inj_left x] f' ∘ fmap[inj_right x'] (from i))).
    { rewrite !comp_assoc.
      rewrite <- sq2.
      rewrite !comp_assoc_sym.
      rewrite <- (fmap_comp (to i) (from i)).
      rewrite iso_to_from.
      rewrite fmap_id.
      now rewrite id_right. }
    rewrite E.
    rewrite !comp_assoc.
    rewrite <- (fmap_comp (from i) (to i)).
    rewrite iso_from_to.
    rewrite fmap_id.
    now rewrite id_left.
Qed.

(* 相关说明。 （已译） *)

(* Tensoring 恒等 left leaves right tensoring [g]. （已译） *)
Lemma composite_id_left {x y : C} (w : C) (g : x ~> y) :
  composite_ff' (id[w]) g ≈ fmap[inj_right w] g.
Proof.
  unfold composite_ff'.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

(* Tensoring 恒等 right leaves left tensoring [f]. （已译） *)
Lemma composite_id_right {x y : C} (w : C) (f : x ~> y) :
  composite_ff' f (id[w]) ≈ fmap[inj_left w] f.
Proof.
  unfold composite_ff'.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma composite_ff'_comp_swap {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  fmap[inj_left y'] f ∘ fmap[inj_right y] g'
    ≈ fmap[inj_right z] g' ∘ fmap[inj_left x'] f →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof.
  intros sq.
  unfold composite_ff'.
  rewrite !fmap_comp.
  rewrite !comp_assoc_sym.
  rewrite (comp_assoc (fmap[inj_right z] g')).
  rewrite <- sq.
  now rewrite !comp_assoc_sym.
Qed.

Lemma composite_ff'_comp_l {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  central f →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof. intro cf; exact (composite_ff'_comp_swap (fst (cf x' y' g'))). Qed.

Lemma composite_ff'_comp_r {x y z x' y' z' : C} {f : y ~> z} {g : x ~> y}
      {f' : y' ~> z'} {g' : x' ~> y'} :
  central g' →
  composite_ff' (f ∘ g) (f' ∘ g') ≈ composite_ff' f f' ∘ composite_ff' g g'.
Proof. intro cg'; exact (composite_ff'_comp_swap (snd (cg' y z f))). Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition CentralSub : Subcategory C := {|
  sobj  := fun _ => poly_unit;
  shom  := fun x y _ _ f => central f;
  scomp := fun _ _ _ _ _ _ _ _ cf cg => central_comp cf cg;
  sid   := fun _ _ => central_id
|}.

Lemma Centre_wide : Wide C CentralSub.
Proof. intro x; exact ttt. Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

End CentralKit.

(*
   本节说明 Central 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Centre (C : Category) `{H : @Binoidal C} : Category :=
  Sub C (@CentralSub C H).
