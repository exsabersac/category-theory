Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Comma.

Context {A B C : Category}.

Context {S : A ⟶ C}.
Context {T : B ⟶ C}.

(** The comma 范畴 (S ↓ T) two 函子 common codomain. （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/comma+object
   nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab: https://ncatlab.org/nlab/show/scone

   本节说明伴随、函子、Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Set Transparent Obligations.
#[local] Obligation Tactic := idtac.

Program Definition Comma : Category := {|
  (* objects: triples (a, b, h : S a ~> T b) *)
  obj     := ∃ p : A ∏ B, S (fst p) ~{C}~> T (snd p);
  (* 态射: pairs (f, g) 交换方块 h' ∘ S f ≈ T g ∘ h （已译） *)
  hom     := fun x y =>
    ∃ f : (fst (`1 x) ~{A}~> fst (`1 y)) * (snd (`1 x) ~{B}~> snd (`1 y)),
      `2 y ∘ fmap[S] (fst f) ≈ fmap[T] (snd f) ∘ `2 x;
  (* 等价: componentwise ≈ A B (square 证明 irrelevant) （已译） *)
  homset  := fun _ _ =>
    {| equiv := fun f g => (fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g) |};
  id      := fun _ => ((id, id); _);    (* identity (id_a, id_b) *)
  (* composition is componentwise (f ∘ f', g ∘ g') *)
  compose := fun _ _ _ f g => ((fst `1 f ∘ fst `1 g, snd `1 f ∘ snd `1 g); _)
|}.
Next Obligation.
  intros [[]] [[]]; simpl in *; equivalence.
Qed.
Next Obligation.
  intros.
  simpl.
  rewrite !fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ?; simpl.
  intros [[]] [[]]; simpl in *.
  rewrite !fmap_comp.
  rewrite comp_assoc.
  rewrites.
  rewrite <- !comp_assoc.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  intros ? ? ? ? ? [e0 e1] ? ? [e2 e3].
  split.
  - now simpl; rewrite e0, e2.
  - now simpl; rewrite e1, e3.
Qed.
Next Obligation.
  intros; simpl.
  split; now rewrite id_left.
Qed.
Next Obligation.
  intros. simpl.
  split; now rewrite id_right.
Qed.
Next Obligation.
  intros.
  simpl.
  split; apply comp_assoc.
Qed.
Next Obligation.
  intros. simpl.
  split; apply comp_assoc_sym.
Qed.

Program Instance comma_proj  : Comma ⟶ A ∏ B := {|
  fobj := fun x => ``x;
  fmap := fun _ _ f => ``f
|}.
Next Obligation.
  intros ? ? ? ? [e0 e1].
  now split.
Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj1 : Comma ⟶ A := {|
  fobj := fun x => fst ``x;
  fmap := fun _ _ f => fst ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

Program Instance comma_proj2 : Comma ⟶ B := {|
  fobj := fun x => snd ``x;
  fmap := fun _ _ f => snd ``f
|}.
Next Obligation. now intros ? ? ? ? [e0 e1]. Qed.
Next Obligation. now repeat intro. Qed.
Next Obligation. now repeat intro. Qed.

#[local] Obligation Tactic := cat_simpl.

Program Instance comma_proj_nat : S ◯ comma_proj1 ⟹ T ◯ comma_proj2.

End Comma.

Notation "S ↓ T" := (@Comma _ _ _ S T) (at level 90) : category_scope.

Theorem comma_proj_mor_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  x ≅ y → `1 x ≅[A ∏ B] `1 y.
Proof.
  destruct 1; simpl.
  isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - apply iso_to_from.
  - apply iso_from_to.
Defined.

Theorem comma_proj_com_iso A B C (S : A ⟶ C) (T : B ⟶ C) (x y : S ↓ T) :
  ∀ iso : x ≅ y,
    `2 x ≈ fmap[T] (snd `1 (from iso)) ∘ `2 y ∘ fmap[S] (fst `1 (to iso)).
Proof.
  intros.
  pose proof (iso_from_to iso); simpl in X.
  destruct (from iso), x0; simpl in *.
  rewrite <- e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst X).
  cat.
Qed.

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

(*
   本节说明函子、（余）极限、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Cocomma {A : Category} {B : Category} {C : Category}
  {S : A ⟶ C} {T : B ⟶ C} := @Comma (B^op) (A^op) (C^op) (T^op) (S^op).

Notation "S ↑ T" := (@Cocomma _ _ _ S T) (at level 90) : category_scope.
