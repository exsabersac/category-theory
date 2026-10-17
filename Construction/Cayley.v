Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The Cayley representation of a category. *)

(*
   nLab: https://ncatlab.org/nlab/show/Yoneda+embedding
   Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem

   本文件给出 Cayley 表示相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the theorem的来源与用途

   Wikipedia: https://en.wikipedia.org/wiki/Cayley%27s_theorem
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Cayley.

Context {C : Category}.

(* An object is just an object of C; a morphism x ~> y is the underlying
   transformation of [Hom y,─] ⟹ [Hom x,─], determined by f _ id (Yoneda). *)
Program Instance Cayley : Category := {
  obj     := C;
  hom     := fun x y =>
    { f : ∀ r, (y ~> r) → (x ~> r)          (* the post-composition action  *)
    & Proper (forall_relation (fun _ => respectful equiv equiv)) f ∧
      ∀ (r : C) (k : y ~> r), f r k ≈ k ∘ f _ id };  (* naturality / Yoneda  *)
  homset  := fun x y => {| equiv := fun f g => ∀ r k, `1 f r k ≈ `1 g r k |};
  id      := fun _ => (fun _ => Datatypes.id; _);
  compose := fun x y z f g  => (fun r k => `1 g r (`1 f r k); _)
}.
Next Obligation.
  equivalence.
  now rewrite X, X0.
Qed.
Next Obligation.
  split.
  - proper.
  - intros; cat.
Qed.
Next Obligation.
  split.
  - proper.
    apply p.
    apply p0.
    apply X.
  - intros.
    symmetry.
    rewrite e.
    rewrite comp_assoc.
    rewrite <- e0.
    rewrite <- e.
    reflexivity.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H, H0.
  rewrite X.
  comp_left.
  apply X0.
Qed.

(* The embedding: f : x ~> y sent post-复合 action
 k ↦ k ∘ f, corepresentable transformation [Hom y,─] ⟹ [Hom x,─]. （已译） *)
Program Instance To_Cayley : C ⟶ Cayley := {
  fobj := fun x => x;
  fmap := fun _ _ f => (fun _ k => k ∘ f; _);
}.
Next Obligation.
  proper.
  proper.
Defined.

(* The retraction: read Cayley-态射 f back C-态射 f _ id,
 recovering original Yoneda law. From_Cayley ∘ To_Cayley = Id. （已译） *)
Program Instance From_Cayley : Cayley ⟶ C := {
  fobj := fun x => x;
  fmap := fun _ y f => `1 f y (@id C y);
}.

Context `{Cayley}.

(* No matter how we associate mapped 态射, 函子 back from
 Cayley yields them left-associated. （已译） *)

Lemma Cayley_Right (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (∀ a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (fmap[To_Cayley] f ∘ (fmap[To_Cayley] g
                                          ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Lemma Cayley_Left (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (∀ a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (((fmap[To_Cayley] f ∘ fmap[To_Cayley] g)
                      ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

(*
   本节说明Yoneda、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Instance Cayley_Cartesian `{CA : @Cartesian C} : @Cartesian Cayley := {
  product_obj := @product_obj C CA;
  fork := fun x y z f g =>
    let f' := to (Covariant_Yoneda_Embedding C x y) (_ f) in
    let g' := to (Covariant_Yoneda_Embedding C x z) (_ g) in
    _ f' g';
  exl := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exl C CA x y) in
    _ f';
  exr := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exr C CA x y) in
    _ f';
}.
Next Obligation.
  construct.
  - construct.
    + apply f.
      exact X.
    + proper.
      rewrite e1.
      rewrite X.
      rewrite <- e1.
      reflexivity.
  - simpl.
    rewrite e1.
    rewrite comp_assoc.
    rewrite <- e1.
    reflexivity.
  - simpl.
    rewrite e1.
    rewrite <- comp_assoc.
    rewrite <- e1.
    reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + apply g.
      exact X.
    + proper.
      rewrite e0.
      rewrite X.
      rewrite <- e0.
      reflexivity.
  - simpl.
    rewrite e0.
    rewrite comp_assoc.
    rewrite <- e0.
    reflexivity.
  - simpl.
    rewrite e0.
    rewrite <- comp_assoc.
    rewrite <- e0.
    reflexivity.
Defined.
Next Obligation.
  exists (fun r h => h ∘ x0 △ x1).
  split.
  - proper.
  - intros; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
  - proper.
    now apply proper_morphism.
  - intros.
    rewrite naturality.
    apply proper_morphism; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
  - proper.
    now apply proper_morphism.
  - intros.
    rewrite naturality.
    apply proper_morphism; cat.
Defined.
Next Obligation.
  proper; simpl in *.
  comp_left.
  apply fork_respects.
  - apply X.
  - apply X0.
Qed.
Next Obligation.
  proper; simpl in *.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    rewrite <- e1.
    reflexivity.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exr_fork.
    rewrite <- e0.
    reflexivity.
  - rewrite <- X, <- H0.
    rewrite e.
    comp_left.
    rewrite (e _ (_ ∘ exl)).
    rewrite (e _ (_ ∘ exr)).
    cat.
    rewrite fork_comp.
    rewrite fork_exl_exr.
    cat.
Qed.

End Cayley.

Require Import Category.Functor.Structure.Cartesian.

#[export]
Program Instance To_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ To_Cayley _ Cayley_Cartesian.

#[export]
Program Instance From_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ From_Cayley Cayley_Cartesian _.
