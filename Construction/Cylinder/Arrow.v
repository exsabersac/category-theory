(** * Exercise II.4.8: the cylinder and arrow-category encodings agree *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Product.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Cylinder.
Require Import Category.Instance.Two.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Shapes.

Generalizable All Variables.

(*
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,

   本文件给出箭头范畴：对象为底范畴的态射，态射为交换方块。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The transpose and its arrow-category form *)

Definition Cyl_transpose {C B : Category} (F : C ∏ _2 ⟶ B) :
  C ⟶ [_2, B] :=
  @curry' Cat Cat_Cartesian Cat_Closed C _2 B F.

Definition Cyl_to_arrow {C B : Category} (F : C ∏ _2 ⟶ B) :
  C ⟶ @Arrow B :=
  Arrow_of_Fun ◯ Cyl_transpose F.

(** ** The two encodings classify the same transformation *)

Lemma cylinder_arrow_dom_nat {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_dom (Cyl_to_arrow (Cyl_functor τ))] f
      ≈ from (@iso_id B (S y)) ∘ fmap[S] f ∘ to (@iso_id B (S x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Lemma cylinder_arrow_cod_nat {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_cod (Cyl_to_arrow (Cyl_functor τ))] f
      ≈ from (@iso_id B (T y)) ∘ fmap[T] f ∘ to (@iso_id B (T x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Theorem cylinder_arrow_agree {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  @equiv _ (@ArrowTriple_Setoid C B)
    (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)))
    (S; (T; τ)).
Proof.
  exists (existT _ (fun c => iso_id) (cylinder_arrow_dom_nat τ)).
  exists (existT _ (fun c => iso_id) (cylinder_arrow_cod_nat τ)).
  intro c; simpl; cat.
Qed.

#[local] Existing Instance ArrowTriple_Setoid.

(* Naturality in the triple, in the setoid sense: equivalent triples
   are carried to equivalent extracted triples. *)
Corollary cylinder_arrow_natural {C B : Category}
          {S T S' T' : C ⟶ B} (τ : S ⟹ T) (τ' : S' ⟹ T')
          (E : ((S; (T; τ)) : ArrowTriple C B) ≈ (S'; (T'; τ'))) :
  (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)) : ArrowTriple C B)
    ≈ Arrow_extract (Cyl_to_arrow (Cyl_functor τ')).
Proof.
  transitivity ((S; (T; τ)) : ArrowTriple C B).
  - apply cylinder_arrow_agree.
  - transitivity ((S'; (T'; τ')) : ArrowTriple C B).
    + exact E.
    + symmetry; apply cylinder_arrow_agree.
Qed.

(* The theorem has content at small categories; the walking arrow
   itself is the donor's own precedent ([Two_Fun_Arrow_at_three]). *)
Example cylinder_arrow_agree_at_two {S T : _2 ⟶ _2} (τ : S ⟹ T) :
  @equiv _ (@ArrowTriple_Setoid _2 _2)
    (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)))
    (S; (T; τ)) :=
  cylinder_arrow_agree τ.
