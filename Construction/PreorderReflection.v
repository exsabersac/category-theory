(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.

Generalizable All Variables.

(** ** The total hom-congruence *)

(** The relation relating ALL parallel morphisms.  Note this is a relation on
    each hom, not on objects: it never relates morphisms of different type. *)
Definition TotalRel (C : Category) : HomRel C := fun _ _ _ _ => True.

(** Every congruence field is immediate: the relation is constantly [True], so
    inclusion of [≈], symmetry, transitivity, and compatibility with
    composition all hold by [I].  (Reflexivity is derived, not a field.) *)
#[export] Instance TotalRel_Congruence (C : Category) :
  @HomCongruence C (TotalRel C).
Proof. constructor; intros; exact I. Defined.

(** ** The reflection *)

(** Same objects as [C]; parallel morphisms all identified. *)
Definition PreorderReflect (C : Category) : Category :=
  Quotient C (TotalRel C).

(** The defining property: the result is thin.  Thin is exactly "is a
    preorder" (Theory/Category.v), so this is the sense in which
    [PreorderReflect C] is a preorder rather than merely a category. *)
Lemma preorder_reflect_thin (C : Category) (x y : PreorderReflect C)
      (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(** Objects are untouched -- definitionally, not merely up to iso. *)
Lemma preorder_reflect_obj (C : Category) :
  obj[PreorderReflect C] = obj[C].
Proof. reflexivity. Qed.

(** The reflection map, identity on objects and on morphisms; only the
    hom-setoid coarsens. *)
Definition Reflect (C : Category) : C ⟶ PreorderReflect C :=
  @QuotientProj C (TotalRel C) _.

(** ** The universal property: the universal thin quotient *)

(** A category is THIN when any two parallel morphisms agree.  By
    Theory/Category.v that is exactly "is a preorder". *)
Definition Thin (D : Category) : Type :=
  ∀ (x y : D) (f g : x ~> y), f ≈ g.

(** [PreorderReflect C] is thin -- [preorder_reflect_thin] repackaged to the
    predicate, so it can be handed to [ThinLift]. *)
Definition PreorderReflect_Thin (C : Category) : Thin (PreorderReflect C) :=
  fun _ _ _ _ => I.

Section Universal.

Context {C D : Category}.
Context (HD : Thin D).
Context (F : C ⟶ D).

(** Every functor into a thin category factors through the reflection.  The
    hypothesis [QuotientLift] needs -- that [F] identifies related morphisms --
    is discharged by thinness of the target alone, with no condition on [F]. *)
Definition ThinLift : PreorderReflect C ⟶ D :=
  @QuotientLift C (TotalRel C) _ D F (fun x y f g _ => HD _ _ _ _).

(** The factorization reproduces [F] on the nose. *)
Lemma ThinLift_proj {x y : C} (f : x ~> y) :
  fmap[ThinLift] (fmap[Reflect C] f) = fmap[F] f.
Proof. reflexivity. Qed.

(** ...and it is the only such functor -- in a form STRONGER than the usual
    uniqueness clause, so read the hypotheses carefully.  No agreement between
    [G] and [F] after the reflection is assumed; object agreement [Hobj] alone
    (needed anyway for the statement to typecheck, since [hom_cast] transports
    along it) already pins [G] on every hom.  The proof is [apply HD] and uses
    nothing else, which is exactly the content: a thin target leaves no room
    for two functors with the same object action to differ, so a fortiori none
    for two different factorizations of [F]. *)
Lemma ThinLift_unique (G : PreorderReflect C ⟶ D)
      (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
      {x y : C} (f : x ~{PreorderReflect C}~> y) :
  hom_cast (Hobj x) (Hobj y) (fmap[G] f) ≈ fmap[ThinLift] f.
Proof. apply HD. Qed.

End Universal.

(** So [PreorderReflect C] is THE universal thin quotient of [C], not merely a
    quotient that happens to be thin.  This is what earns the word
    "reflection" here; the full reflective adjunction with the inclusion of
    preorders into [Cat] is stronger and is item 4 of #803. *)
