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

(*
   本节说明 PreorderReflection 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ThinLift : PreorderReflect C ⟶ D :=
  @QuotientLift C (TotalRel C) _ D F (fun x y f g _ => HD _ _ _ _).

(** The factorization reproduces [F] on the nose. *)
Lemma ThinLift_proj {x y : C} (f : x ~> y) :
  fmap[ThinLift] (fmap[Reflect C] f) = fmap[F] f.
Proof. reflexivity. Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ThinLift_unique (G : PreorderReflect C ⟶ D)
      (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
      {x y : C} (f : x ~{PreorderReflect C}~> y) :
  hom_cast (Hobj x) (Hobj y) (fmap[G] f) ≈ fmap[ThinLift] f.
Proof. apply HD. Qed.

End Universal.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
