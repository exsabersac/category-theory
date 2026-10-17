Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(** * A groupoid is isomorphic to its opposite *)

(*
   nLab:      https://ncatlab.org/nlab/show/opposite+category
   Book:      Riehl, "Category Theory in Context", Example 1.3.14, clauses

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Why inversion is a functor at all, and what it is used for

   nLab:  https://ncatlab.org/nlab/show/opposite+category
   Book:  Riehl, "Category Theory in Context", Example 1.2.2(iii)

   Inversion reverses composition: (f ∘ g)⁻¹ ≈ g⁻¹ ∘ f⁻¹, which is
   [ginv_comp] in Structure/Groupoid.v.  Taking the codomain to be C^op is
   what makes that law the functoriality law rather than an obstruction to
   it — composition in C^op is composition in C with its arguments swapped,
   so the [fmap_comp] obligation below is discharged by [ginv_comp] verbatim,
   with no reordering step.  This is the standard reason a contravariant
   construction is presented as a covariant functor out of (or into) an
   opposite category.  (For a groupoid whose composition happens to be
   commutative — the delooping of an abelian group, say — the two orders
   agree and inversion is an endofunctor as well; nothing below relies on
   either case.)

   Its classical use, which is Riehl's clause (i), is that a right action of
   a group G — a functor (B G)^op ⟶ C — becomes a left action by
   precomposition with the inversion isomorphism.  Group theory states the
   same fact elementwise: x · g becomes g⁻¹ · x.  Because the composite of
   inversion with itself is the identity up to `≈`, the translation is
   reversible, which is what makes "right action" and "left action" two
   presentations of one notion rather than two notions.

   Construction/Deloop/Opposite.v handles a neighbouring statement that
   should not be confused with this one: there [Deloop_op] compares (B M)^op
   with B (M^op) for an arbitrary MONOID M — no inverses are involved, and the
   opposite monoid genuinely differs from M when M is not commutative.  The
   isomorphism here is available only for groupoids, and identifies C with
   C^op rather than with the delooping of anything. *)

(** ** The functor *)

(* Identity on objects, and f ↦ f⁻¹ on morphisms.  Each functor law is a
   [ginv] law from Structure/Groupoid.v: respectfulness is [ginv_respects],
   preservation of identities is [ginv_id], and preservation of composition
   is [ginv_comp] — whose right-hand side g⁻¹ ∘ f⁻¹ IS composition in C^op,
   with no reordering needed. *)
Program Definition Inversion {C : Category} (G : IsGroupoid C) : C ⟶ C^op := {|
  fobj := fun x => x;
  fmap := fun x y f => ginv G f
|}.
Next Obligation. now apply ginv_respects. Qed.
Next Obligation. now apply ginv_id. Qed.
Next Obligation. now apply ginv_comp. Qed.

(* The functor is the identity on objects, literally: [fobj] is [fun x => x],
   so this [=] is an equality of objects holding by [eq_refl], not a claim
   about morphisms. *)
Example Inversion_identity_on_objects {C : Category} (G : IsGroupoid C)
  (x : C) : fobj[Inversion G] x = x := eq_refl.

(* The same functor for C^op, which is a groupoid by [IsGroupoid_op].  Its
   codomain is (C^op)^op, and Construction/Opposite.v makes that C by
   [reflexivity] — the involution is definitional there, so no transport is
   needed to read this as a functor C^op ⟶ C. *)
Definition Inversion_op {C : Category} (G : IsGroupoid C) : C^op ⟶ C :=
  Inversion (IsGroupoid_op G).

(** ** The isomorphism *)

(* Riehl, Example 1.3.14(ii).  Both composites are the identity on objects on
   the nose, so the object-equality component is [eq_refl] and the transports
   in [Functor_StrictEq_Setoid] disappear; what remains in each case is
   (f⁻¹)⁻¹ ≈ f, which is [ginv_involutive]. *)
Program Definition Inversion_iso {C : Category} (G : IsGroupoid C) :
  C ≅[StrictCat] C^op := {|
  to   := Inversion G;
  from := Inversion_op G
|}.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f.
  exact (ginv_involutive G f).
Qed.
Next Obligation.
  exists (fun x => eq_refl).
  intros x y f.
  exact (ginv_involutive G f).
Qed.

(* The weaker [Cat]-level statement, obtained by transporting along the
   identity-on-objects comparison functor [StrictCat_to_Cat]
   (Instance/StrictCat/ToCat.v) — a functor carries isomorphisms to
   isomorphisms ([fobj_iso], Theory/Functor.v).  Per this file's header this
   is an EQUIVALENCE of categories, not an isomorphism of them; it is
   recorded because it is the form most consumers in the library take. *)
Definition Inversion_Cat_iso {C : Category} (G : IsGroupoid C) :
  C ≅[Cat] C^op :=
  fobj_iso StrictCat_to_Cat C (C^op) (Inversion_iso G).

(** ** Instances *)

(* Riehl's clause (i): the delooping of a group is isomorphic to its
   opposite, by inversion.  This is the one-object case of the statement
   above, and the device by which a right action of G — a functor
   (B G)^op ⟶ C — is presented as a left action B G ⟶ C, by precomposing
   with this isomorphism; elementwise, x · g becomes g⁻¹ · x. *)
Definition Deloop_Inversion_iso (G : GrpObject) :
  Deloop G ≅[StrictCat] (Deloop G)^op :=
  Inversion_iso (Deloop_IsGroupoid G).

(* At Z/2, concretely — so the statement is inhabited at an actual group and
   not only parametrically.

   DEGENERATE, and flagged as such: every element of Z/2 is its own inverse,
   so the morphism map of [Inversion] is the identity function here and this
   instance exercises nothing about inversion.  The next one does. *)
Definition Bool_Inversion_iso :
  Deloop Bool_Xor_Grp ≅[StrictCat] (Deloop Bool_Xor_Grp)^op :=
  Deloop_Inversion_iso Bool_Xor_Grp.

(* Z/3 is the smallest group for which inversion moves an element, so it is
   the smallest instance at which the functor is not the identity on
   morphisms.  Structure/Groupoid.v supplies the group. *)
Definition Z3_Inversion_iso :
  Deloop Z3_Grp ≅[StrictCat] (Deloop Z3_Grp)^op :=
  Deloop_Inversion_iso Z3_Grp.

(* The morphism map really moves the arrow [Z3_1].  Both [=]s are Leibniz
   equality on [Z3], which is exactly the `≈` of that carrier setoid, so
   nothing weaker is being claimed. *)
Example Z3_inversion_nontrivial :
  @fmap _ _ (Inversion deloop_Z3_groupoid) ttt ttt Z3_1 = Z3_2 := eq_refl.

Lemma Z3_inversion_not_identity :
  @fmap _ _ (Inversion deloop_Z3_groupoid) ttt ttt Z3_1 <> Z3_1.
Proof. discriminate. Qed.

(* And the core of ANY category is isomorphic to its opposite, since the core
   is always a groupoid ([core_is_groupoid]).  This holds for every C
   whatever, so the family of instances is as large as the library's supply
   of categories. *)
Definition core_Inversion_iso (C : Category) :
  Groupoid C ≅[StrictCat] (Groupoid C)^op :=
  Inversion_iso (core_is_groupoid C).
