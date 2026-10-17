Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.

Generalizable All Variables.

(** * Groupoids: the property, and the vertex-group structure *)

(*
   nLab:      https://ncatlab.org/nlab/show/vertex+group
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
   Book:      Riehl, "Category Theory in Context", Definition 1.1.12 and
   Book:      Fong, Spivak, "Seven Sketches in Compositionality", CUP 2019,

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/groupoid
   nLab:  https://ncatlab.org/nlab/show/fundamental+groupoid
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of the
   Paper: Weinstein, "Groupoids: Unifying Internal and External Symmetry",

   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The predicate *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsGroupoid (C : Category) : Type :=
  ∀ (x y : C) (f : x ~> y), IsIsomorphism f.

Section Groupoid.

Context {C : Category}.
Context (G : IsGroupoid C).

(* The inverse of f, extracted from the groupoid structure. *)
Definition ginv {x y : C} (f : x ~> y) : y ~> x :=
  two_sided_inverse (IsIsomorphism := G x y f).

(* The two inverse laws, in the orientation [IsIsomorphism] states them. *)
Lemma ginv_right {x y : C} (f : x ~> y) : f ∘ ginv f ≈ id.
Proof. exact (is_right_inverse (IsIsomorphism := G x y f)). Qed.

Lemma ginv_left {x y : C} (f : x ~> y) : ginv f ∘ f ≈ id.
Proof. exact (is_left_inverse (IsIsomorphism := G x y f)). Qed.

(*
   本节说明同构、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ginv_unique_r {x y : C} (f : x ~> y) (g : y ~> x) :
  f ∘ g ≈ id → ginv f ≈ g.
Proof.
  intro H.
  symmetry.
  exact (comp_inverse_unique f g (ginv f) H (ginv_left f)).
Qed.

Lemma ginv_unique_l {x y : C} (f : x ~> y) (g : y ~> x) :
  g ∘ f ≈ id → ginv f ≈ g.
Proof.
  intro H.
  exact (comp_inverse_unique f (ginv f) g (ginv_right f) H).
Qed.

(* Inversion respects `≈`.  Like [grp_inv_respects] in Construction/Deloop.v
   this is derived from uniqueness of inverses, not required as data. *)
#[export] Instance ginv_respects {x y : C} :
  Proper (equiv ==> equiv) (@ginv x y).
Proof.
  intros f g Hfg.
  apply ginv_unique_r.
  rewrite Hfg.
  apply ginv_right.
Qed.

Lemma ginv_involutive {x y : C} (f : x ~> y) : ginv (ginv f) ≈ f.
Proof. apply ginv_unique_l, ginv_right. Qed.

Lemma ginv_id {x : C} : ginv (id[x]) ≈ id.
Proof. apply ginv_unique_r; cat. Qed.

(* Inverses of a composite compose in the opposite order. *)
Lemma ginv_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
  ginv (f ∘ g) ≈ ginv g ∘ ginv f.
Proof.
  apply ginv_unique_r.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g).
  rewrite ginv_right, id_left.
  apply ginv_right.
Qed.

(* An arrow of a groupoid, packaged as an object-level isomorphism.  This is
   the bridge from the predicate reading back to `≅`. *)
Definition giso {x y : C} (f : x ~> y) : x ≅ y := IsIsoToIso f (G x y f).

(* Moving an inverse across an equation, the two cancellation rules a
   groupoid computation needs: from g ∘ f ≈ h one reads off g ≈ h ∘ f⁻¹ and
   f ≈ g⁻¹ ∘ h.  Each is one rewrite by [ginv_right] or [ginv_left] after
   substituting h. *)
Lemma ginv_move_r {x y z : C} (f : x ~> y) (g : y ~> z) (h : x ~> z) :
  g ∘ f ≈ h → g ≈ h ∘ ginv f.
Proof.
  intro H.
  rewrite <- H, <- comp_assoc, ginv_right.
  now rewrite id_right.
Qed.

Lemma ginv_move_l {x y z : C} (f : x ~> y) (g : y ~> z) (h : x ~> z) :
  g ∘ f ≈ h → f ≈ ginv g ∘ h.
Proof.
  intro H.
  rewrite <- H, comp_assoc, ginv_left.
  now rewrite id_left.
Qed.

End Groupoid.

Arguments ginv {C} G {x y} f.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ginv_choice_irrelevant {C : Category} (G G' : IsGroupoid C)
  {x y : C} (f : x ~> y) : ginv G f ≈ ginv G' f.
Proof. apply ginv_unique_r, ginv_right. Qed.

(** ** The core of a category is a groupoid *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition core_is_groupoid (C : Category) : IsGroupoid (Groupoid C).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (Groupoid C) x y f (iso_sym f) _ _).
  - apply iso_sym_right_inverse.
  - apply iso_sym_left_inverse.
Defined.

(** ** Duality *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsGroupoid_op {C : Category} (G : IsGroupoid C) : IsGroupoid (C^op).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (C^op) x y f (ginv G f) _ _).
  - exact (ginv_left G f).
  - exact (ginv_right G f).
Defined.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ginv_op_eq {C : Category} (G : IsGroupoid C) {x y : C}
  (f : y ~{C}~> x) : ginv (IsGroupoid_op G) f = ginv G f := eq_refl.

(** ** Groups as one-object groupoids *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record MonInverses (M : MonObject) := {
  minv : carrier M → carrier M;

  minv_l : ∀ a, mon_op (minv a) a ≈ mon_unit;
  minv_r : ∀ a, mon_op a (minv a) ≈ mon_unit
}.

Arguments minv {M} _ _.
Arguments minv_l {M} _ _.
Arguments minv_r {M} _ _.

(* [MonInverses M] and "M is the underlying monoid of a [GrpObject]" are the
   same data, repackaged; both round trips hold. *)
Definition GrpObject_of {M : MonObject} (I : MonInverses M) : GrpObject := {|
  grp_monoid := M;
  grp_inv    := minv I;
  grp_inv_l  := minv_l I;
  grp_inv_r  := minv_r I
|}.

Definition MonInverses_of (G : GrpObject) : MonInverses (grp_monoid G) := {|
  minv   := grp_inv (g:=G);
  minv_l := grp_inv_l (g:=G);
  minv_r := grp_inv_r (g:=G)
|}.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example GrpObject_of_MonInverses_of (G : GrpObject) :
  GrpObject_of (MonInverses_of G) = G := eq_refl.

Example MonInverses_of_GrpObject_of (M : MonObject) (I : MonInverses M) :
  MonInverses_of (GrpObject_of I) = I := eq_refl.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop_IsGroupoid (G : GrpObject) : IsGroupoid (Deloop G) :=
  fun x y f => Deloop_group_invertible G x y f.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop_MonInverses (M : MonObject) (H : IsGroupoid (Deloop M)) :
  MonInverses M := {|
  minv   := fun a => two_sided_inverse (IsIsomorphism := H ttt ttt a);
  minv_l := fun a => is_left_inverse  (IsIsomorphism := H ttt ttt a);
  minv_r := fun a => is_right_inverse (IsIsomorphism := H ttt ttt a)
|}.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem deloop_groupoid_iff (M : MonObject) :
  MonInverses M ↔ IsGroupoid (Deloop M).
Proof.
  split.
  - intro I.
    exact (Deloop_IsGroupoid (GrpObject_of I)).
  - intro H.
    exact (Deloop_MonInverses M H).
Defined.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Deloop_one_object (M : MonObject) : obj[Deloop M] = poly_unit := eq_refl.

(** ** The vertex group *)

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition vertex_group {C : Category} (G : IsGroupoid C) (x : C) : GrpObject := {|
  grp_monoid := hom_monoid C x;
  grp_inv    := fun f => ginv G f;
  grp_inv_l  := fun f => ginv_left G f;
  grp_inv_r  := fun f => ginv_right G f
|}.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example vertex_group_Deloop_monoid (G : GrpObject) :
  grp_monoid (vertex_group (Deloop_IsGroupoid G) ttt) = grp_monoid G := eq_refl.

Example vertex_group_Deloop_inv (G : GrpObject) :
  @grp_inv (vertex_group (Deloop_IsGroupoid G) ttt) = @grp_inv G := eq_refl.

(** ** Monoid homomorphisms, and conjugation *)

(*
   本节说明函子、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record MonHom (M N : MonObject) := {
  mon_map :> carrier M → carrier N;

  mon_map_respects : Proper (equiv ==> equiv) mon_map;

  mon_map_unit : mon_map mon_unit ≈ mon_unit;
  mon_map_op : ∀ a b, mon_map (mon_op a b) ≈ mon_op (mon_map a) (mon_map b)
}.

Arguments mon_map {M N} _ _.
Arguments mon_map_respects {M N} _.
Arguments mon_map_unit {M N} _.
Arguments mon_map_op {M N} _ _ _.

#[export] Existing Instance mon_map_respects.

Record MonIso (M N : MonObject) := {
  moniso_to : MonHom M N;
  moniso_from : MonHom N M;

  moniso_to_from : ∀ b, moniso_to (moniso_from b) ≈ b;
  moniso_from_to : ∀ a, moniso_from (moniso_to a) ≈ a
}.

Arguments moniso_to {M N} _.
Arguments moniso_from {M N} _.
Arguments moniso_to_from {M N} _ _.
Arguments moniso_from_to {M N} _ _.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma MonHom_grp_inv (G H : GrpObject) (φ : MonHom G H) (a : carrier G) :
  φ (grp_inv a) ≈ grp_inv (φ a).
Proof.
  apply (mon_inverse_unique H (φ a) (φ (grp_inv a)) (grp_inv (φ a))).
  - rewrite <- mon_map_op.
    rewrite grp_inv_l.
    apply mon_map_unit.
  - apply grp_inv_r.
Qed.

Section Conjugation.

Context {C : Category}.
Context (G : IsGroupoid C).
Context {x x' : C}.
Context (f : x ~> x').

(* Conjugation by f, as a map hom(x, x) → hom(x', x'). *)
Definition conjugate (a : x ~> x) : x' ~> x' := f ∘ a ∘ ginv G f.

#[local] Instance conjugate_respects : Proper (equiv ==> equiv) conjugate.
Proof. proper; unfold conjugate; now rewrites. Qed.

Lemma conjugate_id : conjugate id ≈ id.
Proof.
  unfold conjugate.
  rewrite id_right.
  apply ginv_right.
Qed.

Lemma conjugate_comp (a b : x ~> x) :
  conjugate (a ∘ b) ≈ conjugate a ∘ conjugate b.
Proof.
  unfold conjugate.
  rewrite <- !comp_assoc.
  (* on the right-hand side the inner  f⁻¹ ∘ f  cancels *)
  rewrite (comp_assoc (ginv G f) f).
  rewrite ginv_left, id_left.
  reflexivity.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition conjugation : MonHom (vertex_group G x) (vertex_group G x') :=
  @Build_MonHom (grp_monoid (vertex_group G x)) (grp_monoid (vertex_group G x'))
    conjugate conjugate_respects conjugate_id conjugate_comp.

End Conjugation.

Arguments conjugate {C} G {x x'} f a.
Arguments conjugation {C} G {x x'} f.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition conjugation_iso {C : Category} (G : IsGroupoid C) {x x' : C}
  (f : x ~> x') : MonIso (vertex_group G x) (vertex_group G x').
Proof.
  refine {| moniso_to   := conjugation G f
          ; moniso_from := conjugation G (ginv G f) |}.
  - (* conjugation by f, after conjugation by f⁻¹ *)
    intro b.
    unfold conjugation, conjugate; simpl.
    rewrite ginv_involutive.
    rewrite <- !comp_assoc.
    rewrite ginv_right, id_right.
    rewrite comp_assoc, ginv_right.
    apply id_left.
  - (* and the other way round *)
    intro a.
    unfold conjugation, conjugate; simpl.
    rewrite ginv_involutive.
    rewrite <- !comp_assoc.
    rewrite ginv_left, id_right.
    rewrite comp_assoc, ginv_left.
    apply id_left.
Defined.

(** ** The two witnesses of Exercise 3.32 *)

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma deloop_nat_iso_is_zero (n : carrier Nat_Plus)
  (H : @IsIsomorphism (Deloop Nat_Plus) ttt ttt n) : n = 0%nat.
Proof.
  pose proof (is_right_inverse (IsIsomorphism := H)) as Hr.
  simpl in Hr.                          (* Hr : (n + two_sided_inverse)%nat = 0%nat *)
  now destruct n.
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem deloop_nat_one_not_invertible :
  @IsIsomorphism (Deloop Nat_Plus) ttt ttt 1%nat → False.
Proof.
  intro H.
  pose proof (deloop_nat_iso_is_zero 1%nat H) as Heq.
  discriminate Heq.
Qed.

Theorem deloop_nat_not_groupoid : IsGroupoid (Deloop Nat_Plus) → False.
Proof.
  intro H.
  exact (deloop_nat_one_not_invertible (H ttt ttt 1%nat)).
Qed.

(* Equivalently, through the biconditional: (ℕ, +) has no inverse operation. *)
Corollary nat_plus_no_inverses : MonInverses Nat_Plus → False.
Proof.
  intro I.
  exact (deloop_nat_not_groupoid (fst (deloop_groupoid_iff Nat_Plus) I)).
Qed.

(* The other witness: the delooping of Z/2 IS a groupoid, because Z/2 is a
   group.  Construction/Deloop.v's [Bool_Xor_Grp] is that group. *)
Definition deloop_bool_groupoid : IsGroupoid (Deloop Bool_Xor_Grp) :=
  Deloop_IsGroupoid Bool_Xor_Grp.

(* And its vertex group is Z/2 back again, on the nose in both data fields —
   the round trip of [vertex_group_Deloop_monoid]/[vertex_group_Deloop_inv]
   at a concrete group. *)
Example vertex_group_bool_inv :
  @grp_inv (vertex_group deloop_bool_groupoid ttt) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(** ** A group whose inversion is not the identity *)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

Inductive Z3 : Set := Z3_0 | Z3_1 | Z3_2.

Definition Z3_add (a b : Z3) : Z3 :=
  match a, b with
  | Z3_0, b    => b
  | a,    Z3_0 => a
  | Z3_1, Z3_1 => Z3_2
  | Z3_1, Z3_2 => Z3_0
  | Z3_2, Z3_1 => Z3_0
  | Z3_2, Z3_2 => Z3_1
  end.

Definition Z3_neg (a : Z3) : Z3 :=
  match a with
  | Z3_0 => Z3_0
  | Z3_1 => Z3_2
  | Z3_2 => Z3_1
  end.

Program Definition Z3_Mon : MonObject := {|
  mon_setoid := {| carrier := Z3
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := Z3_0;
  mon_op     := Z3_add
|}.
Next Obligation.
  intros a b c; now destruct a, b, c.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

Program Definition Z3_Grp : GrpObject := {|
  grp_monoid := Z3_Mon;
  grp_inv    := Z3_neg
|}.
Next Obligation.
  intros a; now destruct a.
Qed.
Next Obligation.
  intros a; now destruct a.
Qed.

Definition deloop_Z3_groupoid : IsGroupoid (Deloop Z3_Grp) :=
  Deloop_IsGroupoid Z3_Grp.

(* Inversion in Z/3 really does move an element.  The [=] is Leibniz equality
   on [Z3], which is exactly the `≈` of [Z3_Mon]'s carrier setoid, so nothing
   weaker is being claimed. *)
Example Z3_inv_1 : grp_inv (g:=Z3_Grp) Z3_1 = Z3_2 := eq_refl.

Lemma Z3_inv_moves : grp_inv (g:=Z3_Grp) Z3_1 <> Z3_1.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------------ *)
(** ** A nonabelian group, and a conjugation that genuinely moves an element *)

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive S3 : Set :=
  | S3_e | S3_r | S3_rr | S3_a | S3_b | S3_c.

(* r is a 3-cycle, rr its square; a, b, c are the three transpositions. *)
Definition S3_mul (x y : S3) : S3 :=
  match x, y with
  | S3_e,  y    => y
  | x,     S3_e => x
  | S3_r,  S3_r  => S3_rr | S3_r,  S3_rr => S3_e
  | S3_rr, S3_r  => S3_e  | S3_rr, S3_rr => S3_r
  | S3_r,  S3_a  => S3_b  | S3_r,  S3_b  => S3_c  | S3_r,  S3_c  => S3_a
  | S3_rr, S3_a  => S3_c  | S3_rr, S3_b  => S3_a  | S3_rr, S3_c  => S3_b
  | S3_a,  S3_r  => S3_c  | S3_b,  S3_r  => S3_a  | S3_c,  S3_r  => S3_b
  | S3_a,  S3_rr => S3_b  | S3_b,  S3_rr => S3_c  | S3_c,  S3_rr => S3_a
  | S3_a,  S3_a  => S3_e  | S3_b,  S3_b  => S3_e  | S3_c,  S3_c  => S3_e
  | S3_a,  S3_b  => S3_rr | S3_b,  S3_c  => S3_rr | S3_c,  S3_a  => S3_rr
  | S3_a,  S3_c  => S3_r  | S3_b,  S3_a  => S3_r  | S3_c,  S3_b  => S3_r
  end.

Definition S3_inv (x : S3) : S3 :=
  match x with
  | S3_e => S3_e | S3_r => S3_rr | S3_rr => S3_r
  | S3_a => S3_a | S3_b => S3_b  | S3_c  => S3_c
  end.

Program Definition S3_Mon : MonObject := {|
  mon_setoid := {| carrier := S3
                 ; is_setoid := {| equiv := eq
                                 ; setoid_equiv := eq_equivalence |} |};
  mon_unit   := S3_e;
  mon_op     := S3_mul
|}.
Next Obligation. intros a b c; now destruct a, b, c. Qed.
Next Obligation. intros a; now destruct a. Qed.
Next Obligation. intros a; now destruct a. Qed.

Program Definition S3_Grp : GrpObject := {|
  grp_monoid := S3_Mon;
  grp_inv    := S3_inv
|}.
Next Obligation. intros a; now destruct a. Qed.
Next Obligation. intros a; now destruct a. Qed.

(* It is genuinely nonabelian — the two three-cycles conjugate the
   transpositions around, which is exactly what Z/2 and Z/3 cannot do. *)
Theorem S3_not_abelian : S3_mul S3_r S3_a = S3_mul S3_a S3_r → False.
Proof. simpl; discriminate. Qed.

Definition deloop_S3_groupoid : IsGroupoid (Deloop S3_Grp) :=
  Deloop_IsGroupoid S3_Grp.

(*
   本节说明 Groupoid 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example S3_conjugation_not_identity :
  conjugate deloop_S3_groupoid (x:=ttt) (x':=ttt) S3_r S3_a = S3_a → False.
Proof. simpl; discriminate. Qed.
