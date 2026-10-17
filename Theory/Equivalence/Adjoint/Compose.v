Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+equivalence
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   本文件给出复合相关构造（伴随/函子/单子等的复合）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section IsoCalculus.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes o h p.
Context {X : Category@{o h p}}.

(* The 恒等 invertible, predicate form. （已译） *)
Program Definition IsIso_id {x : X} : IsIsomorphism (id[x]) := {|
  two_sided_inverse := id
|}.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsIso_along {x y : X} {f g : x ~> y}
  (H : f ≈ g) (Hg : IsIsomorphism g) : IsIsomorphism f :=
  {| two_sided_inverse := @two_sided_inverse X x y g Hg
   ; is_right_inverse :=
       transitivity (compose_respects _ _ H _ _ (reflexivity _))
                    (@is_right_inverse X x y g Hg)
   ; is_left_inverse :=
       transitivity (compose_respects _ _ (reflexivity _) _ _ H)
                    (@is_left_inverse X x y g Hg) |}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition IsIso_comp {x y z : X} {f : y ~> z} {g : x ~> y}
  (Hf : IsIsomorphism f) (Hg : IsIsomorphism g) : IsIsomorphism (f ∘ g) := {|
  two_sided_inverse := @two_sided_inverse X x y g Hg
                         ∘ @two_sided_inverse X y z f Hf
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g).
  rewrite (@is_right_inverse X x y g Hg), id_left.
  apply is_right_inverse.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (@two_sided_inverse X y z f Hf)).
  rewrite (@is_left_inverse X y z f Hf), id_left.
  apply is_left_inverse.
Defined.

End IsoCalculus.

(* A functor carries invertible morphisms to invertible morphisms.  This
   restates [fmap_IsIsomorphism] (Construction/Reflective/Idempotent.v);
   see the header for why it is restated rather than required. *)
Program Definition IsIso_fmap@{xo xh xp yo yh yp +}
  {X : Category@{xo xh xp}} {Y : Category@{yo yh yp}} (G : X ⟶ Y) {x y : X}
  {f : x ~> y} (Hf : IsIsomorphism f) : IsIsomorphism (fmap[G] f) := {|
  two_sided_inverse := fmap[G] (@two_sided_inverse X x y f Hf)
|}.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite (@is_right_inverse X x y f Hf).
  apply fmap_id.
Defined.
Next Obligation.
  rewrite <- fmap_comp.
  rewrite (@is_left_inverse X x y f Hf).
  apply fmap_id.
Defined.

(* * ** The 复合 two adjoint equivalences （已译） *)

Section Compose.

Context {C D E : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context {F' : D ⟶ E} {U' : E ⟶ D}.
Context (A : AdjointEquivalence F U).
Context (B : AdjointEquivalence F' U').

(* The underlying 伴随 复合: [Adjunction_Compose]
 (Adjunction/Compose.v) two underlying 伴随. （已译） *)
Definition adjoint_equivalence_compose_adj : (F' ◯ F) ⊣ (U ◯ U') :=
  Adjunction_Compose (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B).

(* The 复合's unit invertible: transport along Mac Lane's
 whiskering formula, then compose U-image B's unit 同构
 A's own. （已译） *)
Definition adjoint_equivalence_compose_unit_iso (x : C) :
  IsIsomorphism (@unit _ _ _ _ adjoint_equivalence_compose_adj x) :=
  IsIso_along
    (@Adjunction_Compose_unit _ _ _ _ _ _ _
       (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) x)
    (IsIso_comp (IsIso_fmap U (@adj_equiv_unit_iso _ _ _ _ B (F x)))
                (@adj_equiv_unit_iso _ _ _ _ A x)).

(* Dually for the counit. *)
Definition adjoint_equivalence_compose_counit_iso (y : E) :
  IsIsomorphism (@counit _ _ _ _ adjoint_equivalence_compose_adj y) :=
  IsIso_along
    (@Adjunction_Compose_counit _ _ _ _ _ _ _
       (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) y)
    (IsIso_comp (@adj_equiv_counit_iso _ _ _ _ B y)
                (IsIso_fmap F' (@adj_equiv_counit_iso _ _ _ _ A (U' y)))).

(* Mac Lane SIV.4 Exercise 2(b): adjoint equivalences compose. *)
Definition AdjointEquivalence_Compose :
  AdjointEquivalence (F' ◯ F) (U ◯ U') :=
  @Build_AdjointEquivalence C E (F' ◯ F) (U ◯ U')
    adjoint_equivalence_compose_adj
    adjoint_equivalence_compose_unit_iso
    adjoint_equivalence_compose_counit_iso.

(* 相关说明。 （已译） *)

Example AdjointEquivalence_Compose_adjunction :
  @adj_equivalence _ _ _ _ AdjointEquivalence_Compose
    = Adjunction_Compose (@adj_equivalence _ _ _ _ A)
                         (@adj_equivalence _ _ _ _ B) := eq_refl.

Example AdjointEquivalence_Compose_unit_clause (x : C) :
  @adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Compose x
    = adjoint_equivalence_compose_unit_iso x := eq_refl.

Example AdjointEquivalence_Compose_counit_clause (y : E) :
  @adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Compose y
    = adjoint_equivalence_compose_counit_iso y := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AdjointEquivalence_Compose_unit (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) x
    ≈ fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  @Adjunction_Compose_unit _ _ _ _ _ _ _
    (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) x.

Definition AdjointEquivalence_Compose_counit (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) y
    ≈ @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) :=
  @Adjunction_Compose_counit _ _ _ _ _ _ _
    (@adj_equivalence _ _ _ _ A) (@adj_equivalence _ _ _ _ B) y.

(* The strict form: 复合's unit IS A's forward transpose B's
 unit, 复合's counit IS B's inverse transpose A's
 counit. Both conversion. （已译） *)
Example AdjointEquivalence_Compose_unit_transpose (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) x
    = to (@adj _ _ _ _ (@adj_equivalence _ _ _ _ A) x (U' (F' (F x))))
         (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x)) := eq_refl.

Example AdjointEquivalence_Compose_counit_transpose (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Compose) y
    = from (@adj _ _ _ _ (@adj_equivalence _ _ _ _ B) (F (U (U' y))) y)
           (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) := eq_refl.

(* 相关说明。 （已译） *)
Example AdjointEquivalence_Compose_unit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Compose x)
    = @two_sided_inverse _ _ _ _ (@adj_equiv_unit_iso _ _ _ _ A x)
        ∘ fmap[U] (@two_sided_inverse _ _ _ _
                     (@adj_equiv_unit_iso _ _ _ _ B (F x))) := eq_refl.

Example AdjointEquivalence_Compose_counit_inverse (y : E) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Compose y)
    = fmap[F'] (@two_sided_inverse _ _ _ _
                  (@adj_equiv_counit_iso _ _ _ _ A (U' y)))
        ∘ @two_sided_inverse _ _ _ _
            (@adj_equiv_counit_iso _ _ _ _ B y) := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AdjointEquivalence_Compose_via_equivalence :
  AdjointEquivalence (F' ◯ F) (U ◯ U') :=
  Equivalence_to_AdjointEquivalence
    (EquivalenceOfCategories_Compose
       (AdjointEquivalence_to_Equivalence A)
       (AdjointEquivalence_to_Equivalence B)).

(* Its quasi-inverse 复合 two right adjoints the
 nose, what makes type above right one. （已译） *)
Example AdjointEquivalence_Compose_via_quasi_inverse :
  @quasi_inverse C E (F' ◯ F)
    (EquivalenceOfCategories_Compose
       (AdjointEquivalence_to_Equivalence A)
       (AdjointEquivalence_to_Equivalence B)) = U ◯ U' := eq_refl.

End Compose.

(* * ** The 恒等 adjoint 等价 （已译） *)

Section Identity.

Context {C : Category}.

(* Id[C] is adjoint-equivalent to itself, over [Adjunction_Id]
   (Adjunction/Compose.v, itself Instance/Adjoints.v's [adj_id]
   reused).  Both invertibility clauses transport along the identity. *)
Definition AdjointEquivalence_Id : AdjointEquivalence Id[C] Id[C] :=
  @Build_AdjointEquivalence C C Id[C] Id[C] (@Adjunction_Id C)
    (fun x => IsIso_along (@Adjunction_Id_unit C x) IsIso_id)
    (fun x => IsIso_along (@Adjunction_Id_counit C x) IsIso_id).

Example AdjointEquivalence_Id_adjunction :
  @adj_equivalence _ _ _ _ AdjointEquivalence_Id = @Adjunction_Id C := eq_refl.

Definition AdjointEquivalence_Id_unit (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Id) x ≈ id[x] :=
  @Adjunction_Id_unit C x.

Definition AdjointEquivalence_Id_counit (x : C) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ AdjointEquivalence_Id) x ≈ id[x] :=
  @Adjunction_Id_counit C x.

(* The two-sided inverses 恒等's clauses 恒等. （已译） *)
Example AdjointEquivalence_Id_unit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_unit_iso _ _ _ _ AdjointEquivalence_Id x) = id[x] := eq_refl.

Example AdjointEquivalence_Id_counit_inverse (x : C) :
  @two_sided_inverse _ _ _ _
    (@adj_equiv_counit_iso _ _ _ _ AdjointEquivalence_Id x) = id[x] := eq_refl.

End Identity.

(* 相关说明。 （已译） *)

Section Inverse.

Context {C D : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context (A : AdjointEquivalence F U).

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example AdjointEquivalence_swap_readback :
  @adj_equivalence _ _ _ _ (AdjointEquivalence_swap A)
    = AdjointEquivalence_swap_adjunction A := eq_refl.

End Inverse.

(* 相关说明。 （已译） *)

Section Laws.

Context {C1 C2 C3 C4 : Category}.
Context {F1 : C1 ⟶ C2} {U1 : C2 ⟶ C1}.
Context {F2 : C2 ⟶ C3} {U2 : C3 ⟶ C2}.
Context {F3 : C3 ⟶ C4} {U3 : C4 ⟶ C3}.
Context (A : AdjointEquivalence F1 U1).
Context (B : AdjointEquivalence F2 U2).
Context (G : AdjointEquivalence F3 U3).

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition assoc_left :=
  AdjointEquivalence_Compose (AdjointEquivalence_Compose A B) G.

Definition assoc_right :=
  AdjointEquivalence_Compose A (AdjointEquivalence_Compose B G).

Example AdjointEquivalence_Compose_assoc_unit (x : C1) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_left) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_right) x := eq_refl.

Example AdjointEquivalence_Compose_assoc_counit (y : C4) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_left) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ assoc_right) y := eq_refl.

(* The 恒等 laws, at same two grades: not statable at class
 (again pinned probe), nose at unit counit. （已译） *)

Example AdjointEquivalence_Compose_id_left_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example AdjointEquivalence_Compose_id_left_counit (y : C2) :
  @counit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ A) y := eq_refl.

Example AdjointEquivalence_Compose_id_right_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose A (@AdjointEquivalence_Id C2))) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example AdjointEquivalence_Compose_id_right_counit (y : C2) :
  @counit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose A (@AdjointEquivalence_Id C2))) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ A) y := eq_refl.

End Laws.

(** ** Non-vacuity *)

(*
   本节说明伴随、函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition indiscrete_swap :
  AdjointEquivalence (Erase (Indiscrete bool)) IndT :=
  AdjointEquivalence_swap indiscrete_adjoint_equivalence.

Definition indiscrete_square :
  AdjointEquivalence (IndT ◯ Erase (Indiscrete bool))
                     (IndT ◯ Erase (Indiscrete bool)) :=
  AdjointEquivalence_Compose indiscrete_swap indiscrete_adjoint_equivalence.

(* The composite is not an identity: its functor moves an object. *)
Example indiscrete_square_moves :
  (IndT ◯ Erase (Indiscrete bool)) false = true := eq_refl.

Theorem indiscrete_square_not_id :
  (IndT ◯ Erase (Indiscrete bool)) false = false → False.
Proof. discriminate. Qed.

(* Consequently the composite's unit at [false] connects two DIFFERENT
   objects: its codomain is [true].  Recorded on the objects, because
   [Indiscrete]'s hom family ignores its endpoints -- see the header. *)
Example indiscrete_square_unit_codomain :
  (IndT ◯ Erase (Indiscrete bool))
    ((IndT ◯ Erase (Indiscrete bool)) false) = true := eq_refl.

(* The underlying 伴随 witness 复合 two
 constituents', nose. （已译） *)
Example indiscrete_square_adjunction :
  @adj_equivalence _ _ _ _ indiscrete_square
    = Adjunction_Compose
        (@adj_equivalence _ _ _ _ indiscrete_swap)
        (@adj_equivalence _ _ _ _ indiscrete_adjoint_equivalence) := eq_refl.
