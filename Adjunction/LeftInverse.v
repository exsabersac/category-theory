Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Skeleton.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.

(*
    nLab: https://ncatlab.org/nlab/show/reflective+subcategory
    nLab: https://ncatlab.org/nlab/show/adjoint+functor
    nLab: https://ncatlab.org/nlab/show/full+subcategory
    nLab: https://ncatlab.org/nlab/show/fully+faithful+functor
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

Definition InjectiveOnObjects@{ao ah ap xo xh xp}
  {A : Category@{ao ah ap}} {X : Category@{xo xh xp}} (G : A ⟶ X) :=
  ∀ a a' : A, G a = G a' → a = a'.

Definition InjectiveOnObjects_Id@{co ch cp} {C : Category@{co ch cp}} :
  InjectiveOnObjects Id[C] :=
  fun a a' H => H.

Definition InjectiveOnObjects_Compose {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C}
  (HG : InjectiveOnObjects G) (HF : InjectiveOnObjects F) :
  InjectiveOnObjects (G ◯ F) :=
  fun a a' H => HF a a' (HG (F a) (F a') H).

Definition InjectiveOnObjects_cancel {A B C : Category}
  {F : A ⟶ B} {G : B ⟶ C} (HGF : InjectiveOnObjects (G ◯ F)) :
  InjectiveOnObjects F :=
  fun a a' H => HGF a a' (f_equal (fobj[G]) H).

Record LeftAdjointLeftInverse {A X : Category} (G : A ⟶ X) : Type := {
  lali_left : X ⟶ A;
  lali_adj : lali_left ⊣ G;
  lali_obj (a : A) : lali_left (G a) = a;
  lali_counit (a : A) :
    @counit A X lali_left G lali_adj a ≈ id_cast (lali_obj a)
}.

Arguments lali_left {A X G} _.
Arguments lali_adj {A X G} _.
Arguments lali_obj {A X G} _ _.
Arguments lali_counit {A X G} _ _.

Section Consequences.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Local Notation F := (lali_left P).
Local Notation e := (lali_obj P).

Definition lali_counit_iso (a : A) : F (G a) ≅ a := id_cast_iso (e a).

(* 相关说明。 （已译） *)
Program Definition lali_counit_IsIsomorphism (a : A) :
  IsIsomorphism (@counit A X F G (lali_adj P) a) := {|
  two_sided_inverse := id_cast (eq_sym (e a))
|}.
Next Obligation.
  intros a; rewrite (lali_counit P a); apply id_cast_inv_r.
Qed.
Next Obligation.
  intros a; rewrite (lali_counit P a); apply id_cast_inv_l.
Qed.

Program Definition lali_Full : Category.Theory.Functor.Full G := {|
  prefmap := fun a a' h =>
    from (@adj A X F G (lali_adj P) (G a) a') h ∘ id_cast (eq_sym (e a))
|}.
Next Obligation.
  intros a a' g.
  rewrite (@fmap_to_adj_counit A X F G (lali_adj P)).
  rewrite (lali_counit P a).
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l, id_right.
  exact (@from_adj_comp_law A X F G (lali_adj P) (G a) a' g).
Qed.

Program Definition lali_Faithful : Faithful G := {| fmap_inj := _ |}.
Next Obligation.
  intros x y f g Hfg.
  rewrite !(@fmap_to_adj_counit A X F G (lali_adj P)) in Hfg.
  assert (f ∘ @counit A X F G (lali_adj P) x
            ≈ g ∘ @counit A X F G (lali_adj P) x) as Hc.
  { rewrite <- (@to_adj_comp_law A X F G (lali_adj P) _ _
                  (f ∘ @counit A X F G (lali_adj P) x)).
    rewrite <- (@to_adj_comp_law A X F G (lali_adj P) _ _
                  (g ∘ @counit A X F G (lali_adj P) x)).
    now rewrite Hfg. }
  rewrite (lali_counit P x) in Hc.
  rewrite <- (id_right f), <- (id_right g).
  rewrite <- (id_cast_inv_r (e x)).
  rewrite !comp_assoc.
  now rewrite Hc.
Qed.

Definition lali_injective_on_objects : InjectiveOnObjects G :=
  fun a a' H =>
    eq_trans (eq_sym (e a)) (eq_trans (f_equal (fobj[F]) H) (e a')).

End Consequences.

(* * ** Strict 函子 equality, [id_cast] form （已译） *)

Definition strict_id_cast_nat {C D : Category} {F H : C ⟶ D}
  (E : @equiv _ (@Functor_StrictEq_Setoid C D) F H)
  (x y : C) (f : x ~> y) :
  id_cast (`1 E y) ∘ fmap[F] f ≈ fmap[H] f ∘ id_cast (`1 E x) :=
  fst (transport_square (`1 E x) (`1 E y) (fmap[F] f) (fmap[H] f))
      (`2 E x y f).

(* * ** The inverse [id_cast] 同构, without [eq_sym_involutive] （已译） *)

Program Definition id_cast_iso_sym {C : Category} {x y : C} (e : x = y) :
  y ≅ x := {|
  to   := id_cast (eq_sym e);
  from := id_cast e
|}.
Next Obligation. intros; destruct e; cat. Qed.
Next Obligation. intros; destruct e; cat. Qed.

(* * ** An 同构 范畴 等价 范畴 （已译） *)

Section StrictEquivalence.

Context {A B : Category}.
Context (P : A ⟶ B).
Context (Q : B ⟶ A).
Context (E1 : @equiv _ (@Functor_StrictEq_Setoid B B) (P ◯ Q) Id[B]).
Context (E2 : @equiv _ (@Functor_StrictEq_Setoid A A) (Q ◯ P) Id[A]).

Program Definition strict_equivalence : @EquivalenceOfCategories A B P := {|
  quasi_inverse := Q;
  equivalence_counit := (fun b => id_cast_iso (`1 E1 b); _);
  equivalence_unit := (fun a => id_cast_iso_sym (`1 E2 a); _)
|}.
Next Obligation.
  intros b b' u; simpl.
  rewrite <- comp_assoc.
  rewrite <- (strict_id_cast_nat E1 b b' u).
  rewrite comp_assoc, id_cast_inv_l.
  now rewrite id_left.
Qed.
Next Obligation.
  intros a a' u; simpl.
  rewrite (strict_id_cast_nat E2 a a' u).
  rewrite <- comp_assoc, id_cast_inv_r.
  now rewrite id_right.
Qed.

End StrictEquivalence.

(* * ** Transporting along strict equality 右伴随 （已译） *)

Section RightStrict.

Context {A X : Category}.
Context {F : X ⟶ A}.
Context {G G' : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (E : @equiv _ (@Functor_StrictEq_Setoid A X) G G').

Definition rs_to (x : X) (a : A) (f : F x ~> a) : x ~> G' a :=
  id_cast (`1 E a) ∘ to (@adj A X F G Adj x a) f.

Definition rs_from (x : X) (a : A) (g : x ~> G' a) : F x ~> a :=
  from (@adj A X F G Adj x a) (id_cast (eq_sym (`1 E a)) ∘ g).

Program Definition rs_iso (x : X) (a : A) :
  @Isomorphism Sets
    {| carrier := @hom A (F x) a  ; is_setoid := @homset A (F x) a |}
    {| carrier := @hom X x (G' a) ; is_setoid := @homset X x (G' a) |} := {|
  to   := {| morphism := rs_to x a |};
  from := {| morphism := rs_from x a |}
|}.
Next Obligation.
  intros x a f g Hfg; unfold rs_to; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x a f g Hfg; unfold rs_from; simpl.
  now rewrite Hfg.
Qed.
Next Obligation.
  intros x a g; unfold rs_to, rs_from; simpl.
  rewrite (@from_adj_comp_law A X F G Adj).
  rewrite comp_assoc, id_cast_inv_r.
  now rewrite id_left.
Qed.
Next Obligation.
  intros x a f; unfold rs_to, rs_from; simpl.
  rewrite comp_assoc, id_cast_inv_l, id_left.
  exact (@to_adj_comp_law A X F G Adj x a f).
Qed.

Lemma rs_to_nat_l (x y : X) (a : A) (f : F y ~> a) (g : x ~> y) :
  rs_to x a (f ∘ fmap[F] g) ≈ rs_to y a f ∘ g.
Proof.
  unfold rs_to.
  rewrite (@to_adj_nat_l A X F G Adj).
  now rewrite comp_assoc.
Qed.

Lemma rs_to_nat_r (x : X) (a b : A) (f : a ~> b) (g : F x ~> a) :
  rs_to x b (f ∘ g) ≈ fmap[G'] f ∘ rs_to x a g.
Proof.
  unfold rs_to.
  rewrite (@to_adj_nat_r A X F G Adj).
  rewrite comp_assoc.
  rewrite (strict_id_cast_nat E a b f).
  now rewrite <- comp_assoc.
Qed.

Definition rs_adj : F ⊣ G' :=
  @Build_Adjunction' A X F G' rs_iso rs_to_nat_l rs_to_nat_r.

Lemma rs_counit (a : A) :
  @counit A X F G' rs_adj a
    ≈ @counit A X F G Adj a ∘ fmap[F] (id_cast (eq_sym (`1 E a))).
Proof.
  unfold counit.
  transitivity (rs_from (G' a) a id).
  - reflexivity.
  - unfold rs_from.
    rewrite id_right.
    exact (@from_adj_counit A X F G Adj (G' a) a (id_cast (eq_sym (`1 E a)))).
Qed.

End RightStrict.

Definition lali_along_right_strict {A X : Category} {G G' : A ⟶ X}
  (P : LeftAdjointLeftInverse G)
  (E : @equiv _ (@Functor_StrictEq_Setoid A X) G G') :
  LeftAdjointLeftInverse G'.
Proof.
  unshelve refine {|
    lali_left := lali_left P;
    lali_adj := rs_adj (lali_adj P) E;
    lali_obj := fun a =>
      eq_trans (f_equal (fobj[lali_left P]) (eq_sym (`1 E a))) (lali_obj P a)
  |}.
  intros a.
  rewrite (rs_counit (lali_adj P) E a).
  rewrite (lali_counit P a).
  rewrite fmap_id_cast.
  now rewrite id_cast_trans.
Defined.

(* * ** Clause (b): 左伴随, full, faithful, injective 对象 （已译） *)

Record LeftAdjointFFInjective {A X : Category} (G : A ⟶ X) : Type := {
  ffi_left : X ⟶ A;
  ffi_adj : ffi_left ⊣ G;
  ffi_full : Category.Theory.Functor.Full G;
  ffi_faithful : Faithful G;
  ffi_injective : InjectiveOnObjects G
}.

Arguments ffi_left {A X G} _.
Arguments ffi_adj {A X G} _.
Arguments ffi_full {A X G} _.
Arguments ffi_faithful {A X G} _.
Arguments ffi_injective {A X G} _.

Definition lali_implies_ffi {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) : LeftAdjointFFInjective G := {|
  ffi_left := lali_left P;
  ffi_adj := lali_adj P;
  ffi_full := lali_Full P;
  ffi_faithful := lali_Faithful P;
  ffi_injective := lali_injective_on_objects P
|}.

(** ** The image subcategory *)

Section Image.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (B : LeftAdjointFFInjective G).

Program Definition LaliImageSub : Subcategory X := {|
  sobj := fun x => { a : A & G a = x };
  shom := fun x y ox oy f => True
|}.
Next Obligation. intros; exact I. Defined.
Next Obligation. intros; exact I. Defined.

Program Definition ImageTo : A ⟶ Sub X LaliImageSub := {|
  fobj := fun a => (G a; (a; eq_refl));
  fmap := fun a a' f => (fmap[G] f; I)
|}.
Next Obligation. intros a a' f g Hfg; simpl; now rewrite Hfg. Qed.
Next Obligation. intros a; simpl; apply fmap_id. Qed.
Next Obligation. intros a a' a'' f g; simpl; apply fmap_comp. Qed.

Program Definition ImageFrom : Sub X LaliImageSub ⟶ A := {|
  fobj := fun y => `1 (`2 y);
  fmap := fun y y' f =>
    prefmap (Full := ffi_full B)
      (hom_cast (eq_sym (`2 (`2 y))) (eq_sym (`2 (`2 y'))) (`1 f))
|}.
Next Obligation.
  intros y y' f g Hfg.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  rewrite !(fmap_sur (Full := ffi_full B)).
  now apply hom_cast_respects.
Qed.
Next Obligation.
  intros y.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  rewrite (fmap_sur (Full := ffi_full B)), fmap_id.
  now rewrite hom_cast_id.
Qed.
Next Obligation.
  intros y y' y'' f g.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  rewrite fmap_comp, !(fmap_sur (Full := ffi_full B)).
  now rewrite hom_cast_comp.
Qed.


(** The two round trips, at strict functor equality. *)

Definition image_from_to_obj (a : A) : ImageFrom (ImageTo a) = a := eq_refl.

Definition image_to_from_obj (y : Sub X LaliImageSub) :
  ImageTo (ImageFrom y) = y.
Proof. destruct y as [u [b e]]; destruct e; reflexivity. Defined.

Lemma image_from_to_strict :
  @equiv _ (@Functor_StrictEq_Setoid A A) (ImageFrom ◯ ImageTo) Id[A].
Proof.
  apply (strict_equiv_of_id_cast_nat (ImageFrom ◯ ImageTo) Id[A]
           image_from_to_obj).
  intros a a' f; unfold image_from_to_obj; simpl.
  rewrite id_left, id_right.
  apply (fmap_inj (Faithful := ffi_faithful B)).
  now rewrite (fmap_sur (Full := ffi_full B)).
Defined.

Lemma image_to_from_strict :
  @equiv _ (@Functor_StrictEq_Setoid (Sub X LaliImageSub) (Sub X LaliImageSub))
    (ImageTo ◯ ImageFrom) Id[Sub X LaliImageSub].
Proof.
  apply (strict_equiv_of_id_cast_nat (ImageTo ◯ ImageFrom)
           Id[Sub X LaliImageSub] image_to_from_obj).
  intros y y' f.
  destruct y as [u [b e]], y' as [u' [b' e']].
  destruct e, e'; simpl.
  rewrite id_left, id_right.
  now rewrite (fmap_sur (Full := ffi_full B)).
Defined.

Definition ImageIso : @Isomorphism StrictCat A (Sub X LaliImageSub) :=
  @Build_Isomorphism StrictCat A (Sub X LaliImageSub) ImageTo ImageFrom
    image_to_from_strict image_from_to_strict.


(** The image subcategory full reflective, [G] factors through
 嵌入. （已译） *)

Definition image_equivalence : @EquivalenceOfCategories A (Sub X LaliImageSub)
    ImageTo :=
  strict_equivalence ImageTo ImageFrom image_to_from_strict
    image_from_to_strict.

Definition image_incl_obj (y : Sub X LaliImageSub) :
  G (ImageFrom y) = Incl X LaliImageSub y := `2 (`2 y).

Lemma image_incl_strict :
  @equiv _ (@Functor_StrictEq_Setoid (Sub X LaliImageSub) X)
    (G ◯ ImageFrom) (Incl X LaliImageSub).
Proof.
  apply (strict_equiv_of_id_cast_nat (G ◯ ImageFrom) (Incl X LaliImageSub)
           image_incl_obj).
  intros y y' f.
  destruct y as [u [b e]], y' as [u' [b' e']].
  destruct e, e'; simpl.
  rewrite id_left, id_right.
  now rewrite (fmap_sur (Full := ffi_full B)).
Defined.

Definition image_reflective_adj :
  (ImageTo ◯ ffi_left B) ⊣ Incl X LaliImageSub :=
  rs_adj (Adjunction_Compose (ffi_adj B) (equiv_adjunction image_equivalence))
    image_incl_strict.

Definition image_full : Construction.Subcategory.Full X LaliImageSub :=
  fun x y ox oy f => I.

Definition ImageReflective : Reflective LaliImageSub := {|
  reflective_full := image_full;
  reflector := ImageTo ◯ ffi_left B;
  reflective_adj := image_reflective_adj
|}.

Lemma image_factor :
  @equiv _ (@Functor_StrictEq_Setoid A X) G (Incl X LaliImageSub ◯ ImageTo).
Proof.
  apply (strict_equiv_of_id_cast_nat G (Incl X LaliImageSub ◯ ImageTo)
           (fun a => eq_refl)).
  intros a a' f; simpl.
  now rewrite id_left, id_right.
Defined.

End Image.

(* * ** Clause (c): full reflective subcategory 同构 （已译） *)

Record ReflectiveIsoPresentation {A X : Category} (G : A ⟶ X) : Type := {
  ri_sub : Subcategory X;
  ri_reflective : Reflective ri_sub;
  ri_iso : @Isomorphism StrictCat A (Sub X ri_sub);
  ri_factor : @equiv _ (@Functor_StrictEq_Setoid A X) G
                (Incl X ri_sub ◯ to ri_iso)
}.

Arguments ri_sub {A X G} _.
Arguments ri_reflective {A X G} _.
Arguments ri_iso {A X G} _.
Arguments ri_factor {A X G} _.

Definition ffi_implies_ri {A X : Category} {G : A ⟶ X}
  (B : LeftAdjointFFInjective G) : ReflectiveIsoPresentation G := {|
  ri_sub := @LaliImageSub A X G;
  ri_reflective := ImageReflective B;
  ri_iso := ImageIso B;
  ri_factor := @image_factor A X G
|}.

(* * ** Transporting left-adjoint-left-inverse along 同构 （已译） *)

Section StrictIsoTransport.

Context {A X Y : Category}.
Context {K : Y ⟶ X}.
Context (P : LeftAdjointLeftInverse K).
Context (H : @Isomorphism StrictCat A Y).

Definition si_equivalence : @EquivalenceOfCategories Y A (from H) :=
  strict_equivalence (from H) (to H) (iso_from_to H) (iso_to_from H).

Definition si_adj : (from H ◯ lali_left P) ⊣ (K ◯ to H) :=
  Adjunction_Compose (lali_adj P) (equiv_adjunction si_equivalence).

Definition si_obj (a : A) : (from H ◯ lali_left P) ((K ◯ to H) a) = a :=
  eq_trans (f_equal (fobj[from H]) (lali_obj P (to H a)))
           (`1 (iso_from_to H) a).

Lemma si_counit (a : A) :
  @counit A X (from H ◯ lali_left P) (K ◯ to H) si_adj a ≈ id_cast (si_obj a).
Proof.
  transitivity
    (from (@adj A Y (from H) (to H) (equiv_adjunction si_equivalence)
             (lali_left P (K (to H a))) a)
       (@counit Y X (lali_left P) K (lali_adj P) (to H a))).
  { reflexivity. }
  rewrite (lali_counit P (to H a)).
  rewrite (@from_adj_counit A Y (from H) (to H)
             (equiv_adjunction si_equivalence)).
  rewrite (equiv_adjunction_counit_at si_equivalence a).
  rewrite fmap_id_cast.
  unfold si_obj.
  rewrite <- id_cast_trans.
  reflexivity.
Qed.

Definition lali_along_strict_iso : LeftAdjointLeftInverse (K ◯ to H) := {|
  lali_left := from H ◯ lali_left P;
  lali_adj := si_adj;
  lali_obj := si_obj;
  lali_counit := si_counit
|}.

End StrictIsoTransport.

(** ** The characterization *)

Definition strict_sym {C D : Category} {F H : C ⟶ D}
  (E : @equiv _ (@Functor_StrictEq_Setoid C D) F H) :
  @equiv _ (@Functor_StrictEq_Setoid C D) H F :=
  @Equivalence_Symmetric _ _
    (@setoid_equiv _ (@Functor_StrictEq_Setoid C D)) F H E.

Definition ri_lali_implies_lali {A X : Category} {G : A ⟶ X}
  (Pres : ReflectiveIsoPresentation G)
  (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))) :
  LeftAdjointLeftInverse G :=
  lali_along_right_strict
    (lali_along_strict_iso L (ri_iso Pres))
    (strict_sym (ri_factor Pres)).

Theorem lali_characterization {A X : Category} (G : A ⟶ X) :
  (LeftAdjointLeftInverse G → LeftAdjointFFInjective G)
    * (LeftAdjointFFInjective G → ReflectiveIsoPresentation G)
    * (∀ Pres : ReflectiveIsoPresentation G,
         LeftAdjointLeftInverse (Incl X (ri_sub Pres))
           → LeftAdjointLeftInverse G).
Proof.
  split; [ split | ].
  - exact (@lali_implies_ffi A X G).
  - exact (@ffi_implies_ri A X G).
  - exact (@ri_lali_implies_lali A X G).
Defined.

Definition ri_lali_implies_ffi {A X : Category} {G : A ⟶ X}
  (Pres : ReflectiveIsoPresentation G)
  (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))) :
  LeftAdjointFFInjective G :=
  lali_implies_ffi (ri_lali_implies_lali Pres L).

Definition lali_implies_ri {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) : ReflectiveIsoPresentation G :=
  ffi_implies_ri (lali_implies_ffi P).

(* * ** The 嵌入 image subcategory has left-adjoint-left-inverse （已译） *)

Section ImageInsertion.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Local Notation B := (lali_implies_ffi P).

Definition ii_obj (y : Sub X (@LaliImageSub A X G)) :
  (ImageTo ◯ lali_left P) (Incl X (@LaliImageSub A X G) y) = y :=
  eq_trans
    (f_equal (fobj[ImageTo ◯ lali_left P]) (eq_sym (image_incl_obj B y)))
    (eq_trans (f_equal (fobj[@ImageTo A X G])
                 (lali_obj P (ImageFrom B y)))
              (image_to_from_obj B y)).

Lemma ii_counit (y : Sub X (@LaliImageSub A X G)) :
  @counit (Sub X (@LaliImageSub A X G)) X (ImageTo ◯ lali_left P)
    (Incl X (@LaliImageSub A X G)) (image_reflective_adj B) y
    ≈ id_cast (ii_obj y).
Proof.
  unfold image_reflective_adj.
  rewrite (rs_counit
             (Adjunction_Compose (ffi_adj B)
                (equiv_adjunction (image_equivalence B)))
             (image_incl_strict B) y).
  transitivity
    (from (@adj (Sub X (@LaliImageSub A X G)) A ImageTo (ImageFrom B)
             (equiv_adjunction (image_equivalence B))
             (lali_left P (G (ImageFrom B y))) y)
       (@counit A X (lali_left P) G (lali_adj P) (ImageFrom B y))
       ∘ fmap[ImageTo ◯ lali_left P]
           (id_cast (eq_sym (image_incl_obj B y)))).
  { reflexivity. }
  rewrite (lali_counit P (ImageFrom B y)).
  rewrite (@from_adj_counit (Sub X (@LaliImageSub A X G)) A ImageTo
             (ImageFrom B) (equiv_adjunction (image_equivalence B))).
  rewrite (equiv_adjunction_counit_at (image_equivalence B) y).
  rewrite !fmap_id_cast.
  unfold ii_obj.
  rewrite <- !id_cast_trans.
  reflexivity.
Qed.

Definition lali_image_insertion :
  LeftAdjointLeftInverse (Incl X (@LaliImageSub A X G)) := {|
  lali_left := ImageTo ◯ lali_left P;
  lali_adj := image_reflective_adj B;
  lali_obj := ii_obj;
  lali_counit := ii_counit
|}.

End ImageInsertion.

(* 相关说明。 （已译） *)

Definition lali_ri_insertion {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) :
  LeftAdjointLeftInverse (Incl X (ri_sub (lali_implies_ri P))) :=
  lali_image_insertion P.

Definition lali_cycle {A X : Category} {G : A ⟶ X}
  (P : LeftAdjointLeftInverse G) : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali (lali_implies_ri P) (lali_ri_insertion P).

(** ** Examples *)

Definition Id_LALI {C : Category} : LeftAdjointLeftInverse (Id[C]) := {|
  lali_left := Id[C];
  lali_adj := Adjunction_Id;
  lali_obj := fun a => eq_refl;
  lali_counit := fun a => Adjunction_Id_counit
|}.

Section TerminalPoint.

Universes o h.

Context {C : Category@{o h h}}.
Context (T : @Terminal C).

Local Notation One := (_1@{o h h}).
Local Notation t := (@terminal_obj C T).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition PointAt (c : C) : One ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ _ => id
|}.
Next Obligation. proper. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; now rewrite id_left. Qed.

Lemma one_cat_thin {x y : @obj One} (f g : @hom One x y) : f ≈ g.
Proof. destruct f, g; reflexivity. Qed.

Definition point_adj : Erase C ⊣ PointAt t.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros x a.
    unshelve eapply Build_Isomorphism.
    + unshelve eapply Build_SetoidMorphism.
      * exact (fun _ => @one C T x).
      * proper.
    + unshelve eapply Build_SetoidMorphism.
      * exact (fun _ => ttt).
      * proper.
    + intros g; simpl; apply one_unique.
    + intros f; simpl; now destruct f.
  - intros x y a f g; simpl; apply one_unique.
  - intros x a b f g; simpl; apply one_unique.
Defined.

Definition terminal_LALI : LeftAdjointLeftInverse (PointAt t).
Proof.
  unshelve refine {| lali_left := Erase C; lali_adj := point_adj |}.
  - intros a; now destruct a.
  - intros a; apply one_cat_thin.
Defined.

End TerminalPoint.

(** A non-degenerate instance: the walking arrow. *)

Program Definition TwoY_Terminal : @Terminal _2 := {|
  terminal_obj := TwoY;
  one := fun x => match x with
                  | TwoX => TwoXY
                  | TwoY => TwoIdY
                  end
|}.
Next Obligation.
  intros x f g; destruct x; simpl in *.
  - pose proof (TwoHom_inv TwoX TwoY f) as Hf.
    pose proof (TwoHom_inv TwoX TwoY g) as Hg.
    simpl in Hf, Hg; now subst.
  - pose proof (TwoHom_inv TwoY TwoY f) as Hf.
    pose proof (TwoHom_inv TwoY TwoY g) as Hg.
    simpl in Hf, Hg; now subst.
Qed.

Definition two_LALI : LeftAdjointLeftInverse (PointAt (C:=_2) TwoY) :=
  terminal_LALI TwoY_Terminal.

Example two_lali_left_is_Erase :
  lali_left two_LALI = Erase _2 := eq_refl.

Example two_lali_obj_TwoY :
  PointAt (C:=_2) TwoY (lali_left two_LALI TwoX) = TwoY := eq_refl.

Lemma two_lali_moves_TwoX :
  PointAt (C:=_2) TwoY (lali_left two_LALI TwoX) = TwoX → False.
Proof. simpl; discriminate. Qed.

(*
   本节说明 LeftInverse 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Readbacks.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).
Context (B : LeftAdjointFFInjective G).

Example ffi_left_is_lali_left :
  ffi_left (lali_implies_ffi P) = lali_left P := eq_refl.

Example ffi_adj_is_lali_adj :
  ffi_adj (lali_implies_ffi P) = lali_adj P := eq_refl.

Example ri_sub_is_image :
  ri_sub (lali_implies_ri P) = @LaliImageSub A X G := eq_refl.

Example ri_iso_to_is_ImageTo :
  to (ri_iso (ffi_implies_ri B)) = @ImageTo A X G := eq_refl.

Example ri_iso_from_is_ImageFrom :
  from (ri_iso (ffi_implies_ri B)) = ImageFrom B := eq_refl.

Example image_reflector_is_composite :
  reflector (ImageReflective B) = ImageTo ◯ ffi_left B := eq_refl.

Example image_incl_obj_is_membership (y : Sub X (@LaliImageSub A X G)) :
  image_incl_obj B y = `2 (`2 y) := eq_refl.

Example image_from_to_obj_is_refl (a : A) :
  image_from_to_obj B a = eq_refl := eq_refl.

Example lali_Full_prefmap (a a' : A) (h : G a ~> G a') :
  prefmap (Full := lali_Full P) h
    = from (@adj A X (lali_left P) G (lali_adj P) (G a) a') h
        ∘ id_cast (eq_sym (lali_obj P a)) := eq_refl.

Example lali_left_along_right_strict {G' : A ⟶ X}
  (E : @equiv _ (@Functor_StrictEq_Setoid A X) G G') :
  lali_left (lali_along_right_strict P E) = lali_left P := eq_refl.

Example lali_image_insertion_left :
  lali_left (lali_image_insertion P) = ImageTo ◯ lali_left P := eq_refl.

End Readbacks.

Example lali_left_along_strict_iso {A X Y : Category} {K : Y ⟶ X}
  (L : LeftAdjointLeftInverse K) (H : @Isomorphism StrictCat A Y) :
  lali_left (lali_along_strict_iso L H) = from H ◯ lali_left L := eq_refl.

Example terminal_lali_left {C : Category} (T : @Terminal C) :
  lali_left (terminal_LALI T) = Erase C := eq_refl.
