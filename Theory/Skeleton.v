Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(** * 骨骼与骨骼范畴 *)

(* nLab: https://ncatlab.org/nlab/show/skeleton
   Wikipedia: https://en.wikipedia.org/wiki/Skeleton_(category_theory)

   范畴的骨骼 (skeleton) 是选择每个同构类恰一个代表对象所得的等价子范畴：骨骼等价于原范畴，
   且同构对象在骨骼中重合。本文件在库的 setoid/宇宙纪律下构造骨骼与相关等价数据；长证明旁注
   若仍为英文属后续波次。 *)

(* * ** The half-adjoint correction, at level 对象 types （已译） *)

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HalfAdjoint.
Context {A B : Type}.
Variable f : A → B.
Variable g : B → A.
Variable eta : ∀ a, g (f a) = a.
Variable eps : ∀ b, f (g b) = b.

Lemma f_equal_idmap {X : Type} {x y : X} (p : x = y) :
  f_equal (fun z => z) p = p.
Proof. now destruct p. Qed.

Lemma ap_ap {X Y Z : Type} (u : X → Y) (v : Y → Z) {x y : X} (p : x = y) :
  f_equal v (f_equal u p) = f_equal (fun t => v (u t)) p.
Proof. now destruct p. Qed.

Lemma homotopy_natural {X Y : Type} (u v : X → Y) (H : ∀ x, u x = v x)
      {x y : X} (p : x = y) :
  eq_trans (H x) (f_equal v p) = eq_trans (f_equal u p) (H y).
Proof. destruct p; simpl. now rewrite eq_trans_refl_l. Qed.

Lemma cancel_right {X : Type} {x y z : X} (p q : x = y) (r : y = z) :
  eq_trans p r = eq_trans q r → p = q.
Proof. destruct r; auto. Qed.

Lemma homotopy_id_shift (u : A → A) (H : ∀ x, u x = x) (x : A) :
  H (u x) = f_equal u (H x).
Proof.
  apply (cancel_right _ _ (H x)).
  pose proof (homotopy_natural u (fun z => z) H (H x)) as N.
  rewrite f_equal_idmap in N. now rewrite N.
Qed.

Lemma ap_eta (a : A) :
  f_equal f (eta (g (f a))) = f_equal (fun z => f (g z)) (f_equal f (eta a)).
Proof.
  rewrite (ap_ap f (fun z => f (g z)) (eta a)).
  pose proof (homotopy_id_shift (fun x => g (f x)) eta a) as E1.
  simpl in E1. rewrite E1.
  now rewrite (ap_ap (fun x => g (f x)) f (eta a)).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition adjointified (b : B) : f (g b) = b :=
  eq_trans (eq_sym (eps (f (g b)))) (eq_trans (f_equal f (eta (g b))) (eps b)).

Lemma half_adjoint_triangle (a : A) : adjointified (f a) = f_equal f (eta a).
Proof.
  unfold adjointified. rewrite ap_eta.
  pose proof (homotopy_natural (fun z => f (g z)) (fun z => z) eps
                (f_equal f (eta a))) as N.
  rewrite f_equal_idmap in N. rewrite <- N.
  rewrite eq_trans_assoc, eq_trans_sym_inv_l.
  now rewrite eq_trans_refl_l.
Qed.

End HalfAdjoint.

(* * ** Strict 函子 equality family 对象 equalities （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma transport_square {D : Category} {a a' b b' : D}
  (p : a = a') (q : b = b') (u : a ~{D}~> b) (v : a' ~{D}~> b') :
  (Logic.transport (fun z => a ~{D}~> z) q u
     ≈ Logic.transport_r (fun z => z ~{D}~> b') p v)
  ↔ (id_cast q ∘ u ≈ v ∘ id_cast p).
Proof.
  destruct p, q; unfold Logic.transport, Logic.transport_r, id_cast; simpl;
    split; intro H; [ now rewrite id_left, id_right | ].
  now rewrite id_left, id_right in H.
Qed.

Definition strict_equiv_of_id_cast_nat
  {C D : Category} (F G : C ⟶ D) (e : ∀ x : C, F x = G x)
  (H : ∀ (x y : C) (f : x ~> y),
         id_cast (e y) ∘ fmap[F] f ≈ fmap[G] f ∘ id_cast (e x)) :
  @equiv _ (@Functor_StrictEq_Setoid C D) F G :=
  existT _ e (fun x y f => snd (transport_square (e x) (e y)
                                  (fmap[F] f) (fmap[G] f)) (H x y f)).

(** ** Skeletal categories *)

(* Mac Lane §IV.4 Definition 3, second half; Riehl Definition 1.5.16.  A
   plain [Definition], not a [Class]: nothing here is registered for
   instance resolution, following Theory/Equivalence.v. *)

Definition Skeletal (C : Category) := ∀ x y : C, x ≅ y → x = y.

(* * ** An 等价 between skeletal 范畴 同构 （已译） *)

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SkeletalEquivalence.
Context {A B : Category}.
Variable SA : Skeletal A.
Variable SB : Skeletal B.
Variable F : A ⟶ B.
Variable E : EquivalenceOfCategories F.
#[local] Existing Instance E.
Notation G := (@quasi_inverse A B F E).

Definition F_Full : Category.Theory.Functor.Full F := Equivalence_Full E.
Definition F_Faithful : Faithful F := Equivalence_Faithful E.

Definition eta_ob (a : A) : G (F a) = a :=
  eq_sym (SA a (G (F a)) (@equivalence_unit_at A B F E a)).
Definition eps_ob (b : B) : F (G b) = b :=
  SB (F (G b)) b (@equivalence_counit_at A B F E b).
Definition Eps (b : B) : F (G b) = b :=
  adjointified (fobj[F]) (fobj[G]) eta_ob eps_ob b.

Lemma Eps_triangle (a : A) : Eps (F a) = f_equal (fobj[F]) (eta_ob a).
Proof. apply half_adjoint_triangle. Qed.

#[local] Obligation Tactic := idtac.

Program Definition Finv : B ⟶ A := {|
  fobj := fun b => G b;
  fmap := fun b b' h =>
    prefmap (Full := F_Full) (hom_cast (eq_sym (Eps b)) (eq_sym (Eps b')) h)
|}.
Next Obligation.
  intros b b' h h' Hh.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite !(fmap_sur (Full := F_Full)).
  now apply hom_cast_respects.
Qed.
Next Obligation.
  intros b.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite (fmap_sur (Full := F_Full)), fmap_id.
  now rewrite hom_cast_id.
Qed.
Next Obligation.
  intros b b' b'' g h.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite fmap_comp, !(fmap_sur (Full := F_Full)).
  now rewrite hom_cast_comp.
Qed.

Lemma FFinv_strict :
  @equiv _ (@Functor_StrictEq_Setoid B B) (F ◯ Finv) Id[B].
Proof using All.
  apply (strict_equiv_of_id_cast_nat (F ◯ Finv) Id[B] Eps).
  intros b b' h.
  change (fmap[F ◯ Finv] h)
    with (fmap[F] (prefmap (Full := F_Full)
            (hom_cast (eq_sym (Eps b)) (eq_sym (Eps b')) h))).
  rewrite (fmap_sur (Full := F_Full)).
  rewrite hom_cast_decompose, eq_sym_involutive, !comp_assoc.
  rewrite id_cast_inv_r, id_left.
  reflexivity.
Qed.

(* The [!Eps_triangle] rewrite below crux: RAW counit the
 goal would carry loop at intermediate 对象 UIP could
 collapse. （已译） *)

Lemma FinvF_strict :
  @equiv _ (@Functor_StrictEq_Setoid A A) (Finv ◯ F) Id[A].
Proof using All.
  apply (strict_equiv_of_id_cast_nat (Finv ◯ F) Id[A] eta_ob).
  intros a b f.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite !fmap_comp, !fmap_id_cast.
  change (fmap[Finv ◯ F] f)
    with (prefmap (Full := F_Full)
            (hom_cast (eq_sym (Eps (F a))) (eq_sym (Eps (F b))) (fmap[F] f))).
  rewrite (fmap_sur (Full := F_Full)).
  rewrite hom_cast_decompose, eq_sym_involutive, !Eps_triangle, !comp_assoc.
  rewrite id_cast_inv_r, id_left.
  reflexivity.
Qed.

Definition skeletal_equivalence_is_isomorphism : A ≅[StrictCat] B :=
  @Build_Isomorphism StrictCat A B F Finv FFinv_strict FinvF_strict.

End SkeletalEquivalence.

Arguments skeletal_equivalence_is_isomorphism {A B} SA SB F E.

(* 相关说明。 （已译） *)

(*
   本节说明同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Skeleton.
Context {C : Category}.

Record Skeleton := {
  skel_sub  : Subcategory C;
  skel_full : Subcategory.Full C skel_sub;
  skel_rep  : C → Sub C skel_sub;
  skel_iso  : ∀ x : C, x ≅ `1 (skel_rep x);
  skel_uniq : ∀ (x : C) (a : Sub C skel_sub), x ≅ `1 a → skel_rep x = a
}.

End Skeleton.

Arguments Skeleton : clear implicits.

Definition skel_cat {C : Category} (S : Skeleton C) : Category :=
  Sub C (skel_sub S).

Definition skel_incl {C : Category} (S : Skeleton C) : skel_cat S ⟶ C :=
  Incl C (skel_sub S).

Section SkeletonTheory.
Context {C : Category}.
Variable S : Skeleton C.

Theorem skeleton_is_skeletal : Skeletal (skel_cat S).
Proof using.
  intros a b i.
  rewrite <- (skel_uniq S `1 a a iso_id).
  apply (skel_uniq S).
  exists (`1 (to i)) (`1 (from i)).
  - exact (iso_to_from i).
  - exact (iso_from_to i).
Qed.

Definition Incl_Full : Functor.Full (skel_incl S) :=
  Full_Implies_Full_Functor C (skel_sub S) (skel_full S).

Program Definition Incl_EssSurj : EssentiallySurjective (skel_incl S) := {|
  eso_obj := skel_rep S;
  eso_iso := fun x => iso_sym (skel_iso S x)
|}.

(* Mac Lane §IV.4 Remark 1, first half: 含入 skeleton an
 等价. [Defined], so reflector below reduces. （已译） *)

Theorem skeleton_inclusion_is_equivalence :
  EquivalenceOfCategories (skel_incl S).
Proof using.
  exact (@FF_ESO_Equivalence _ _ (skel_incl S)
           Incl_Full (Incl_Faithful C (skel_sub S)) Incl_EssSurj).
Defined.

Definition skeleton_equivalence : skel_cat S ≃ C :=
  (skel_incl S; skeleton_inclusion_is_equivalence).

(* 相关说明。 （已译） *)
Definition skel_reflect : C ⟶ skel_cat S :=
  @quasi_inverse _ _ _ skeleton_inclusion_is_equivalence.

Definition skeleton_counit : skel_incl S ◯ skel_reflect ≈ Id[C] :=
  @equivalence_counit _ _ _ skeleton_inclusion_is_equivalence.

Definition skeleton_unit : Id[skel_cat S] ≈ skel_reflect ◯ skel_incl S :=
  @equivalence_unit _ _ _ skeleton_inclusion_is_equivalence.

Corollary skel_reflect_obj (x : C) : skel_reflect x = skel_rep S x.
Proof. reflexivity. Qed.

Corollary skel_reflect_incl_obj (a : skel_cat S) :
  skel_reflect (skel_incl S a) = a.
Proof. exact (skel_uniq S `1 a a iso_id). Qed.

End SkeletonTheory.

Arguments skel_reflect {C} S.

Definition skeleton_counit_iso {C : Category} (S : Skeleton C) :
  skel_incl S ◯ skel_reflect S ≅[Fun] Id[C] :=
  equiv_iso (skeleton_counit S).

Definition skeleton_unit_iso {C : Category} (S : Skeleton C) :
  Id[skel_cat S] ≅[Fun] skel_reflect S ◯ skel_incl S :=
  equiv_iso (skeleton_unit S).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition skeleton_remark {C : Category} (S : Skeleton C) :
  (Id[C] ≅[Fun] skel_incl S ◯ skel_reflect S)
  * (∀ a : skel_cat S, skel_reflect S (skel_incl S a) = a) :=
  (iso_sym (skeleton_counit_iso S), skel_reflect_incl_obj S).

(*
   本节说明 Skeleton 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Mac Lane §IV.4 Exercise 1 *)

Definition skeletons_of_equivalent_are_isomorphic
  {C D : Category} (S : Skeleton C) (T : Skeleton D) (Eq : C ≃ D) :
  skel_cat S ≅[StrictCat] skel_cat T :=
  let e : skel_cat S ≃ skel_cat T :=
      Equivalence_trans (skeleton_equivalence S)
        (Equivalence_trans Eq (Equivalence_sym (skeleton_equivalence T))) in
  skeletal_equivalence_is_isomorphism
    (skeleton_is_skeletal S) (skeleton_is_skeletal T) (`1 e) (`2 e).

Definition skeletons_are_isomorphic {C : Category} (S1 S2 : Skeleton C) :
  skel_cat S1 ≅[StrictCat] skel_cat S2 :=
  skeletons_of_equivalent_are_isomorphic S1 S2 (Equivalence_refl C).

Definition strict_iso_to_equivalence {A B : Category}
           (i : A ≅[StrictCat] B) : A ≃ B :=
  (to i;
   @Build_EquivalenceOfCategories A B (to i) (from i)
     (strict_equiv_implies_fun_equiv _ _ (iso_to_from i))
     (symmetry (strict_equiv_implies_fun_equiv _ _ (iso_from_to i)))).

Definition equivalent_of_isomorphic_skeletons
  {C D : Category} (S : Skeleton C) (T : Skeleton D)
  (i : skel_cat S ≅[StrictCat] skel_cat T) : C ≃ D :=
  Equivalence_trans (Equivalence_sym (skeleton_equivalence S))
    (Equivalence_trans (strict_iso_to_equivalence i) (skeleton_equivalence T)).

Definition skeletons_isomorphic_iff_equivalent
  {C D : Category} (S : Skeleton C) (T : Skeleton D) :
  (C ≃ D) ↔ (skel_cat S ≅[StrictCat] skel_cat T) :=
  (skeletons_of_equivalent_are_isomorphic S T,
   equivalent_of_isomorphic_skeletons S T).

(* * ** Riehl Remark 1.5.17: comparison 函子 along arbitrary F （已译） *)

Definition skel_comparison {C D : Category}
  (S : Skeleton C) (T : Skeleton D) (F : C ⟶ D) : skel_cat S ⟶ skel_cat T :=
  skel_reflect T ◯ (F ◯ skel_incl S).

Theorem skel_comparison_natural {C D : Category}
  (S : Skeleton C) (T : Skeleton D) (F : C ⟶ D) :
  skel_incl T ◯ skel_comparison S T F ≈ F ◯ skel_incl S.
Proof.
  unfold skel_comparison.
  rewrite (fun_equiv_comp_assoc (skel_incl T) (skel_reflect T)
             (F ◯ skel_incl S)).
  rewrite (skeleton_counit T).
  now rewrite (fun_equiv_id_left (F ◯ skel_incl S)).
Qed.

Definition skel_comparison_natural_iso {C D : Category}
  (S : Skeleton C) (T : Skeleton D) (F : C ⟶ D) :
  skel_incl T ◯ skel_comparison S T F ≅[Fun] F ◯ skel_incl S :=
  equiv_iso (skel_comparison_natural S T F).

(* 相关说明。 （已译） *)

Section Skeleton0.
Context {C : Category}.

Record Skeleton0 := {
  s0_sub  : Subcategory C;
  s0_full : Subcategory.Full C s0_sub;
  s0_rep  : C → Sub C s0_sub;
  s0_iso  : ∀ x : C, x ≅ `1 (s0_rep x);
  s0_uniq : ∀ (x : C) (a : Sub C s0_sub), x ≅ `1 a → `1 (s0_rep x) = `1 a
}.

End Skeleton0.
Arguments Skeleton0 : clear implicits.

Theorem skeleton0_is_skeletal_carrier {C : Category} (S : Skeleton0 C)
        (a b : Sub C (s0_sub S)) (i : a ≅ b) : `1 a = `1 b.
Proof.
  rewrite <- (s0_uniq S `1 a a iso_id).
  apply (s0_uniq S).
  exists (`1 (to i)) (`1 (from i)).
  - exact (iso_to_from i).
  - exact (iso_from_to i).
Qed.

(* The countermodel: over discrete 范畴, select membership proofs
 free loop space each 对象. （已译） *)

Program Definition Loop_Sub (A : Type) : Subcategory (DiscreteCat A) := {|
  sobj := fun x => x = x;
  shom := fun x y ox oy f => True
|}.

Program Definition LoopSkeleton0 (A : Type) : Skeleton0 (DiscreteCat A) := {|
  s0_sub  := Loop_Sub A;
  s0_full := fun x y ox oy f => I;
  s0_rep  := fun x => (x; @eq_refl A x);
  s0_iso  := fun x => iso_id;
  s0_uniq := fun x a f => to f
|}.

Theorem skeleton0_skeletal_forces_UIP
  (K : ∀ (C : Category) (S : Skeleton0 C), Skeletal (Sub C (s0_sub S))) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A.
  assert (loops : ∀ (x : A) (l : x = x), l = eq_refl).
  { intros x l.
    pose proof (K (DiscreteCat A) (LoopSkeleton0 A)
                  (x; @eq_refl A x) (x; l)
                  (Full_sub_iso (DiscreteCat A) (Loop_Sub A)
                     (fun _ _ _ _ _ => I) (@eq_refl A x) l iso_id)) as H.
    exact (match H in _ = w return (`2 w = @eq_refl A (`1 w))
           with eq_refl => eq_refl end). }
  intros x y p q; destruct p; symmetry; apply loops.
Qed.

(* * ** A skeletal 范畴 own skeleton （已译） *)

Program Definition Wide_Sub (C : Category) : Subcategory C := {|
  sobj := fun _ => poly_unit;
  shom := fun x y ox oy f => True
|}.

Section SkeletalOwnSkeleton.
#[local] Obligation Tactic := idtac.

Program Definition Skeleton_of_Skeletal {C : Category} (H : Skeletal C) :
  Skeleton C := {|
  skel_sub  := Wide_Sub C;
  skel_full := fun x y ox oy f => I;
  skel_rep  := fun x => (x; ttt);
  skel_iso  := fun x => iso_id;
  skel_uniq := _
|}.
Next Obligation.
  intros C H x a i.
  destruct a as [y oy]; simpl in *.
  destruct (H x y i).
  now destruct oy.
Qed.

End SkeletalOwnSkeleton.

Lemma DiscreteCat_Skeletal (A : Type) : Skeletal (DiscreteCat A).
Proof. intros x y f; exact (to f). Qed.

(* 相关说明。 （已译） *)

(* Skeletality IS invariant under 同构 范畴. The other
 half — that it is not invariant under 等价 — is
 [skeletality_is_not_equivalence_invariant] in
 Theory/Skeleton/Separation.v.（已译） *)

Theorem Skeletal_StrictCat_invariant {C D : Category}
        (i : C ≅[StrictCat] D) : Skeletal C → Skeletal D.
Proof.
  intro SC.
  destruct (iso_to_from i) as [eq_ob _].
  assert (E : ∀ d : D, fobj[to i] (fobj[from i] d) = d)
    by (intro d; exact (eq_ob d)).
  intros x y f.
  exact (eq_trans (eq_sym (E x))
           (eq_trans (f_equal (fobj[to i])
                        (SC (from i x) (from i y) (fobj_iso (from i) x y f)))
              (E y))).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
