Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Fractions.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/localization
    nLab:      https://ncatlab.org/nlab/show/calculus+of+fractions
    Book: Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
    Book: Gabriel, Zisman, Calculus of Fractions and Homotopy Theory,

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma iso_conj_inverse {D : Category} {X1 Y1 X2 Y2 : D}
  (p : X1 ≅ X2) (q : Y1 ≅ Y2)
  (a : X1 ~> Y1) (b : Y1 ~> X1) (a' : X2 ~> Y2) (b' : Y2 ~> X2)
  (Hba : b ∘ a ≈ id) (Ha'b' : a' ∘ b' ≈ id)
  (Ha : a ≈ from q ∘ a' ∘ to p) :
  b ≈ from p ∘ b' ∘ to q.
Proof.
  assert (Hac : a ∘ (from p ∘ b' ∘ to q) ≈ id).
  { rewrite Ha.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to p) (from p)).
    rewrite iso_to_from, id_left.
    rewrite (comp_assoc a' b').
    rewrite Ha'b', id_left.
    apply iso_from_to. }
  rewrite <- (id_left (from p ∘ b' ∘ to q)).
  rewrite <- Hba.
  rewrite <- comp_assoc.
  rewrite Hac.
  now rewrite id_right.
Qed.

(** ** Naturality spreads from the generators to every zig-zag word *)

Section FractionsWeak.

Context {C D : Category}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Fractions_weak_edge
  (G1 G2 : Fractions C ⟶ D) (iso : ∀ x : C, G1 x ≅ G2 x)
  (Hgen : ∀ (x y : C) (f : x ~{C}~> y),
     fmap[G1] (fmap[FractionsProj C] f)
       ≈ from (iso y) ∘ fmap[G2] (fmap[FractionsProj C] f) ∘ to (iso x))
  {x y : C} (e : ZEdge (WAll C) x y) :
  fmap[G1] (tlist_singleton e)
    ≈ from (iso y) ∘ fmap[G2] (tlist_singleton e) ∘ to (iso x).
Proof.
  destruct e as [f | [g w]].
  - exact (Hgen x y f).
  - exact (iso_conj_inverse (iso y) (iso x)
             (fmap[G1] (zfwd (WAll C) g)) (fmap[G1] (zbwd (WAll C) g w))
             (fmap[G2] (zfwd (WAll C) g)) (fmap[G2] (zbwd (WAll C) g w))
             (zbwd_zfwd_functor (WAll C) G1 g w)
             (zfwd_zbwd_functor (WAll C) G2 g w)
             (Hgen y x g)).
Qed.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Fractions_weak_word
  (G1 G2 : Fractions C ⟶ D) (iso : ∀ x : C, G1 x ≅ G2 x)
  (Hgen : ∀ (x y : C) (f : x ~{C}~> y),
     fmap[G1] (fmap[FractionsProj C] f)
       ≈ from (iso y) ∘ fmap[G2] (fmap[FractionsProj C] f) ∘ to (iso x)) :
  ∀ (x y : C) (u : x ~{Fractions C}~> y),
    fmap[G1] u ≈ from (iso y) ∘ fmap[G2] u ∘ to (iso x).
Proof.
  intros x y u.
  induction u as [| a b e rest IH].
  - rewrite !fmap_id, id_right.
    now rewrite iso_from_to.
  - assert (Hu : (e ::: rest)
                 = @compose (Fractions C) a b y rest (tlist_singleton e))
      by apply tlist_app_cons.
    rewrite Hu, !fmap_comp.
    rewrite IH, (Fractions_weak_edge G1 G2 iso Hgen e).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite !comp_assoc.
    apply compose_respects; [ | reflexivity ].
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity | ].
    rewrite comp_assoc.
    now rewrite iso_to_from, id_left.
Qed.

End FractionsWeak.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Fractions_proj_epic_weak {C D : Category} (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_Setoid (Fractions C) D) L L'.
Proof.
  destruct E as [iso Hn].
  exists iso.
  exact (Fractions_weak_word L L' iso Hn).
Qed.

(** ** The universal property, at [Functor_Setoid] strength *)

Section FractionsUMPWeak.

Context {C D : Category}.
Variable Dg : IsGroupoid D.
Variable F : C ⟶ D.

Let Finv := fun (x y : C) (f : x ~> y) => Dg (F x) (F y) (fmap[F] f).

(* Existence is free: the strict factorization of [Construction/Fractions.v]
   pushed forward along [strict_equiv_implies_fun_equiv]. *)

Lemma FractionsLift_factors_weak :
  @equiv _ (@Functor_Setoid C D) F (FractionsLift F Finv ◯ FractionsProj C).
Proof.
  symmetry.
  apply strict_equiv_implies_fun_equiv.
  exact (FractionsLift_factors F Finv).
Qed.

Lemma FractionsLift_unique_weak (L : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :
  @equiv _ (@Functor_Setoid (Fractions C) D) (FractionsLift F Finv) L.
Proof.
  apply Fractions_proj_epic_weak.
  transitivity F.
  - symmetry; exact FractionsLift_factors_weak.
  - exact E.
Qed.

(* Riehl 4.1.15, left half, in the shape [universal_arrow_from_UMP] consumes:
   the same [Unique] record as [Fractions_UMP_groupoid], over
   [Functor_Setoid] in both positions instead of [Functor_StrictEq_Setoid]. *)

Definition Fractions_UMP_weak :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :=
  @Build_Unique _ (@Functor_Setoid (Fractions C) D) _
    (FractionsLift F Finv)
    FractionsLift_factors_weak
    FractionsLift_unique_weak.

End FractionsUMPWeak.
