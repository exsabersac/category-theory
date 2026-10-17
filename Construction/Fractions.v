Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Groupoid.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Construction.Quotient.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/calculus+of+fractions
    nLab:      https://ncatlab.org/nlab/show/localization
    nLab:      https://ncatlab.org/nlab/show/core
    Wikipedia: https://en.wikipedia.org/wiki/Localization_of_a_category
    Book: Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
    Book: Gabriel, Zisman, Calculus of Fractions and Homotopy Theory,
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Transporting a two-sided inverse along object equalities: if [a] and [a']
   correspond under [hom_cast], so do their inverses. *)
Lemma hom_cast_inverse {D : Category} {A B A' B' : D}
  (α : A = A') (β : B = B')
  (a : A ~> B) (b : B ~> A) (a' : A' ~> B') (b' : B' ~> A')
  (Hab : a ∘ b ≈ id) (Hb'a' : b' ∘ a' ≈ id)
  (Haa' : hom_cast α β a ≈ a') :
  hom_cast β α b ≈ b'.
Proof.
  destruct α, β.
  change (hom_cast eq_refl eq_refl a) with a in Haa'.
  change (hom_cast eq_refl eq_refl b) with b.
  rewrite Haa' in Hab.
  exact (comp_inverse_unique a' b b' Hab Hb'a').
Qed.

(* A [hom_cast] agreement read backwards. *)
Lemma hom_cast_sym {D : Category} {x y x' y' : D} (ex : x = x') (ey : y = y')
  (f : x ~> y) (g : x' ~> y') :
  hom_cast ex ey f ≈ g → hom_cast (eq_sym ex) (eq_sym ey) g ≈ f.
Proof. destruct ex, ey; intro H; now symmetry. Qed.

Section FracZigZag.

Context {C : Category}.

Variable W : ∀ x y : C, (x ~> y) → Type.

(* An edge of the glued quiver. *)
Definition ZEdge (x y : C) : Type :=
  ((x ~> y) + { f : y ~> x & W y x f })%type.

Definition ZEdge_equiv {x y : C} (a b : ZEdge x y) : Type :=
  match a, b with
  | inl f, inl g => f ≈ g
  | inr f, inr g => projT1 f ≈ projT1 g
  | _, _ => False
  end.

#[local] Instance ZEdge_equiv_Equivalence {x y : C} :
  Equivalence (@ZEdge_equiv x y).
Proof.
  constructor.
  - intros [f|[f w]]; simpl; reflexivity.
  - intros [f|[f w]] [g|[g v]] H; simpl in *;
      solve [ destruct H | now symmetry ].
  - intros [f|[f w]] [g|[g v]] [h|[h u]] H1 H2; simpl in *;
      solve [ destruct H1 | destruct H2 | now transitivity g ].
Qed.

Program Definition ZQuiver : Quiver := {|
  nodes := @obj C;
  edges := ZEdge;
  edgeset := fun x y => {| equiv := @ZEdge_equiv x y |}
|}.

Definition FreeZigZag : Category := FreeOnQuiver ZQuiver.

Definition zfwd {x y : C} (f : x ~> y) : x ~{FreeZigZag}~> y :=
  tlist_singleton (inl f).

Definition zbwd {x y : C} (f : x ~> y) (w : W x y f) : y ~{FreeZigZag}~> x :=
  tlist_singleton (inr (existT _ f w)).

Lemma zsingleton_respects {x y : C} (a b : ZEdge x y) :
  ZEdge_equiv a b →
  @equiv _ (@homset FreeZigZag x y) (tlist_singleton a) (tlist_singleton b).
Proof.
  intro H.
  unfold tlist_singleton; simpl;
    unfold tlist_quiver_equiv, tlist'_quiver_equiv.
  exists eq_refl; [ exact H | reflexivity ].
Qed.

Lemma zfwd_respects {x y : C} (f g : x ~> y) :
  f ≈ g → @equiv _ (@homset FreeZigZag x y) (zfwd f) (zfwd g).
Proof. apply (zsingleton_respects (inl f) (inl g)). Qed.

Lemma zbwd_respects {x y : C} (f g : x ~> y) (v : W x y f) (w : W x y g) :
  f ≈ g → @equiv _ (@homset FreeZigZag y x) (zbwd f v) (zbwd g w).
Proof.
  apply (zsingleton_respects (inr (existT _ f v)) (inr (existT _ g w))).
Qed.

(* The generating relations. *)
Inductive ZRel : ∀ x y : C,
    (x ~{FreeZigZag}~> y) → (x ~{FreeZigZag}~> y) → Type :=
  | zr_id (x : C) : ZRel x x (zfwd (@id C x)) (@id FreeZigZag x)
  | zr_comp {x y z : C} (f : x ~> y) (g : y ~> z) :
      ZRel x z (zfwd g ∘ zfwd f) (zfwd (g ∘ f))
  | zr_inv_l {x y : C} (f : x ~> y) (w : W x y f) :
      ZRel x x (zbwd f w ∘ zfwd f) (@id FreeZigZag x)
  | zr_inv_r {x y : C} (f : x ~> y) (w : W x y f) :
      ZRel y y (zfwd f ∘ zbwd f w) (@id FreeZigZag y).

Definition FracZigZag : Category := QuotientCong FreeZigZag ZRel.

Definition ZigZagProj : C ⟶ FracZigZag :=
  Build_Functor C FracZigZag
    (fun x => x)
    (fun x y f => zfwd f)
    (fun x y f g Hfg => cc_equiv (zfwd_respects f g Hfg))
    (fun x => cc_gen (zr_id x))
    (fun x y z f g => cc_sym (cc_gen (zr_comp g f))).

(* Every W-morphism becomes invertible in the localization. *)
Definition ZigZagProj_inverts {x y : C} (f : x ~> y) (w : W x y f) :
  @IsIsomorphism FracZigZag x y (fmap[ZigZagProj] f) :=
  @Build_IsIsomorphism FracZigZag x y (fmap[ZigZagProj] f)
    (zbwd f w) (cc_gen (zr_inv_r f w)) (cc_gen (zr_inv_l f w)).

(* ...and so, symmetrically, does the formal inverse itself. *)
Definition zbwd_IsIso {x y : C} (f : x ~> y) (w : W x y f) :
  @IsIsomorphism FracZigZag y x (zbwd f w) :=
  @Build_IsIsomorphism FracZigZag y x (zbwd f w)
    (zfwd f) (cc_gen (zr_inv_l f w)) (cc_gen (zr_inv_r f w)).

(* The two cancellation equations, as they read after any functor out of the
   localization. *)
Lemma zbwd_zfwd_functor {D : Category} (K : FracZigZag ⟶ D)
  {x y : C} (f : x ~> y) (w : W x y f) :
  fmap[K] (zbwd f w) ∘ fmap[K] (zfwd f) ≈ id.
Proof.
  rewrite <- fmap_comp.
  transitivity (fmap[K] (@id FracZigZag x)).
  - apply fmap_respects; exact (cc_gen (zr_inv_l f w)).
  - apply fmap_id.
Qed.

Lemma zfwd_zbwd_functor {D : Category} (K : FracZigZag ⟶ D)
  {x y : C} (f : x ~> y) (w : W x y f) :
  fmap[K] (zfwd f) ∘ fmap[K] (zbwd f w) ≈ id.
Proof.
  rewrite <- fmap_comp.
  transitivity (fmap[K] (@id FracZigZag y)).
  - apply fmap_respects; exact (cc_gen (zr_inv_r f w)).
  - apply fmap_id.
Qed.

(** ** The universal property *)

Context {D : Category}.
Variable F : C ⟶ D.
Variable Winv : ∀ (x y : C) (f : x ~> y), W x y f →
  @IsIsomorphism D (F x) (F y) (fmap[F] f).

Definition winv {x y : C} (g : y ~> x) (w : W y x g) : F x ~{D}~> F y :=
  @two_sided_inverse D (F y) (F x) (fmap[F] g) (Winv y x g w).

Lemma winv_right {x y : C} (g : y ~> x) (w : W y x g) :
  fmap[F] g ∘ winv g w ≈ id.
Proof. exact (@is_right_inverse D _ _ _ (Winv y x g w)). Qed.

Lemma winv_left {x y : C} (g : y ~> x) (w : W y x g) :
  winv g w ∘ fmap[F] g ≈ id.
Proof. exact (@is_left_inverse D _ _ _ (Winv y x g w)). Qed.

Definition zump_edge {x y : C} (e : ZEdge x y) : F x ~{D}~> F y :=
  match e with
  | inl f => fmap[F] f
  | inr (existT _ g w) => winv g w
  end.

Lemma zump_edge_respects {x y : C} (a b : ZEdge x y) :
  ZEdge_equiv a b → zump_edge a ≈ zump_edge b.
Proof.
  destruct a as [f|[g w]], b as [f'|[g' w']]; simpl; intro H;
    try solve [ destruct H ].
  - now rewrite H.
  - apply (comp_inverse_unique (fmap[F] g')).
    + rewrite <- H; apply winv_right.
    + apply winv_left.
Qed.

Program Definition zump_qhom : QuiverHomomorphism ZQuiver (QuiverOfCat D) := {|
  fnodes := fun x => F x;
  fedgemap := fun x y e => zump_edge e
|}.
Next Obligation. repeat intro; now apply zump_edge_respects. Qed.

Definition zump_free : FreeZigZag ⟶ D := InducedFunctor ZQuiver zump_qhom.

Lemma zump_free_fwd {x y : C} (f : x ~> y) :
  fmap[zump_free] (zfwd f) ≈ fmap[F] f.
Proof. simpl; apply id_left. Qed.

Lemma zump_free_bwd {x y : C} (f : x ~> y) (w : W x y f) :
  fmap[zump_free] (zbwd f w) ≈ winv f w.
Proof. simpl; apply id_left. Qed.

(* [zump_free] merges every generating relation, hence (by [cc_kernel],
   inside [QuotientCongLift]) the whole generated congruence. *)
Lemma zump_merges : ∀ (x y : C) (a b : x ~{FreeZigZag}~> y),
  ZRel x y a b → fmap[zump_free] a ≈ fmap[zump_free] b.
Proof.
  intros x y a b H; destruct H.
  - now rewrite zump_free_fwd, !fmap_id.
  - rewrite fmap_comp, !zump_free_fwd.
    now rewrite fmap_comp.
  - now rewrite fmap_comp, zump_free_bwd, zump_free_fwd, fmap_id, winv_left.
  - now rewrite fmap_comp, zump_free_fwd, zump_free_bwd, fmap_id, winv_right.
Qed.

(* The induced functor out of the localization. *)
Definition ZigZagLift : FracZigZag ⟶ D :=
  @QuotientCongLift FreeZigZag D ZRel zump_free zump_merges.

Lemma ZigZagLift_fwd {x y : C} (f : x ~> y) :
  fmap[ZigZagLift] (fmap[ZigZagProj] f) ≈ fmap[F] f.
Proof. exact (zump_free_fwd f). Qed.

Lemma ZigZagLift_bwd {x y : C} (f : x ~> y) (w : W x y f) :
  fmap[ZigZagLift] (zbwd f w) ≈ winv f w.
Proof. exact (zump_free_bwd f w). Qed.

(* The factorization, as one equality of functors in [StrictCat]. *)
Lemma ZigZagLift_factors :
  @equiv _ (@Functor_StrictEq_Setoid C D) (ZigZagLift ◯ ZigZagProj) F.
Proof.
  apply (strict_of_hom_cast (ZigZagLift ◯ ZigZagProj) F (fun _ => eq_refl)).
  intros x y f; exact (ZigZagLift_fwd f).
Qed.

(** *** Uniqueness of the factorization *)

Lemma ZigZagLift_unique_edge (G : FracZigZag ⟶ D)
  (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
  (Hmor : ∀ (x y : C) (f : x ~{C}~> y),
      hom_cast (Hobj x) (Hobj y) (fmap[G] (fmap[ZigZagProj] f)) ≈ fmap[F] f)
  {x y : C} (e : ZEdge x y) :
  hom_cast (Hobj x) (Hobj y) (fmap[G] (tlist_singleton e))
    ≈ fmap[ZigZagLift] (tlist_singleton e).
Proof.
  destruct e as [f | [g w]].
  - transitivity (fmap[F] f).
    + exact (Hmor x y f).
    + symmetry; exact (ZigZagLift_fwd f).
  - unshelve eapply (hom_cast_inverse (Hobj y) (Hobj x)
                       (fmap[G] (zfwd g)) _
                       (fmap[ZigZagLift] (zfwd g)) _).
    + exact (zfwd_zbwd_functor G g w).
    + exact (zbwd_zfwd_functor ZigZagLift g w).
    + transitivity (fmap[F] g).
      * exact (Hmor y x g).
      * symmetry; exact (ZigZagLift_fwd g).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ZigZagLift_unique (G : FracZigZag ⟶ D)
  (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
  (Hmor : ∀ (x y : C) (f : x ~{C}~> y),
      hom_cast (Hobj x) (Hobj y) (fmap[G] (fmap[ZigZagProj] f)) ≈ fmap[F] f) :
  ∀ (x y : C) (u : x ~{FracZigZag}~> y),
    hom_cast (Hobj x) (Hobj y) (fmap[G] u) ≈ fmap[ZigZagLift] u.
Proof.
  intros x y u.
  induction u as [| a b e rest IH].
  - rewrite !fmap_id; apply hom_cast_id.
  - assert (Hu : (e ::: rest)
                 = @compose FracZigZag a b y rest (tlist_singleton e))
      by apply tlist_app_cons.
    rewrite Hu, !fmap_comp.
    rewrite <- (hom_cast_comp (Hobj a) (Hobj b) (Hobj y)
                  (fmap[G] rest) (fmap[G] (tlist_singleton e))).
    rewrite IH, (ZigZagLift_unique_edge G Hobj Hmor e).
    reflexivity.
Qed.

(* The same uniqueness, as one equality of functors in [StrictCat]. *)
Corollary ZigZagLift_unique_strict (G : FracZigZag ⟶ D)
  (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
  (Hmor : ∀ (x y : C) (f : x ~{C}~> y),
      hom_cast (Hobj x) (Hobj y) (fmap[G] (fmap[ZigZagProj] f)) ≈ fmap[F] f) :
  @equiv _ (@Functor_StrictEq_Setoid FracZigZag D) G ZigZagLift.
Proof.
  apply (strict_of_hom_cast G ZigZagLift Hobj).
  exact (ZigZagLift_unique G Hobj Hmor).
Qed.

End FracZigZag.

Arguments ZEdge {C} W x y.
Arguments ZQuiver {C} W.
Arguments FreeZigZag {C} W.
Arguments zfwd {C} W {x y} f.
Arguments zbwd {C} W {x y} f w.
Arguments ZRel {C} W x y _ _.
Arguments FracZigZag {C} W.
Arguments ZigZagProj {C} W.

(** * The category of fractions [C[C⁻¹]] *)

(* The class consisting of every morphism.  It is [Type]-valued because the
   generating relation [ZRel] is, and [unit] rather than [True] so that no
   [Prop]-elimination restriction can arise. *)
Definition WAll (C : Category) : ∀ x y : C, (x ~> y) → Type :=
  fun _ _ _ => unit.

Definition Fractions (C : Category) : Category := FracZigZag (WAll C).

Definition FractionsProj (C : Category) : C ⟶ Fractions C :=
  ZigZagProj (WAll C).

(* Every morphism of [C] becomes invertible in [C[C⁻¹]]. *)
Definition FractionsProj_inverts {C : Category} {x y : C} (f : x ~> y) :
  @IsIsomorphism (Fractions C) x y (fmap[FractionsProj C] f) :=
  ZigZagProj_inverts (WAll C) f tt.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition frac_IsIso_compose {E : Category} {x y z : E} {f : y ~> z} {g : x ~> y}
  (Hf : @IsIsomorphism E y z f) (Hg : @IsIsomorphism E x y g) :
  @IsIsomorphism E x z (f ∘ g).
Proof.
  unshelve eapply Build_IsIsomorphism.
  - exact (@two_sided_inverse E x y g Hg ∘ @two_sided_inverse E y z f Hf).
  - rewrite comp_assoc,
      <- (comp_assoc f g (@two_sided_inverse E x y g Hg)).
    rewrite (@is_right_inverse E x y g Hg), id_right.
    apply (@is_right_inverse E y z f Hf).
  - rewrite comp_assoc,
      <- (comp_assoc (@two_sided_inverse E x y g Hg)
                     (@two_sided_inverse E y z f Hf) f).
    rewrite (@is_left_inverse E y z f Hf), id_right.
    apply (@is_left_inverse E x y g Hg).
Defined.

Definition frac_IsIso_id {E : Category} (x : E) : @IsIsomorphism E x x id :=
  @Build_IsIsomorphism E x x id id (id_left id) (id_left id).

(*
   本节说明 Fractions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Fractions_IsGroupoid (C : Category) : IsGroupoid (Fractions C).
Proof.
  intros x y u.
  induction u as [| a b e rest IH].
  - exact (frac_IsIso_id (E:=Fractions C) y).
  - assert (Hu : (e ::: rest)
                 = @compose (Fractions C) a b y rest (tlist_singleton e))
      by apply tlist_app_cons.
    rewrite Hu.
    apply (frac_IsIso_compose IH).
    destruct e as [f | [g u]].
    + exact (ZigZagProj_inverts (WAll C) f tt).
    + exact (zbwd_IsIso (WAll C) g u).
Defined.

(** ** The universal property of [C[C⁻¹]] *)

Section FractionsUMP.

Context {C D : Category}.
Variable F : C ⟶ D.
Variable Finv : ∀ (x y : C) (f : x ~> y),
  @IsIsomorphism D (F x) (F y) (fmap[F] f).

Definition FractionsLift : Fractions C ⟶ D :=
  ZigZagLift (WAll C) F (fun x y f _ => Finv x y f).

Lemma FractionsLift_fwd {x y : C} (f : x ~> y) :
  fmap[FractionsLift] (fmap[FractionsProj C] f) ≈ fmap[F] f.
Proof. exact (ZigZagLift_fwd (WAll C) F (fun x y f _ => Finv x y f) f). Qed.

Lemma FractionsLift_factors :
  @equiv _ (@Functor_StrictEq_Setoid C D) (FractionsLift ◯ FractionsProj C) F.
Proof. exact (ZigZagLift_factors (WAll C) F (fun x y f _ => Finv x y f)). Qed.

Lemma FractionsLift_unique (G : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_StrictEq_Setoid C D) F (G ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D) FractionsLift G.
Proof.
  destruct (hom_cast_of_strict F (G ◯ FractionsProj C) E) as [Hobj Hmor].
  symmetry.
  exact (ZigZagLift_unique_strict (WAll C) F (fun x y f _ => Finv x y f) G
           (fun x => eq_sym (Hobj x))
           (fun x y f => hom_cast_sym (Hobj x) (Hobj y) _ _ (Hmor x y f))).
Qed.

Definition Fractions_UMP :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C)) :=
  @Build_Unique _ (@Functor_StrictEq_Setoid (Fractions C) D) _
    FractionsLift
    (symmetry FractionsLift_factors)
    FractionsLift_unique.

End FractionsUMP.

(** ** Riehl 4.1.15, the left half, at a groupoid target *)

(* Every functor into a groupoid inverts every morphism, so the hypothesis of
   [Fractions_UMP] is automatic there. *)
Definition Fractions_UMP_groupoid {C D : Category} (Dg : IsGroupoid D)
  (F : C ⟶ D) :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C)) :=
  Fractions_UMP F (fun x y f => Dg (F x) (F y) (fmap[F] f)).

(* The other half of the hom-set bijection: precomposition with the
   projection is injective on functors into a groupoid.  Two functors out of
   [C[C⁻¹]] that agree on [C] agree everywhere. *)
Corollary Fractions_proj_epic {C D : Category} (Dg : IsGroupoid D)
  (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_StrictEq_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D) L L'.
Proof.
  pose (U := Fractions_UMP_groupoid Dg (L ◯ FractionsProj C)).
  transitivity (unique_obj U).
  - symmetry; exact (uniqueness U L (reflexivity _)).
  - exact (uniqueness U L' E).
Qed.

(** ** The bridge to the free groupoid on a quiver *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FreeGroupoidToFractions (C : Category) :
  FreeGroupoid (QuiverOfCat C) ⟶ Fractions C :=
  FreeGroupoidFunctor (QuiverOfCat C) (Fractions_IsGroupoid C)
    (QuiverHomomorphismOfFunctor C (Fractions C) (FractionsProj C)).

(* It carries a positive generator to the image of that morphism of [C]. *)
Lemma FreeGroupoidToFractions_pos {C : Category} {x y : C} (f : x ~> y) :
  fmap[FreeGroupoidToFractions C] (fgpos (G:=QuiverOfCat C) f)
    ≈ fmap[FractionsProj C] f.
Proof.
  exact (FreeGroupoidFunctor_gen (QuiverOfCat C) (Fractions_IsGroupoid C)
           (QuiverHomomorphismOfFunctor C (Fractions C) (FractionsProj C)) f).
Qed.

(* ...and it is the identity on objects. *)
Lemma FreeGroupoidToFractions_obj {C : Category} (x : C) :
  fobj[FreeGroupoidToFractions C] x = x.
Proof. reflexivity. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem fractions_universal {C D : Category} (Dg : IsGroupoid D)
  (F : C ⟶ D) :
  { K : Fractions C ⟶ D &
  { Hobj : ∀ x : C, fobj[K] x = fobj[F] x &
    ((∀ (x y : C) (f : x ~> y),
        hom_cast (Hobj x) (Hobj y)
          (fmap[K] (fmap[FractionsProj C] f)) ≈ fmap[F] f) *
     (∀ (K' : Fractions C ⟶ D)
        (Hobj' : ∀ x : C, fobj[K'] x = fobj[F] x),
        (∀ (x y : C) (f : x ~> y),
           hom_cast (Hobj' x) (Hobj' y)
             (fmap[K'] (fmap[FractionsProj C] f)) ≈ fmap[F] f) →
        ∀ (x y : C) (u : x ~{Fractions C}~> y),
          hom_cast (Hobj' x) (Hobj' y) (fmap[K'] u)
            ≈ hom_cast (Hobj x) (Hobj y) (fmap[K] u)))%type } }.
Proof.
  pose (Finv := fun (x y : C) (f : x ~> y) => Dg (F x) (F y) (fmap[F] f)).
  exists (FractionsLift F Finv), (fun _ => eq_refl).
  split.
  - intros x y f; exact (FractionsLift_fwd F Finv f).
  - intros K' Hobj' Hgen x y u.
    exact (ZigZagLift_unique (WAll C) F (fun x y f _ => Finv x y f)
             K' Hobj' Hgen x y u).
Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition frac_restrict {C D : Category} (S : Fractions C ⟶ D) : C ⟶ D :=
  S ◯ FractionsProj C.

Lemma frac_restrict_recovers {C D : Category} (Dg : IsGroupoid D)
  (S : Fractions C ⟶ D) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (FractionsLift (frac_restrict S)
       (fun x y f => Dg _ _ (fmap[frac_restrict S] f))) S.
Proof.
  apply FractionsLift_unique.
  reflexivity.
Qed.

Lemma frac_extend_restrict {C D : Category} (F : C ⟶ D)
  (Finv : ∀ (x y : C) (f : x ~> y), @IsIsomorphism D (F x) (F y) (fmap[F] f)) :
  @equiv _ (@Functor_StrictEq_Setoid C D)
    (frac_restrict (FractionsLift F Finv)) F.
Proof. exact (FractionsLift_factors F Finv). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma FractionsProj_separates {C D : Category} (Dg : IsGroupoid D)
  (F : C ⟶ D) {x y : C} (f g : x ~> y)
  (H : fmap[F] f ≈ fmap[F] g → False) :
  @equiv _ (@homset (Fractions C) x y)
    (fmap[FractionsProj C] f) (fmap[FractionsProj C] g) → False.
Proof.
  intro E.
  apply H.
  pose (Finv := fun (a b : C) (h : a ~> b) => Dg (F a) (F b) (fmap[F] h)).
  rewrite <- (FractionsLift_fwd F Finv f), <- (FractionsLift_fwd F Finv g).
  now rewrite E.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FractionsProj_Faithful {C : Category} (Cg : IsGroupoid C) :
  Faithful (FractionsProj C).
Proof.
  unshelve econstructor.
  intros x y f g E.
  pose (Finv := fun (a b : C) (h : a ~> b) => Cg a b h).
  transitivity (fmap[FractionsLift (Id[C]) Finv] (fmap[FractionsProj C] f)).
  - symmetry; exact (FractionsLift_fwd (Id[C]) Finv f).
  - rewrite E; exact (FractionsLift_fwd (Id[C]) Finv g).
Defined.

(* An unconditional instance of that: the core of any category is a groupoid
   (Structure/Groupoid.v's [core_is_groupoid]), so localizing a core merges
   nothing. *)
Definition FractionsProj_Faithful_core (C : Category) :
  Faithful (FractionsProj (Groupoid C)) :=
  FractionsProj_Faithful (core_is_groupoid C).
