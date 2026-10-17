Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Maps of adjunctions *)

(*
   nLab: https://ncatlab.org/nlab/show/mate

   本文件给出 Map 相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Map 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma id_cast_sym_trans {X : Category} {u v w : X} (p : u = v) (q : v = w) :
  id_cast (eq_sym (eq_trans p q))
    ≈ id_cast (eq_sym p) ∘ id_cast (eq_sym q).
Proof. destruct p, q; cat. Qed.

Lemma fmap_id_cast_sym {X Y : Category} (G : X ⟶ Y) {u v : X} (e : u = v) :
  id_cast (eq_sym (f_equal G e)) ≈ fmap[G] (id_cast (eq_sym e)).
Proof. destruct e; simpl; symmetry; apply fmap_id. Qed.

(* * ** The engine: comparison isomorphisms three-way 等价 （已译） *)

(*
   本节说明 Map 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MapCompare.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (al : ∀ x : D, K (F x) ≅ F' (L x)).
Context (be : ∀ a : C, L (U a) ≅ U' (K a)).

Notation "⌊ f ⌋"  := (to   (@adj _ _ _ _ A  _ _) f).
Notation "⌈ f ⌉"  := (from (@adj _ _ _ _ A  _ _) f).
Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).
Notation "'η²' x" := (@unit   _ _ _ _ A' x) (at level 9).
Notation "'ε²' a" := (@counit _ _ _ _ A' a) (at level 9).

(* Naturality of the two comparison families. *)

Definition CompareLeftNat : Type :=
  ∀ (x y : D) (f : x ~> y),
    to (al y) ∘ fmap[K] (fmap[F] f) ≈ fmap[F'] (fmap[L] f) ∘ to (al x).

Definition CompareRightNat : Type :=
  ∀ (a b : C) (f : a ~> b),
    to (be b) ∘ fmap[L] (fmap[U] f) ≈ fmap[U'] (fmap[K] f) ∘ to (be a).

(* An invertible natural family is natural in the inverse direction too. *)
Lemma compare_left_nat_from (Hal : CompareLeftNat) (x y : D) (f : x ~> y) :
  from (al y) ∘ fmap[F'] (fmap[L] f) ≈ fmap[K] (fmap[F] f) ∘ from (al x).
Proof.
  transitivity
    (from (al y) ∘ (fmap[F'] (fmap[L] f) ∘ (to (al x) ∘ from (al x)))).
  { now rewrite iso_to_from, id_right. }
  rewrite (comp_assoc (fmap[F'] (fmap[L] f))).
  rewrite <- (Hal x y f).
  rewrite comp_assoc, comp_assoc, iso_from_to.
  now rewrite id_left.
Qed.

(* Mac Lane's display (3), quantified over every transposable arrow. *)
Definition MapAdjHom : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    ⌊ fmap[K] k ∘ from (al x) ⌋² ≈ to (be a) ∘ fmap[L] ⌊ k ⌋.

(* 相关说明。 （已译） *)
Definition MapAdjUnit : Type :=
  ∀ x : D,
    to (be (F x)) ∘ fmap[L] (η x) ≈ fmap[U'] (from (al x)) ∘ η² (L x).

(* Mac Lane's Kε = ε'K, likewise. *)
Definition MapAdjCounit : Type :=
  ∀ a : C,
    fmap[K] (ε a) ∘ from (al (U a)) ≈ ε² (K a) ∘ fmap[F'] (to (be a)).

(* Mac Lane's own argument: chase the identity arrow around display (3). *)
Lemma map_hom_to_unit : MapAdjHom → MapAdjUnit.
Proof.
  intros H x.
  pose proof (H x (F x) id) as Hx.
  rewrite fmap_id, id_left in Hx.
  rewrite (to_adj_unit (H:=A')) in Hx.
  now rewrite <- Hx.
Qed.

Lemma map_unit_to_hom : CompareRightNat → MapAdjUnit → MapAdjHom.
Proof.
  intros Hbe H x a k.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite <- (H x : _ ≈ _).
  rewrite comp_assoc.
  rewrite <- (Hbe (F x) a k).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  now rewrite <- (to_adj_unit (H:=A)).
Qed.

(* 相关说明。 （已译） *)
Lemma map_hom_to_counit : MapAdjHom → MapAdjCounit.
Proof.
  intros H a.
  pose proof (H (U a) a (ε a)) as Ha.
  rewrite (to_adj_counit (H:=A)) in Ha.
  rewrite fmap_id, id_right in Ha.
  apply (snd (adj_univ (H:=A') _ _)) in Ha.
  rewrite Ha.
  now rewrite (from_adj_counit (H:=A')).
Qed.

Lemma map_counit_to_hom : CompareLeftNat → MapAdjCounit → MapAdjHom.
Proof.
  intros Hal H x a k.
  apply (fst (adj_univ (H:=A') _ _)).
  rewrite (from_adj_counit (H:=A')).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (H a : _ ≈ _).
  rewrite <- comp_assoc.
  rewrite (compare_left_nat_from Hal _ _ ⌊ k ⌋).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (from_adj_counit (H:=A)).
  now rewrite (to_adj_comp_law (H:=A)).
Qed.

Theorem map_adj_hom_iff_unit :
  CompareRightNat → (MapAdjHom ↔ MapAdjUnit).
Proof.
  intros Hbe; split; [ exact map_hom_to_unit | exact (map_unit_to_hom Hbe) ].
Qed.

Theorem map_adj_hom_iff_counit :
  CompareLeftNat → (MapAdjHom ↔ MapAdjCounit).
Proof.
  intros Hal; split;
    [ exact map_hom_to_counit | exact (map_counit_to_hom Hal) ].
Qed.

Theorem map_adj_unit_iff_counit :
  CompareLeftNat → CompareRightNat → (MapAdjUnit ↔ MapAdjCounit).
Proof.
  intros Hal Hbe; split; intro H.
  - exact (map_hom_to_counit (map_unit_to_hom Hbe H)).
  - exact (map_hom_to_unit (map_counit_to_hom Hal H)).
Qed.

End MapCompare.

(* * ** The two squares, at Leibniz equality 对象 （已译） *)

Section StrictSquares.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D}.
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record AdjSquares : Type := {
  sq_K : C ⟶ C';
  sq_L : D ⟶ D';

  sq_left : ∀ x : D, sq_K (F x) = F' (sq_L x);
  sq_left_nat : ∀ (x y : D) (f : x ~> y),
    id_cast (sq_left y) ∘ fmap[sq_K] (fmap[F] f)
      ≈ fmap[F'] (fmap[sq_L] f) ∘ id_cast (sq_left x);

  sq_right : ∀ a : C, sq_L (U a) = U' (sq_K a);
  sq_right_nat : ∀ (a b : C) (f : a ~> b),
    id_cast (sq_right b) ∘ fmap[sq_L] (fmap[U] f)
      ≈ fmap[U'] (fmap[sq_K] f) ∘ id_cast (sq_right a)
}.

(* The comparison isomorphisms engine 所消耗. （已译） *)

Definition sq_al (S : AdjSquares) (x : D) : sq_K S (F x) ≅ F' (sq_L S x)
  := id_cast_iso (sq_left S x).

Definition sq_be (S : AdjSquares) (a : C) : sq_L S (U a) ≅ U' (sq_K S a)
  := id_cast_iso (sq_right S a).

(* The 复合 对象 equalities Mac Lane's Lη = η'L Kε = ε'K use. （已译） *)

Definition sq_unit_eq (S : AdjSquares) (x : D)
  : sq_L S (U (F x)) = U' (F' (sq_L S x))
  := eq_trans (sq_right S (F x)) (f_equal U' (sq_left S x)).

Definition sq_counit_eq (S : AdjSquares) (a : C)
  : sq_K S (F (U a)) = F' (U' (sq_K S a))
  := eq_trans (sq_left S (U a)) (f_equal F' (sq_right S a)).

End StrictSquares.

(* 相关说明。 （已译） *)

Section StrictMap.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').

(* Display (3), quantified over every transposable arrow. *)
Definition SquaresHom (S : @AdjSquares C D F U C' D' F' U') : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    to (@adj _ _ _ _ A' _ _)
       (fmap[sq_K S] k ∘ id_cast (eq_sym (sq_left S x)))
      ≈ id_cast (sq_right S a) ∘ fmap[sq_L S] (to (@adj _ _ _ _ A _ _) k).

Definition SquaresUnit (S : @AdjSquares C D F U C' D' F' U') : Type :=
  ∀ x : D,
    id_cast (sq_right S (F x)) ∘ fmap[sq_L S] (@unit _ _ _ _ A x)
      ≈ fmap[U'] (id_cast (eq_sym (sq_left S x)))
          ∘ @unit _ _ _ _ A' (sq_L S x).

Definition SquaresCounit (S : @AdjSquares C D F U C' D' F' U') : Type :=
  ∀ a : C,
    fmap[sq_K S] (@counit _ _ _ _ A a) ∘ id_cast (eq_sym (sq_left S (U a)))
      ≈ @counit _ _ _ _ A' (sq_K S a) ∘ fmap[F'] (id_cast (sq_right S a)).

(* 相关说明。 （已译） *)

Lemma squares_hom_is_generic (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom S = MapAdjHom A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S).
Proof. reflexivity. Qed.

Lemma squares_unit_is_generic (S : @AdjSquares C D F U C' D' F' U') :
  SquaresUnit S = MapAdjUnit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S).
Proof. reflexivity. Qed.

Lemma squares_counit_is_generic (S : @AdjSquares C D F U C' D' F' U') :
  SquaresCounit S = MapAdjCounit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S).
Proof. reflexivity. Qed.

Lemma sq_left_CompareLeftNat (S : @AdjSquares C D F U C' D' F' U') :
  CompareLeftNat (sq_K S) (sq_L S) (sq_al S).
Proof. exact (sq_left_nat S). Qed.

Lemma sq_right_CompareRightNat (S : @AdjSquares C D F U C' D' F' U') :
  CompareRightNat (sq_K S) (sq_L S) (sq_be S).
Proof. exact (sq_right_nat S). Qed.

(* Proposition 1, in three named biconditionals. *)

Theorem squares_hom_iff_unit (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom S ↔ SquaresUnit S.
Proof.
  exact (map_adj_hom_iff_unit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S)
           (sq_right_CompareRightNat S)).
Qed.

Theorem squares_hom_iff_counit (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom S ↔ SquaresCounit S.
Proof.
  exact (map_adj_hom_iff_counit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S)
           (sq_left_CompareLeftNat S)).
Qed.

Theorem map_of_adjunctions_unit_iff_counit
  (S : @AdjSquares C D F U C' D' F' U') :
  SquaresUnit S ↔ SquaresCounit S.
Proof.
  exact (map_adj_unit_iff_counit A A' (sq_K S) (sq_L S) (sq_al S) (sq_be S)
           (sq_left_CompareLeftNat S) (sq_right_CompareRightNat S)).
Qed.

(* 相关说明。 （已译） *)

Theorem squares_unit_fused (S : @AdjSquares C D F U C' D' F' U') :
  SquaresUnit S
    ↔ (∀ x : D,
         id_cast (sq_unit_eq S x) ∘ fmap[sq_L S] (@unit _ _ _ _ A x)
           ≈ @unit _ _ _ _ A' (sq_L S x)).
Proof.
  unfold SquaresUnit, sq_unit_eq; split; intros H x.
  - rewrite <- id_cast_trans.
    rewrite <- comp_assoc.
    rewrite (H x).
    rewrite <- fmap_id_cast.
    rewrite comp_assoc, <- fmap_comp, id_cast_inv_r, fmap_id.
    now rewrite id_left.
  - rewrite <- (H x).
    rewrite <- id_cast_trans.
    rewrite <- comp_assoc.
    rewrite <- fmap_id_cast.
    rewrite comp_assoc, <- fmap_comp, id_cast_inv_l, fmap_id.
    now rewrite id_left.
Qed.

Theorem squares_counit_fused (S : @AdjSquares C D F U C' D' F' U') :
  SquaresCounit S
    ↔ (∀ a : C,
         fmap[sq_K S] (@counit _ _ _ _ A a)
           ≈ @counit _ _ _ _ A' (sq_K S a) ∘ id_cast (sq_counit_eq S a)).
Proof.
  unfold SquaresCounit, sq_counit_eq; split; intros H a.
  - rewrite <- id_cast_trans.
    rewrite <- fmap_id_cast.
    rewrite comp_assoc.
    rewrite <- (H a).
    rewrite <- comp_assoc, id_cast_inv_l.
    now rewrite id_right.
  - rewrite (H a).
    rewrite <- id_cast_trans.
    rewrite <- fmap_id_cast.
    rewrite <- !comp_assoc, id_cast_inv_r.
    now rewrite id_right.
Qed.

(* 相关说明。 （已译） *)
Record MapOfAdjunctions : Type := {
  map_squares : @AdjSquares C D F U C' D' F' U';
  map_hom : SquaresHom map_squares
}.

Definition map_K (M : MapOfAdjunctions) : C ⟶ C' := sq_K (map_squares M).
Definition map_L (M : MapOfAdjunctions) : D ⟶ D' := sq_L (map_squares M).

Definition map_unit (M : MapOfAdjunctions) : SquaresUnit (map_squares M) :=
  fst (squares_hom_iff_unit (map_squares M)) (map_hom M).

Definition map_counit (M : MapOfAdjunctions) : SquaresCounit (map_squares M)
  := fst (squares_hom_iff_counit (map_squares M)) (map_hom M).

Definition MapOfAdjunctions_of_unit
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresUnit S)
  : MapOfAdjunctions :=
  {| map_squares := S; map_hom := snd (squares_hom_iff_unit S) H |}.

Definition MapOfAdjunctions_of_counit
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresCounit S)
  : MapOfAdjunctions :=
  {| map_squares := S; map_hom := snd (squares_hom_iff_counit S) H |}.

(* 相关说明。 （已译） *)

Example map_of_unit_squares
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresUnit S) :
  map_squares (MapOfAdjunctions_of_unit S H) = S.
Proof. reflexivity. Qed.

Example map_of_counit_squares
  (S : @AdjSquares C D F U C' D' F' U') (H : SquaresCounit S) :
  map_squares (MapOfAdjunctions_of_counit S H) = S.
Proof. reflexivity. Qed.

End StrictMap.

(** ** Identity and composition *)

Section SquaresIdComp.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D}.
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}.

Program Definition AdjSquares_id : @AdjSquares C D F U C D F U := {|
  sq_K := Id[C];
  sq_L := Id[D];
  sq_left  := fun x => eq_refl;
  sq_right := fun a => eq_refl
|}.

Program Definition AdjSquares_compose
  (S : @AdjSquares C D F U C' D' F' U')
  (T : @AdjSquares C' D' F' U' C'' D'' F'' U'')
  : @AdjSquares C D F U C'' D'' F'' U'' := {|
  sq_K := sq_K T ◯ sq_K S;
  sq_L := sq_L T ◯ sq_L S;
  sq_left := fun x =>
    eq_trans (f_equal (sq_K T) (sq_left S x)) (sq_left T (sq_L S x));
  sq_right := fun a =>
    eq_trans (f_equal (sq_L T) (sq_right S a)) (sq_right T (sq_K S a))
|}.
Next Obligation.
  rewrite <- !id_cast_trans.
  rewrite <- !fmap_id_cast.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (sq_left_nat S).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite (sq_left_nat T).
  now rewrite <- comp_assoc.
Qed.
Next Obligation.
  rewrite <- !id_cast_trans.
  rewrite <- !fmap_id_cast.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (sq_right_nat S).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite (sq_right_nat T).
  now rewrite <- comp_assoc.
Qed.

End SquaresIdComp.

Section MapIdComp.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}
        (A'' : F'' ⊣ U'').

Program Definition MapOfAdjunctions_id : MapOfAdjunctions A A := {|
  map_squares := AdjSquares_id
|}.
Next Obligation.
  intros x a k; simpl.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.

Program Definition MapOfAdjunctions_compose
  (M : MapOfAdjunctions A A') (N : MapOfAdjunctions A' A'')
  : MapOfAdjunctions A A'' := {|
  map_squares :=
    AdjSquares_compose (map_squares A A' M) (map_squares A' A'' N)
|}.
Next Obligation.
  intros x a k; simpl.
  rewrite id_cast_sym_trans.
  rewrite fmap_id_cast_sym.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (map_hom A' A'' N (sq_L (map_squares A A' M) x)
             (sq_K (map_squares A A' M) a)
             (fmap[sq_K (map_squares A A' M)] k
                ∘ id_cast (eq_sym (sq_left (map_squares A A' M) x)))).
  rewrite (map_hom A A' M x a k).
  rewrite fmap_comp.
  rewrite fmap_id_cast.
  rewrite comp_assoc.
  now rewrite id_cast_trans.
Qed.

(* 相关说明。 （已译） *)

Example map_id_K : map_K A A MapOfAdjunctions_id = Id[C].
Proof. reflexivity. Qed.

Example map_id_L : map_L A A MapOfAdjunctions_id = Id[D].
Proof. reflexivity. Qed.

Example map_id_left_square (x : D) :
  sq_left (map_squares A A MapOfAdjunctions_id) x = eq_refl.
Proof. reflexivity. Qed.

Example map_compose_K (M : MapOfAdjunctions A A') (N : MapOfAdjunctions A' A'')
  : map_K A A'' (MapOfAdjunctions_compose M N)
      = map_K A' A'' N ◯ map_K A A' M.
Proof. reflexivity. Qed.

Example map_compose_L (M : MapOfAdjunctions A A') (N : MapOfAdjunctions A' A'')
  : map_L A A'' (MapOfAdjunctions_compose M N)
      = map_L A' A'' N ◯ map_L A A' M.
Proof. reflexivity. Qed.

End MapIdComp.

(* * ** The ≈ reading: squares up natural 同构 （已译） *)

Section WeakSquares.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D}.
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'}.

(* [≈] on functors is [Functor_Setoid], which IS natural isomorphism. *)
Record WeakAdjSquares : Type := {
  wsq_K : C ⟶ C';
  wsq_L : D ⟶ D';
  wsq_left  : wsq_K ◯ F ≈ F' ◯ wsq_L;
  wsq_right : wsq_L ◯ U ≈ U' ◯ wsq_K
}.

Definition wsq_al (W : WeakAdjSquares) (x : D)
  : wsq_K W (F x) ≅ F' (wsq_L W x) := `1 (wsq_left W) x.

Definition wsq_be (W : WeakAdjSquares) (a : C)
  : wsq_L W (U a) ≅ U' (wsq_K W a) := `1 (wsq_right W) a.

Lemma wsq_left_nat (W : WeakAdjSquares) :
  CompareLeftNat (wsq_K W) (wsq_L W) (wsq_al W).
Proof.
  intros x y f.
  rewrite (`2 (wsq_left W) x y f).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Lemma wsq_right_nat (W : WeakAdjSquares) :
  CompareRightNat (wsq_K W) (wsq_L W) (wsq_be W).
Proof.
  intros a b f.
  rewrite (`2 (wsq_right W) a b f).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(* A strict square is in particular a ≈ one. *)

Lemma strict_weak_left (S : @AdjSquares C D F U C' D' F' U') :
  ∀ (x y : D) (f : x ~> y),
    fmap[sq_K S] (fmap[F] f)
      ≈ id_cast (eq_sym (sq_left S y)) ∘ fmap[F'] (fmap[sq_L S] f)
          ∘ id_cast (sq_left S x).
Proof.
  intros x y f.
  rewrite <- comp_assoc.
  rewrite <- (sq_left_nat S x y f).
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_left.
Qed.

Lemma strict_weak_right (S : @AdjSquares C D F U C' D' F' U') :
  ∀ (a b : C) (f : a ~> b),
    fmap[sq_L S] (fmap[U] f)
      ≈ id_cast (eq_sym (sq_right S b)) ∘ fmap[U'] (fmap[sq_K S] f)
          ∘ id_cast (sq_right S a).
Proof.
  intros a b f.
  rewrite <- comp_assoc.
  rewrite <- (sq_right_nat S a b f).
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_left.
Qed.

Definition WeakAdjSquares_of_AdjSquares
  (S : @AdjSquares C D F U C' D' F' U') : WeakAdjSquares := {|
  wsq_K := sq_K S;
  wsq_L := sq_L S;
  wsq_left  := existT _ (fun x => id_cast_iso (sq_left S x))
                        (strict_weak_left S);
  wsq_right := existT _ (fun a => id_cast_iso (sq_right S a))
                        (strict_weak_right S)
|}.

End WeakSquares.

Section WeakMap.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').

Definition WeakSquaresHom (W : @WeakAdjSquares C D F U C' D' F' U') : Type :=
  MapAdjHom A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W).

Definition WeakSquaresUnit (W : @WeakAdjSquares C D F U C' D' F' U') : Type :=
  MapAdjUnit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W).

Definition WeakSquaresCounit (W : @WeakAdjSquares C D F U C' D' F' U')
  : Type := MapAdjCounit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W).

Theorem weak_hom_iff_unit (W : @WeakAdjSquares C D F U C' D' F' U') :
  WeakSquaresHom W ↔ WeakSquaresUnit W.
Proof.
  exact (map_adj_hom_iff_unit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W)
           (wsq_right_nat W)).
Qed.

Theorem weak_hom_iff_counit (W : @WeakAdjSquares C D F U C' D' F' U') :
  WeakSquaresHom W ↔ WeakSquaresCounit W.
Proof.
  exact (map_adj_hom_iff_counit A A' (wsq_K W) (wsq_L W) (wsq_al W) (wsq_be W)
           (wsq_left_nat W)).
Qed.

Theorem weak_unit_iff_counit (W : @WeakAdjSquares C D F U C' D' F' U') :
  WeakSquaresUnit W ↔ WeakSquaresCounit W.
Proof.
  exact (map_adj_unit_iff_counit A A' (wsq_K W) (wsq_L W) (wsq_al W)
           (wsq_be W) (wsq_left_nat W) (wsq_right_nat W)).
Qed.

Record WeakMapOfAdjunctions : Type := {
  wmap_squares : @WeakAdjSquares C D F U C' D' F' U';
  wmap_hom : WeakSquaresHom wmap_squares
}.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strict_hom_is_weak_hom (S : @AdjSquares C D F U C' D' F' U') :
  SquaresHom A A' S = WeakSquaresHom (WeakAdjSquares_of_AdjSquares S).
Proof. reflexivity. Qed.

Definition WeakMapOfAdjunctions_of_MapOfAdjunctions
  (M : MapOfAdjunctions A A') : WeakMapOfAdjunctions := {|
  wmap_squares := WeakAdjSquares_of_AdjSquares (map_squares A A' M);
  wmap_hom := map_hom A A' M
|}.

End WeakMap.

(* * ** The 恒等-bounding-函子 case IS Adjunction/Conjugate.v （已译） *)

Section ConjugateCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {F' : D ⟶ C} {U' : C ⟶ D} (A' : F' ⊣ U').
Context (al : ∀ x : D, F x ≅ F' x).
Context (be : ∀ a : C, U a ≅ U' a).
Context (Hal : CompareLeftNat (F:=F) (F':=F') Id[C] Id[D] al).
Context (Hbe : CompareRightNat (U:=U) (U':=U') Id[C] Id[D] be).

Program Definition conj_sigma : F' ⟹ F := {|
  transform := fun x => from (al x)
|}.
Next Obligation.
  symmetry; exact (compare_left_nat_from Id[C] Id[D] al Hal x y f).
Qed.
Next Obligation.
  exact (compare_left_nat_from Id[C] Id[D] al Hal x y f).
Qed.

Program Definition conj_tau : U ⟹ U' := {|
  transform := fun a => to (be a)
|}.
Next Obligation. symmetry; exact (Hbe x y f). Qed.
Next Obligation. exact (Hbe x y f). Qed.

Theorem map_adj_hom_is_conjugate :
  MapAdjHom A A' Id[C] Id[D] al be = Conjugate A A' conj_sigma conj_tau.
Proof. reflexivity. Qed.

End ConjugateCase.

(* * ** A map 伴随 not 恒等 （已译） *)

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProductAdjunction.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {E B : Category} {G : B ⟶ E} {V : E ⟶ B} (A2 : G ⊣ V).

Program Definition prod_adj_iso (x : D ∏ B) (y : C ∏ E) :
  @Isomorphism Sets
    {| carrier   := @hom (C ∏ E) ((F ∏⟶ G) x) y;
       is_setoid := @homset (C ∏ E) ((F ∏⟶ G) x) y |}
    {| carrier   := @hom (D ∏ B) x ((U ∏⟶ V) y);
       is_setoid := @homset (D ∏ B) x ((U ∏⟶ V) y) |} := {|
  to   := {| morphism := fun f => (to (@adj _ _ _ _ A  _ _) (fst f),
                                   to (@adj _ _ _ _ A2 _ _) (snd f)) |};
  from := {| morphism := fun g => (from (@adj _ _ _ _ A  _ _) (fst g),
                                   from (@adj _ _ _ _ A2 _ _) (snd g)) |}
|}.
Next Obligation.
  intros f g Hfg; split; simpl;
    [ now rewrite (fst Hfg) | now rewrite (snd Hfg) ].
Qed.
Next Obligation.
  intros f g Hfg; split; simpl;
    [ now rewrite (fst Hfg) | now rewrite (snd Hfg) ].
Qed.
Next Obligation.
  split; simpl;
    [ exact (from_adj_comp_law (H:=A)  h)
    | exact (from_adj_comp_law (H:=A2) h0) ].
Qed.
Next Obligation.
  split; simpl;
    [ exact (to_adj_comp_law (H:=A)  h)
    | exact (to_adj_comp_law (H:=A2) h0) ].
Qed.

Definition AdjunctionProduct : (F ∏⟶ G) ⊣ (U ∏⟶ V) :=
  Build_Adjunction' prod_adj_iso
    (fun x y z f g => (to_adj_nat_l (Adjunction:=A)  (fst f) (fst g),
                       to_adj_nat_l (Adjunction:=A2) (snd f) (snd g)))
    (fun x y z f g => (to_adj_nat_r (Adjunction:=A)  (fst f) (fst g),
                       to_adj_nat_r (Adjunction:=A2) (snd f) (snd g))).

End ProductAdjunction.

Section SwapWitness.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).

(*
   本节说明 Map 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition SwapSquares :
  @AdjSquares (C ∏ C) (D ∏ D) (F ∏⟶ F) (U ∏⟶ U)
              (C ∏ C) (D ∏ D) (F ∏⟶ F) (U ∏⟶ U) := {|
  sq_K := Swap;
  sq_L := Swap;
  sq_left  := fun x => eq_refl;
  sq_right := fun a => eq_refl
|}.

Program Definition SwapMap
  : MapOfAdjunctions (AdjunctionProduct A A) (AdjunctionProduct A A) := {|
  map_squares := SwapSquares
|}.
Next Obligation.
  intros x a k; split; simpl;
    [ rewrite id_left; apply (to_adj_respects (H:=A)); apply id_right
    | rewrite id_left; apply (to_adj_respects (H:=A)); apply id_right ].
Qed.

Example swap_map_K_moves (x y : C) :
  fobj[map_K (AdjunctionProduct A A) (AdjunctionProduct A A) SwapMap] (x, y)
    = (y, x).
Proof. reflexivity. Qed.

(* So swap map agrees 恒等 map at (x, y) two
 对象 coincide. （已译） *)
Theorem swap_map_not_identity (x y : C) :
  fobj[map_K (AdjunctionProduct A A) (AdjunctionProduct A A) SwapMap] (x, y)
    = fobj[map_K (AdjunctionProduct A A) (AdjunctionProduct A A)
             (MapOfAdjunctions_id (AdjunctionProduct A A))] (x, y)
  → x = y.
Proof. intros H; exact (f_equal snd H). Qed.

End SwapWitness.

(* * ** An unconditional separation, over two-对象 范畴 （已译） *)

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition MapAdjTwo : Category := {|
  obj     := bool;
  hom     := fun _ _ => poly_unit;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => ttt;
  compose := fun _ _ _ _ _ => ttt
|}.

Program Definition MapAdjTwo_adj : Id[MapAdjTwo] ⊣ Id[MapAdjTwo] :=
  Build_Adjunction' (fun x y => iso_id) _ _.

Definition MapAdjTwoSwap := SwapMap MapAdjTwo_adj.

Example mapadj_two_swap_moves :
  fobj[map_K (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             MapAdjTwoSwap] (true, false)
    = (false, true).
Proof. reflexivity. Qed.

Theorem mapadj_two_swap_not_identity :
  fobj[map_K (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             MapAdjTwoSwap] (true, false)
    = fobj[map_K (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
                 (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj)
             (MapOfAdjunctions_id
                (AdjunctionProduct MapAdjTwo_adj MapAdjTwo_adj))]
        (true, false)
  → False.
Proof.
  intro H.
  pose proof (swap_map_not_identity MapAdjTwo_adj true false H) as Hb.
  discriminate Hb.
Qed.
