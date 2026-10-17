Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Finite products from a terminal object and binary products *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Book:      Mac Lane, CWM 2nd ed., §III.5 Proposition 1 (p. 73)
   Book:      Awodey, Category Theory 1st ed., §2.7

   本文件给出有限情形。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Index vocabulary *)

Definition fin0_rect (P : Fin.t 0 → Type) (i : Fin.t 0) : P i :=
  Fin.case0 P i.

Definition fin2fam_rect (P : Fin.t 2 → Type)
  (p1 : P Fin.F1) (p2 : P (Fin.FS Fin.F1)) (i : Fin.t 2) : P i :=
  Fin.caseS' i P p1
    (fun j => Fin.caseS' j (fun j => P (Fin.FS j)) p2
                (fun k => Fin.case0 (fun k => P (Fin.FS (Fin.FS k))) k)).

Definition fin0 {C : Category} : Fin.t 0 → C :=
  fin0_rect (fun _ => C).

Definition fin2fam {C : Category} (x y : C) : Fin.t 2 → C :=
  fin2fam_rect (fun _ => C) x y.

Definition fin0_legs {C : Category} {a : C} (f : Fin.t 0 → C) :
  ∀ i : Fin.t 0, a ~> f i :=
  fin0_rect (fun i => a ~> f i).

Definition fin2_legs {C : Category} {a x y : C}
  (f : a ~> x) (g : a ~> y) : ∀ i : Fin.t 2, a ~> fin2fam x y i :=
  fin2fam_rect (fun i => a ~> fin2fam x y i) f g.

Definition fin3_rect (P : Fin.t 3 → Type) (p1 : P Fin.F1)
  (p2 : P (Fin.FS Fin.F1)) (p3 : P (Fin.FS (Fin.FS Fin.F1)))
  (i : Fin.t 3) : P i :=
  Fin.caseS' i P p1 (fun j => fin2fam_rect (fun j => P (Fin.FS j)) p2 p3 j).

Definition fin3 {C : Category} (x y z : C) : Fin.t 3 → C :=
  fin3_rect (fun _ => C) x y z.

Definition fin3_legs {C : Category} {a x y z : C}
  (f : a ~> x) (g : a ~> y) (h : a ~> z) :
  ∀ i : Fin.t 3, a ~> fin3 x y z i :=
  fin3_rect (fun i => a ~> fin3 x y z i) f g h.

(** ** The right fold *)

Section FiniteProducts.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

Fixpoint fin_prod (n : nat) : (Fin.t n → C) → C :=
  match n as n0 return (Fin.t n0 → C) → C with
  | O    => fun _ => 1%object
  | S m  => fun f => (f Fin.F1 × fin_prod m (fun i => f (Fin.FS i)))%object
  end.

Fixpoint fin_proj (n : nat) :
  ∀ (f : Fin.t n → C) (i : Fin.t n), fin_prod n f ~> f i :=
  match n as n0
    return ∀ (f : Fin.t n0 → C) (i : Fin.t n0), fin_prod n0 f ~> f i with
  | O    => fun f i => Fin.case0 (fun i => fin_prod 0 f ~> f i) i
  | S m  => fun f i =>
      Fin.caseS' i (fun i => fin_prod (S m) f ~> f i)
        exl
        (fun j => fin_proj m (fun k => f (Fin.FS k)) j ∘ exr)
  end.

Fixpoint fin_tuple (n : nat) :
  ∀ (f : Fin.t n → C) (c : C) (pi : ∀ i, c ~> f i), c ~> fin_prod n f :=
  match n as n0
    return ∀ (f : Fin.t n0 → C) (c : C) (pi : ∀ i, c ~> f i),
             c ~> fin_prod n0 f with
  | O    => fun _ _ _ => one
  | S m  => fun f c pi =>
      pi Fin.F1
        △ fin_tuple m (fun k => f (Fin.FS k)) c (fun k => pi (Fin.FS k))
  end.

Lemma fin_proj_fin_tuple (c : C) :
  ∀ (n : nat) (f : Fin.t n → C) (pi : ∀ i, c ~> f i) (i : Fin.t n),
    fin_proj n f i ∘ fin_tuple n f c pi ≈ pi i.
Proof.
  intros n; induction n as [|m IHm]; intros f pi i.
  - exact (Fin.case0
             (fun i => fin_proj 0 f i ∘ fin_tuple 0 f c pi ≈ pi i) i).
  - pattern i; apply (Fin.caseS' i); simpl.
    + apply exl_fork.
    + intro j.
      rewrite <- comp_assoc.
      rewrite exr_fork.
      apply (IHm (fun k => f (Fin.FS k)) (fun k => pi (Fin.FS k)) j).
Qed.

Lemma fin_tuple_unique (c : C) :
  ∀ (n : nat) (f : Fin.t n → C) (pi : ∀ i, c ~> f i)
    (u : c ~> fin_prod n f),
    (∀ i, fin_proj n f i ∘ u ≈ pi i) → u ≈ fin_tuple n f c pi.
Proof.
  intros n; induction n as [|m IHm]; intros f pi u Hu.
  - apply one_unique.
  - simpl.
    apply (snd (ump_products _ _ _)).
    split.
    + apply (Hu Fin.F1).
    + apply IHm.
      intro j.
      rewrite comp_assoc.
      apply (Hu (Fin.FS j)).
Qed.

Definition fin_prod_ump (n : nat) (f : Fin.t n → C)
  (c : C) (pi : ∀ i, c ~> f i) :
  ∃! u : c ~> fin_prod n f, ∀ i, fin_proj n f i ∘ u ≈ pi i.
Proof.
  unshelve eapply Build_Unique.
  - exact (fin_tuple n f c pi).
  - exact (fin_proj_fin_tuple c n f pi).
  - intros v Hv.
    symmetry.
    exact (fin_tuple_unique c n f pi v Hv).
Defined.

Definition fin_IsIndexedProduct (n : nat) (f : Fin.t n → C) :
  IsIndexedProduct f (fin_prod n f) (fin_proj n f) :=
  {| iprod_desc := fun c pi => fin_prod_ump n f c pi |}.

(** ** The small arities *)

Example fin_prod_zero (f : Fin.t 0 → C) : fin_prod 0 f = 1%object := eq_refl.

Example fin_prod_one (f : Fin.t 1 → C) :
  fin_prod 1 f = (f Fin.F1 × 1)%object := eq_refl.

Example fin_prod_two (f : Fin.t 2 → C) :
  fin_prod 2 f = (f Fin.F1 × (f (Fin.FS Fin.F1) × 1))%object := eq_refl.

Example fin_proj_one (f : Fin.t 1 → C) : fin_proj 1 f Fin.F1 = exl := eq_refl.

Example fin_proj_two_snd (f : Fin.t 2 → C) :
  fin_proj 2 f (Fin.FS Fin.F1) = exl ∘ exr := eq_refl.

Example fin_tuple_two (f : Fin.t 2 → C) (c : C) (pi : ∀ i, c ~> f i) :
  fin_tuple 2 f c pi = pi Fin.F1 △ (pi (Fin.FS Fin.F1) △ one) := eq_refl.

Definition fin_prod_one_iso (f : Fin.t 1 → C) : fin_prod 1 f ≅ f Fin.F1 :=
  prod_one_r.

Definition fin_prod_two_iso (f : Fin.t 2 → C) :
  fin_prod 2 f ≅ (f Fin.F1 × f (Fin.FS Fin.F1))%object :=
  prod_respects_iso _ _ iso_id _ _ prod_one_r.

End FiniteProducts.

Arguments fin_prod {C _ _} n f.
Arguments fin_proj {C _ _} n f i.
Arguments fin_tuple {C _ _} n f c pi.

(** ** Reading an indexed product at the two bracketing arities *)

Definition iprod_zero_IsTerminalObj {C : Category} (f : Fin.t 0 → C)
  (p : C) (proj : ∀ i, p ~> f i) (HP : IsIndexedProduct f p proj) :
  IsTerminalObj p.
Proof.
  intro x.
  destruct (iprod_desc HP (@fin0_legs C x f)) as [u _ Hu].
  unshelve eapply Build_Unique.
  - exact u.
  - exact I.
  - intros v _.
    apply Hu.
    exact (fun i => fin0_rect (fun i => proj i ∘ v ≈ fin0_legs f i) i).
Defined.

Section IndexedProductTwo.

Context {C : Category} (x y p : C).
Context (proj : ∀ i, p ~> fin2fam x y i).
Context (HP : IsIndexedProduct (fin2fam x y) p proj).

Definition iprod2_med {a : C} (f : a ~> x) (g : a ~> y) : a ~> p :=
  unique_obj (iprod_desc HP (fin2_legs f g)).

Definition iprod2_med_commutes {a : C} (f : a ~> x) (g : a ~> y) :
  ∀ i, proj i ∘ iprod2_med f g ≈ fin2_legs f g i :=
  unique_property (iprod_desc HP (fin2_legs f g)).

Definition iprod2_med_unique {a : C} (f : a ~> x) (g : a ~> y) (v : a ~> p) :
  (∀ i, proj i ∘ v ≈ fin2_legs f g i) → iprod2_med f g ≈ v :=
  uniqueness (iprod_desc HP (fin2_legs f g)) v.

Definition iprod_two_IsCartesianProduct : @IsCartesianProduct C x y p.
Proof using C HP p proj x y.
  unshelve econstructor.
  - exact (@iprod2_med).
  - exact (proj Fin.F1).
  - exact (proj (Fin.FS Fin.F1)).
  - intros a f1 f2 Hf g1 g2 Hg.
    apply iprod2_med_unique.
    apply (fin2fam_rect
             (fun i => proj i ∘ iprod2_med f2 g2 ≈ fin2_legs f1 g1 i)).
    + etransitivity; [ apply iprod2_med_commutes | symmetry; exact Hf ].
    + etransitivity; [ apply iprod2_med_commutes | symmetry; exact Hg ].
  - intros a f g h.
    split; intros HH.
    + split.
      * rewrite HH; apply (iprod2_med_commutes f g Fin.F1).
      * rewrite HH; apply (iprod2_med_commutes f g (Fin.FS Fin.F1)).
    + destruct HH as [H1 H2].
      symmetry.
      apply iprod2_med_unique.
      exact (fin2fam_rect (fun i => proj i ∘ h ≈ fin2_legs f g i) H1 H2).
Defined.

End IndexedProductTwo.

(** ** Essential uniqueness of an indexed product *)

Section IndexedProductUnique.

Context {C : Category} {A : Type} (f : A → C) (p q : C).
Context (projp : ∀ a, p ~> f a) (projq : ∀ a, q ~> f a).
Context (HP : IsIndexedProduct f p projp).
Context (HQ : IsIndexedProduct f q projq).

Definition iprod_compare : p ~> q := unique_obj (iprod_desc HQ projp).

Definition iprod_compare_inv : q ~> p := unique_obj (iprod_desc HP projq).

Definition iprod_compare_commutes : ∀ a, projq a ∘ iprod_compare ≈ projp a :=
  unique_property (iprod_desc HQ projp).

Definition iprod_compare_inv_commutes :
  ∀ a, projp a ∘ iprod_compare_inv ≈ projq a :=
  unique_property (iprod_desc HP projq).

Definition iprod_unique_iso : p ≅ q.
Proof using A C HP HQ f p projp projq q.
  unshelve econstructor.
  - exact iprod_compare.
  - exact iprod_compare_inv.
  - destruct (iprod_desc HQ projq) as [u _ Hun].
    rewrite <- (Hun id (fun a => id_right (projq a))).
    symmetry.
    apply Hun.
    intro a.
    rewrite comp_assoc.
    rewrite iprod_compare_commutes.
    apply iprod_compare_inv_commutes.
  - destruct (iprod_desc HP projp) as [u _ Hun].
    rewrite <- (Hun id (fun a => id_right (projp a))).
    symmetry.
    apply Hun.
    intro a.
    rewrite comp_assoc.
    rewrite iprod_compare_inv_commutes.
    apply iprod_compare_commutes.
Defined.

End IndexedProductUnique.

Definition Cartesian_of_IsCartesianProduct {C : Category}
  (P : C → C → C) (HP : ∀ x y : C, @IsCartesianProduct C x y (P x y)) :
  @Cartesian C := {|
  product_obj   := P;
  fork          := fun x y z f g => @fork' C y z (P y z) (HP y z) x f g;
  exl           := fun x y => @exl' C x y (P x y) (HP x y);
  exr           := fun x y => @exr' C x y (P x y) (HP x y);
  fork_respects := fun x y z => @fork'_respects C y z (P y z) (HP y z) x;
  ump_products  := fun x y z => @ump_product C y z (P y z) (HP y z) x
|}.

(** ** The class of finite products, and its two directions *)

Class HasFiniteProducts (C : Category) := {
  finite_product {n : nat} (f : Fin.t n → C) : C;
  finite_product_proj {n : nat} (f : Fin.t n → C) (i : Fin.t n) :
    finite_product f ~> f i;
  finite_product_ump {n : nat} (f : Fin.t n → C) :
    IsIndexedProduct f (finite_product f) (finite_product_proj f)
}.

Definition Cartesian_Terminal_HasFiniteProducts {C : Category}
  (CP : @Cartesian C) (T : @Terminal C) : HasFiniteProducts C := {|
  finite_product      := fun n f => fin_prod n f;
  finite_product_proj := fun n f i => fin_proj n f i;
  finite_product_ump  := fun n f => fin_IsIndexedProduct n f
|}.

Definition HasFiniteProducts_Terminal {C : Category}
  (HP : HasFiniteProducts C) : @Terminal C :=
  Terminal_from_IsTerminalObj
    (iprod_zero_IsTerminalObj fin0 (finite_product fin0)
       (finite_product_proj fin0) (finite_product_ump fin0)).

Definition HasFiniteProducts_Cartesian {C : Category}
  (HP : HasFiniteProducts C) : @Cartesian C :=
  Cartesian_of_IsCartesianProduct
    (fun x y => finite_product (fin2fam x y))
    (fun x y => iprod_two_IsCartesianProduct x y
                  (finite_product (fin2fam x y))
                  (finite_product_proj (fin2fam x y))
                  (finite_product_ump (fin2fam x y))).

Theorem HasFiniteProducts_iff (C : Category) :
  HasFiniteProducts C ↔ (@Cartesian C * @Terminal C)%type.
Proof.
  split.
  - intro HP.
    exact (HasFiniteProducts_Cartesian HP, HasFiniteProducts_Terminal HP).
  - intros [CP T].
    exact (Cartesian_Terminal_HasFiniteProducts CP T).
Defined.

(** ** The two bracketing arities of the fold itself *)

Definition fin_zero_IsTerminalObj {C : Category}
  (CP : @Cartesian C) (T : @Terminal C) (f : Fin.t 0 → C) :
  IsTerminalObj (fin_prod 0 f) :=
  iprod_zero_IsTerminalObj f (fin_prod 0 f) (fin_proj 0 f)
    (fin_IsIndexedProduct 0 f).

Definition fin_two_IsCartesianProduct {C : Category}
  (CP : @Cartesian C) (T : @Terminal C) (x y : C) :
  @IsCartesianProduct C x y (fin_prod 2 (fin2fam x y)) :=
  iprod_two_IsCartesianProduct x y (fin_prod 2 (fin2fam x y))
    (fin_proj 2 (fin2fam x y)) (fin_IsIndexedProduct 2 (fin2fam x y)).

(*
   本节说明 Finite 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin_prod_unique_iso {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (n : nat) (f : Fin.t n → C) (q : C)
  (projq : ∀ i, q ~> f i) (HQ : IsIndexedProduct f q projq) :
  fin_prod n f ≅ q :=
  iprod_unique_iso f (fin_prod n f) q (fin_proj n f) projq
    (fin_IsIndexedProduct n f) HQ.

(* ... and the isomorphism commutes with the projections, in both
   directions.  A bare [≅] would be the weak form. *)
Definition fin_prod_unique_iso_to {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (n : nat) (f : Fin.t n → C) (q : C)
  (projq : ∀ i, q ~> f i) (HQ : IsIndexedProduct f q projq) :
  ∀ i, projq i ∘ to (fin_prod_unique_iso CP T n f q projq HQ)
         ≈ fin_proj n f i :=
  iprod_compare_commutes f (fin_prod n f) q (fin_proj n f) projq HQ.

Definition fin_prod_unique_iso_from {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (n : nat) (f : Fin.t n → C) (q : C)
  (projq : ∀ i, q ~> f i) (HQ : IsIndexedProduct f q projq) :
  ∀ i, fin_proj n f i ∘ from (fin_prod_unique_iso CP T n f q projq HQ)
         ≈ projq i :=
  iprod_compare_inv_commutes f (fin_prod n f) q (fin_proj n f) projq
    (fin_IsIndexedProduct n f).

(** ** Awodey's left-associated ternary product *)

Section AwodeyTernary.

(*
   本节说明笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context {C : Category}.
Context (CP : @Cartesian C).
Context (x y z : C).

Definition awodey_prod : C := ((x × y) × z)%object.

Definition awodey_proj : ∀ i, awodey_prod ~> fin3 x y z i :=
  fin3_rect (fun i => awodey_prod ~> fin3 x y z i)
    (exl ∘ exl) (exr ∘ exl) exr.

Definition awodey_tuple {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  c ~> awodey_prod :=
  (pi Fin.F1 △ pi (Fin.FS Fin.F1)) △ pi (Fin.FS (Fin.FS Fin.F1)).

(* The three triangles, stated with the projections written out so that no
   tactic has to unfold [awodey_proj]; they are convertible with it. *)
Lemma awodey_tuple_1 {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  (exl ∘ exl) ∘ awodey_tuple pi ≈ pi Fin.F1.
Proof.
  unfold awodey_tuple.
  rewrite <- comp_assoc, exl_fork.
  apply exl_fork.
Qed.

Lemma awodey_tuple_2 {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  (exr ∘ exl) ∘ awodey_tuple pi ≈ pi (Fin.FS Fin.F1).
Proof.
  unfold awodey_tuple.
  rewrite <- comp_assoc, exl_fork.
  apply exr_fork.
Qed.

Lemma awodey_tuple_3 {c : C} (pi : ∀ i, c ~> fin3 x y z i) :
  exr ∘ awodey_tuple pi ≈ pi (Fin.FS (Fin.FS Fin.F1)).
Proof.
  unfold awodey_tuple.
  apply exr_fork.
Qed.

Definition awodey_IsIndexedProduct :
  IsIndexedProduct (fin3 x y z) awodey_prod awodey_proj.
Proof using C CP x y z.
  constructor.
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (awodey_tuple pi).
  - apply (fin3_rect (fun i => awodey_proj i ∘ awodey_tuple pi ≈ pi i)).
    + exact (awodey_tuple_1 pi).
    + exact (awodey_tuple_2 pi).
    + exact (awodey_tuple_3 pi).
  - intros v Hv.
    unfold awodey_tuple.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + apply (snd (ump_products _ _ _)).
      split.
      * rewrite comp_assoc.
        exact (Hv Fin.F1).
      * rewrite comp_assoc.
        exact (Hv (Fin.FS Fin.F1)).
    + exact (Hv (Fin.FS (Fin.FS Fin.F1))).
Defined.

End AwodeyTernary.

(* Awodey §2.7's displayed ternary product IS this file's right fold, up to
   a canonical isomorphism commuting with all three projections. *)
Definition awodey_fold_iso {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (x y z : C) :
  fin_prod 3 (fin3 x y z) ≅ awodey_prod CP x y z :=
  fin_prod_unique_iso CP T 3 (fin3 x y z) (awodey_prod CP x y z)
    (awodey_proj CP x y z) (awodey_IsIndexedProduct CP x y z).

Definition awodey_fold_iso_to {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (x y z : C) :
  ∀ i, awodey_proj CP x y z i ∘ to (awodey_fold_iso CP T x y z)
         ≈ fin_proj 3 (fin3 x y z) i :=
  fin_prod_unique_iso_to CP T 3 (fin3 x y z) (awodey_prod CP x y z)
    (awodey_proj CP x y z) (awodey_IsIndexedProduct CP x y z).

Definition awodey_fold_iso_from {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (x y z : C) :
  ∀ i, fin_proj 3 (fin3 x y z) i ∘ from (awodey_fold_iso CP T x y z)
         ≈ awodey_proj CP x y z i :=
  fin_prod_unique_iso_from CP T 3 (fin3 x y z) (awodey_prod CP x y z)
    (awodey_proj CP x y z) (awodey_IsIndexedProduct CP x y z).

(** ** The dual *)

Section FiniteCoproducts.

Context {C : Category}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

Definition fin_coprod (n : nat) (f : Fin.t n → C) : C :=
  @fin_prod (C^op) CC I n f.

Definition fin_inj (n : nat) (f : Fin.t n → C) (i : Fin.t n) :
  f i ~> fin_coprod n f :=
  @fin_proj (C^op) CC I n f i.

Definition fin_cotuple (n : nat) (f : Fin.t n → C) (c : C)
  (iota : ∀ i, f i ~> c) : fin_coprod n f ~> c :=
  @fin_tuple (C^op) CC I n f c iota.

Definition fin_coprod_ump (n : nat) (f : Fin.t n → C)
  (c : C) (iota : ∀ i, f i ~> c) :
  ∃! u : fin_coprod n f ~> c, ∀ i, u ∘ fin_inj n f i ≈ iota i :=
  @fin_prod_ump (C^op) CC I n f c iota.

Definition fin_IsIndexedCoproduct (n : nat) (f : Fin.t n → C) :
  IsIndexedCoproduct f (fin_coprod n f) (fin_inj n f) :=
  @fin_IsIndexedProduct (C^op) CC I n f.

End FiniteCoproducts.

Arguments fin_coprod {C} CC I n f.
Arguments fin_inj {C} CC I n f i.
Arguments fin_cotuple {C} CC I n f c iota.

Definition HasFiniteCoproducts (C : Category) : Type :=
  @HasFiniteProducts (C^op).

Existing Class HasFiniteCoproducts.

Definition Build_HasFiniteCoproducts {C : Category}
  (cobj : ∀ n : nat, (Fin.t n → C) → C)
  (cinj : ∀ (n : nat) (f : Fin.t n → C) (i : Fin.t n), f i ~> cobj n f)
  (cump : ∀ (n : nat) (f : Fin.t n → C),
            IsIndexedCoproduct f (cobj n f) (cinj n f)) :
  HasFiniteCoproducts C :=
  @Build_HasFiniteProducts (C^op) cobj cinj cump.

Section FiniteCoproductAPI.

Context {C : Category}.
Context {H : HasFiniteCoproducts C}.

Definition finite_coproduct {n : nat} (f : Fin.t n → C) : C :=
  @finite_product (C^op) H n f.

Definition finite_coproduct_inj {n : nat} (f : Fin.t n → C) (i : Fin.t n) :
  f i ~> finite_coproduct f :=
  @finite_product_proj (C^op) H n f i.

Definition finite_coproduct_ump {n : nat} (f : Fin.t n → C) :
  IsIndexedCoproduct f (finite_coproduct f) (finite_coproduct_inj f) :=
  @finite_product_ump (C^op) H n f.

End FiniteCoproductAPI.

Definition Cocartesian_Initial_HasFiniteCoproducts {C : Category}
  (CC : @Cocartesian C) (I : @Initial C) : HasFiniteCoproducts C :=
  @Cartesian_Terminal_HasFiniteProducts (C^op) CC I.

Definition HasFiniteCoproducts_Cocartesian {C : Category}
  (HP : HasFiniteCoproducts C) : @Cocartesian C :=
  @HasFiniteProducts_Cartesian (C^op) HP.

Definition HasFiniteCoproducts_Initial {C : Category}
  (HP : HasFiniteCoproducts C) : @Initial C :=
  @HasFiniteProducts_Terminal (C^op) HP.

(** ** Non-vacuity: the fold computes *)

Example coq_fin_prod_zero (f : Fin.t 0 → Coq) :
  fin_prod 0 f = unit := eq_refl.

Example coq_fin_prod_three :
  fin_prod 3 (fun _ : Fin.t 3 => nat : Coq)
    = (nat * (nat * (nat * unit)))%type := eq_refl.

Example coq_fin_prod_mixed :
  fin_prod 2 (fin2fam (bool : Coq) (nat : Coq))
    = (bool * (nat * unit))%type := eq_refl.

Example coq_fin_tuple_computes :
  fin_tuple 2 (fin2fam (bool : Coq) (nat : Coq)) (nat : Coq)
    (fin2_legs (fun n : nat => Nat.eqb n O) (fun n : nat => S n))
    (S (S (S O))) = (false, (S (S (S (S O))), tt)) := eq_refl.

Example coq_fin_proj_computes :
  fin_proj 2 (fin2fam (bool : Coq) (nat : Coq)) (Fin.FS Fin.F1)
    (true, (S (S O), tt)) = S (S O) := eq_refl.
