Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Omega.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(* * * The finite ordinals 范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/simplex+category
 nLab:      https://ncatlab.org/nlab/show/interval+category
 Wikipedia: https://en.wikipedia.org/wiki/Posetal_category
 Book:      Mac Lane, Categories for the Working Mathematician, 2nd ed.,
 Book:      Fong and Spivak, Seven Sketches in Compositionality, §3.2.1
 Book:      Riehl, Category Theory in Context, §1.6

   本文件给出序数相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ---------- [le_t] is a subsingleton ---------- *)

Lemma nat_succ_add_neq (d m : nat) : (S (d + m) = m)%nat → False.
Proof.
  induction m as [| m' IH]; simpl; intro H.
  - discriminate.
  - apply IH.
    injection H; intro E.
    now rewrite PeanoNat.Nat.add_succ_r in E.
Qed.

Lemma le_t_sum {m n} (f : le_t m n) : ex (fun d : nat => (n = d + m)%nat).
Proof.
  induction f as [| k f' [d Hd]].
  - exists 0%nat; reflexivity.
  - exists (S d); simpl; now rewrite Hd.
Qed.

Lemma le_t_no_desc {m} (f : le_t (S m) m) : False.
Proof.
  destruct (le_t_sum f) as [d Hd].
  rewrite PeanoNat.Nat.add_succ_r in Hd.
  exact (nat_succ_add_neq d m (eq_sym Hd)).
Qed.

Lemma le_t_zero_absurd {m} (f : le_t (S m) 0) : False.
Proof.
  destruct (le_t_sum f) as [d Hd].
  rewrite PeanoNat.Nat.add_succ_r in Hd.
  discriminate.
Qed.

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma le_t_inv {n m} (g : le_t n m) :
  ({ e : n = m & g = eq_rect n (le_t n) le_t_n m e } +
   { m' : nat & { e : m = S m' &
       { g' : le_t n m' & g = eq_rect (S m') (le_t n) (le_t_S g') m (eq_sym e) } } })%type.
Proof.
  destruct g as [| m' g'].
  - left; exists eq_refl; reflexivity.
  - right; exists m', eq_refl, g'; reflexivity.
Qed.

(* Thinness, in its raw form: [le_t m n] has at most one inhabitant. *)
Lemma le_t_irr {m n} (f g : le_t m n) : f = g.
Proof.
  induction f as [| k f' IH].
  - destruct (le_t_inv g) as [[e He] | [m' [e [g' Hg]]]].
    + rewrite He.
      now rewrite (UIP_dec PeanoNat.Nat.eq_dec e eq_refl).
    + subst m.
      now destruct (le_t_no_desc g').
  - destruct (le_t_inv g) as [[e He] | [m' [e [g' Hg]]]].
    + subst m.
      now destruct (le_t_no_desc f').
    + injection e; intro E; subst m'.
      rewrite (UIP_dec PeanoNat.Nat.eq_dec e eq_refl) in Hg.
      simpl in Hg; subst g.
      now rewrite (IH g').
Qed.

(* ---------- derived arithmetic on [le_t] ---------- *)

Definition le_t_pred_self (a : nat) : le_t (Nat.pred a) a :=
  match a with
  | O   => le_t_n
  | S k => le_t_S le_t_n
  end.

Definition le_t_pred {a b} (f : le_t a b) : le_t (Nat.pred a) (Nat.pred b) :=
  match f in le_t _ b' return le_t (Nat.pred a) (Nat.pred b') with
  | le_t_n    => le_t_n
  | le_t_S f' => le_t_trans (le_t_pred_self a) f'
  end.

Definition le_t_SS_inv {a b} (f : le_t (S a) (S b)) : le_t a b := le_t_pred f.

Fixpoint le_t_SS {a b} (f : le_t a b) : le_t (S a) (S b) :=
  match f in le_t _ b' return le_t (S a) (S b') with
  | le_t_n    => le_t_n
  | le_t_S f' => le_t_S (le_t_SS f')
  end.

Definition le_t_zero (b : nat) : le_t O b :=
  nat_rect (fun k => le_t O k) le_t_n (fun _ ih => le_t_S ih) b.

(* ---------- the ordinal on n objects, as a category ---------- *)

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Ord_obj@{u} (n : nat) : Type@{u} := ord_at {
  ord_val   : nat;
  ord_bound : le_t@{u} (S ord_val) n
}.

Arguments ord_at {n} _ _.
Arguments ord_val {n} _.
Arguments ord_bound {n} _.

(* The 范畴 laws Omega's, transported along [ord_val]; 证明
 script one Instance/Omega.v uses [Omega] itself. （已译） *)
Program Definition Ordinal@{o h p} (n : nat) : Category@{o h p} := {|
  obj     := Ord_obj@{o} n;
  hom     := fun x y => le_t@{h} (ord_val x) (ord_val y);
  homset  := Morphism_equality@{o h p};
  id      := fun _ => le_t_n@{h};
  compose := fun _ _ _ f g => le_t_trans@{h} g f
|}.
Solve All Obligations with
  (simpl; intros; try subst;
   rewrite ?le_t_trans_id_l, ?le_t_trans_id_r, ?le_t_trans_assoc;
   try reflexivity).

(* Thinness [Ordinal n]: any two parallel arrows equal, nose.
 This one 引理 discharges essentially every coherence obligation below. （已译） *)
Lemma ord_thin {n} {x y : Ordinal n} (f g : x ~> y) : f = g.
Proof. exact (le_t_irr f g). Qed.

(* 相关说明。 （已译） *)
Lemma ord_obj_eq {n} {x y : Ord_obj n} : ord_val x = ord_val y → x = y.
Proof.
  destruct x as [i Hi], y as [j Hj]; simpl; intro e.
  subst j.
  now rewrite (le_t_irr Hi Hj).
Qed.

Definition ord_iso_of_eq {n} {x y : Ord_obj n} (e : x = y) :
  @Isomorphism (Ordinal n) x y :=
  match e in _ = z return @Isomorphism (Ordinal n) x z with
  | eq_refl => iso_id
  end.

Definition ord_iso {n} {x y : Ord_obj n} (e : ord_val x = ord_val y) :
  @Isomorphism (Ordinal n) x y := ord_iso_of_eq (ord_obj_eq e).

(* ---------- distinguished 对象 generating steps ---------- （已译） *)

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ord_incl {n} (x : Ord_obj n) : Ord_obj (S n) :=
  ord_at (ord_val x) (le_t_S (ord_bound x)).

Definition ord_succ {n} (x : Ord_obj n) : Ord_obj (S n) :=
  ord_at (S (ord_val x)) (le_t_SS (ord_bound x)).

Definition ord_step {n} (k : Ord_obj n) :
  @hom (Ordinal (S n)) (ord_incl k) (ord_succ k) := le_t_S le_t_n.

(* ---------- the embedding functors ---------- *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Ord_Incl (n : nat) : Ordinal n ⟶ Ordinal (S n) := {|
  fobj := ord_incl;
  fmap := fun _ _ f => f
|}.

Program Definition Ord_Omega (n : nat) : Ordinal n ⟶ Omega := {|
  fobj := ord_val;
  fmap := fun _ _ f => f
|}.

#[export] Program Instance Ord_Incl_Faithful (n : nat) : Faithful (Ord_Incl n) := {|
  fmap_inj := fun _ _ _ _ H => H
|}.
#[export] Program Instance Ord_Incl_Full (n : nat) : Full (Ord_Incl n) := {|
  prefmap := fun _ _ g => g
|}.
#[export] Program Instance Ord_Omega_Faithful (n : nat) : Faithful (Ord_Omega n) := {|
  fmap_inj := fun _ _ _ _ H => H
|}.
#[export] Program Instance Ord_Omega_Full (n : nat) : Full (Ord_Omega n) := {|
  prefmap := fun _ _ g => g
|}.

Theorem Ord_Omega_Incl (n : nat) :
  Ord_Omega (S n) ◯ Ord_Incl n ≈ Ord_Omega n.
Proof.
  exists (fun _ => iso_id).
  simpl; intros.
  apply le_t_irr.
Qed.

(* ---------- freeness: [Ordinal (S n)] is free on n composable arrows ---------- *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition OrdSteps {C : Category} (n : nat) (X : nat → C) : Type :=
  ∀ k : nat, le_t (S k) n → X k ~> X (S k).

Definition OrdArrows {C : Category} (n : nat) (X : nat → C) : Type :=
  ∀ i j : nat, le_t j n → le_t i j → X i ~> X j.

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint chain_fmap {C : Category} {n : nat} {X : nat → C} (s : OrdSteps n X)
  {i j : nat} (f : le_t i j) {struct f} : le_t j n → X i ~> X j :=
  match f in le_t _ j' return le_t j' n → X i ~> X j' with
  | le_t_n    => fun _ => id
  | le_t_S f' => fun H => s _ H ∘ chain_fmap s f' (le_t_trans (le_t_S le_t_n) H)
  end.

(* Definitional sanity pin (unused below; [eq_refl]-style check the
 fold sends reflexivity 恒等, kept so refactor breaks it
 caught here rather than downstream). （已译） *)
Lemma chain_fmap_id {C : Category} {n} {X : nat → C} (s : OrdSteps n X)
  (i : nat) (H : le_t i n) : chain_fmap s (@le_t_n i) H ≈ id.
Proof. reflexivity. Qed.

Lemma chain_fmap_comp {C : Category} {n} {X : nat → C} (s : OrdSteps n X)
  {i j k : nat} (g : le_t i j) (f : le_t j k) :
  ∀ (Hj : le_t j n) (Hk : le_t k n),
    chain_fmap s (le_t_trans g f) Hk ≈ chain_fmap s f Hk ∘ chain_fmap s g Hj.
Proof.
  induction f as [| m f' IH]; simpl; intros Hj Hk.
  - rewrite id_left.
    now rewrite (le_t_irr Hk Hj).
  - rewrite <- comp_assoc.
    now rewrite (IH Hj (le_t_trans (le_t_S le_t_n) Hk)).
Qed.

(* A path n arrows gives genuine 函子 out ordinal n+1
 对象, whose action 对象 [X] read off index. （已译） *)
Program Definition Functor_of_Steps {C : Category} {n : nat} {X : nat → C}
  (s : OrdSteps n X) : Ordinal (S n) ⟶ C := {|
  fobj := fun x => X (ord_val x);
  fmap := fun _ y f => chain_fmap s f (le_t_SS_inv (ord_bound y))
|}.
Next Obligation. apply chain_fmap_comp. Qed.

Theorem Functor_of_Steps_step {C : Category} {n : nat} {X : nat → C}
  (s : OrdSteps n X) (k : Ord_obj n) :
  fmap[Functor_of_Steps s] (ord_step k) ≈ s (ord_val k) (ord_bound k).
Proof.
  simpl.
  rewrite id_right.
  now rewrite (le_t_irr (le_t_SS_inv (le_t_SS (ord_bound k))) (ord_bound k)).
Qed.

Definition steps_of_arrows {C : Category} {n} {X : nat → C} (u : OrdArrows n X) :
  OrdSteps n X := fun k H => u k (S k) H (le_t_S le_t_n).

Definition arrows_of_steps {C : Category} {n} {X : nat → C} (s : OrdSteps n X) :
  OrdArrows n X := fun i j H f => chain_fmap s f H.

(* 相关说明。 （已译） *)
Theorem steps_arrows_steps {C : Category} {n} {X : nat → C} (s : OrdSteps n X) :
  ∀ k H, steps_of_arrows (arrows_of_steps s) k H ≈ s k H.
Proof.
  intros k H; unfold steps_of_arrows, arrows_of_steps; simpl.
  now rewrite id_right.
Qed.

(* And functorial action determined steps: 这是 freeness. （已译） *)
Theorem arrows_steps_arrows {C : Category} {n} {X : nat → C} (u : OrdArrows n X)
  (Hid : ∀ i (H : le_t i n), u i i H le_t_n ≈ id)
  (Hcomp : ∀ i j k (Hj : le_t j n) (Hk : le_t k n) (g : le_t i j) (f : le_t j k),
      u i k Hk (le_t_trans g f) ≈ u j k Hk f ∘ u i j Hj g) :
  ∀ i j (f : le_t i j) (H : le_t j n),
    arrows_of_steps (steps_of_arrows u) i j H f ≈ u i j H f.
Proof.
  unfold arrows_of_steps, steps_of_arrows.
  intros i j f; induction f as [| m f' IH]; simpl; intro H.
  - now rewrite Hid.
  - rewrite IH.
    assert (E : u i (S m) H (le_t_S f')
                  ≈ u m (S m) H (le_t_S le_t_n)
                      ∘ u i m (le_t_trans (le_t_S le_t_n) H) f')
      by apply (Hcomp i m (S m) (le_t_trans (le_t_S le_t_n) H) H f' (le_t_S le_t_n)).
    now rewrite E.
Qed.

(* Record eta [Ord_obj]: 对象 value 与…配对 bound,
 definitionally. This what lets value-indexed 自然性 引理 below
 applied at arbitrary 对象. （已译） *)
Example ord_eta {n} (x : Ord_obj n) : ord_at (ord_val x) (ord_bound x) = x := eq_refl.

(* The uniqueness half freeness, form setoid discipline wants:
 自然性 need checked n generating steps. （已译） *)
Theorem ord_naturality_from_steps {C : Category} {n : nat}
  (F G : Ordinal (S n) ⟶ C) (θ : ∀ x : Ord_obj (S n), F x ≅ G x)
  (Hgen : ∀ k : Ord_obj n,
      to (θ (ord_succ k)) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ to (θ (ord_incl k))) :
  ∀ (i j : nat) (f : le_t i j) (Hi : le_t (S i) (S n)) (Hj : le_t (S j) (S n)),
    to (θ (ord_at j Hj)) ∘ @fmap _ _ F (ord_at i Hi) (ord_at j Hj) f
      ≈ @fmap _ _ G (ord_at i Hi) (ord_at j Hj) f ∘ to (θ (ord_at i Hi)).
Proof.
  intros i j f; induction f as [| m f' IH]; intros Hi Hj.
  - rewrite (le_t_irr Hj Hi).
    assert (EF : @fmap _ _ F (ord_at i Hi) (ord_at i Hi) le_t_n ≈ id)
      by exact (@fmap_id _ _ F (ord_at i Hi)).
    assert (EG : @fmap _ _ G (ord_at i Hi) (ord_at i Hi) le_t_n ≈ id)
      by exact (@fmap_id _ _ G (ord_at i Hi)).
    rewrite EF, EG.
    now rewrite id_left, id_right.
  - pose (Hm := le_t_SS_inv Hj : le_t (S m) n).
    rewrite (le_t_irr Hj (le_t_SS Hm)).
    assert (Estep : @fmap _ _ F (ord_at i Hi) (ord_at (S m) (le_t_SS Hm)) (le_t_S f')
              ≈ fmap[F] (ord_step (ord_at m Hm))
                  ∘ @fmap _ _ F (ord_at i Hi) (ord_at m (le_t_S Hm)) f').
    { rewrite <- fmap_comp.
      apply fmap_respects, le_t_irr. }
    assert (Estep' : @fmap _ _ G (ord_at i Hi) (ord_at (S m) (le_t_SS Hm)) (le_t_S f')
              ≈ fmap[G] (ord_step (ord_at m Hm))
                  ∘ @fmap _ _ G (ord_at i Hi) (ord_at m (le_t_S Hm)) f').
    { rewrite <- fmap_comp.
      apply fmap_respects, le_t_irr. }
    rewrite Estep, Estep'.
    rewrite comp_assoc.
    rewrite (Hgen (ord_at m Hm)).
    rewrite <- comp_assoc.
    rewrite (IH Hi (le_t_S Hm)).
    now rewrite comp_assoc.
Qed.

Lemma ord_iso_natural_flip {C : Category} {a b c d : C}
  (i : a ≅ c) (j : b ≅ d) (u : a ~> b) (v : c ~> d)
  (H : to j ∘ u ≈ v ∘ to i) : u ≈ from j ∘ v ∘ to i.
Proof.
  rewrite <- comp_assoc.
  rewrite <- H.
  rewrite comp_assoc.
  rewrite iso_from_to.
  now rewrite id_left.
Qed.

Theorem ord_functor_equiv_from_steps {C : Category} {n : nat}
  (F G : Ordinal (S n) ⟶ C) (θ : ∀ x : Ord_obj (S n), F x ≅ G x)
  (Hgen : ∀ k : Ord_obj n,
      to (θ (ord_succ k)) ∘ fmap[F] (ord_step k)
        ≈ fmap[G] (ord_step k) ∘ to (θ (ord_incl k))) :
  F ≈ G.
Proof.
  exists θ.
  intros x y f.
  apply (ord_iso_natural_flip (θ x) (θ y)).
  exact (ord_naturality_from_steps F G θ Hgen
           (ord_val x) (ord_val y) f (ord_bound x) (ord_bound y)).
Qed.

(* ---------- every functor out of [Ordinal (S n)] comes from a path ---------- *)

Fixpoint le_t_min (k n : nat) {struct k} : le_t (Nat.min k n) n :=
  match k as k0 return le_t (Nat.min k0 n) n with
  | O => le_t_zero n
  | S k' => match n as n0 return le_t (Nat.min (S k') n0) n0 with
            | O => le_t_n
            | S n' => le_t_SS (le_t_min k' n')
            end
  end.

Lemma le_t_min_l (k n : nat) : le_t k n → (Nat.min k n = k)%nat.
Proof.
  revert n; induction k as [| k' IH]; intros n H.
  - reflexivity.
  - destruct n as [| n'].
    + destruct (le_t_zero_absurd H).
    + simpl; f_equal.
      exact (IH n' (le_t_SS_inv H)).
Qed.

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ord_clamp {n : nat} (k : nat) : Ord_obj (S n) :=
  ord_at (Nat.min k n) (le_t_SS (le_t_min k n)).

Lemma ord_clamp_id {n} (x : Ord_obj (S n)) : ord_clamp (ord_val x) = x.
Proof.
  apply ord_obj_eq; simpl.
  apply le_t_min_l.
  exact (le_t_SS_inv (ord_bound x)).
Qed.

Definition ord_mor_of_eq {n} {x y : Ord_obj n} (e : x = y) :
  @hom (Ordinal n) x y :=
  match e in _ = z return @hom (Ordinal n) x z with
  | eq_refl => le_t_n
  end.

(* Equal 对象 thin 范畴 have canonical 同构, 函子
 carries it over; inverse laws follow thinness alone. （已译） *)
Program Definition ord_functor_iso {n} {C : Category} (F : Ordinal n ⟶ C)
  {x y : Ord_obj n} (e : x = y) : F x ≅ F y := {|
  to   := fmap[F] (ord_mor_of_eq e);
  from := fmap[F] (ord_mor_of_eq (eq_sym e))
|}.
Solve All Obligations with
  (intros; rewrite <- fmap_comp; rewrite <- (@fmap_id _ _ F _);
   apply fmap_respects, le_t_irr).

Lemma ord_clamp_eq {n} (k : nat) (H : le_t k n) :
  @ord_clamp n k = ord_at k (le_t_SS H).
Proof. apply ord_obj_eq; simpl; now apply le_t_min_l. Qed.

Definition ord_clamp_step {n} (k : nat) (H : le_t (S k) n) :
  @hom (Ordinal (S n)) (@ord_clamp n k) (@ord_clamp n (S k)).
Proof.
  rewrite (ord_clamp_eq k (le_t_trans (le_t_S le_t_n) H)).
  rewrite (ord_clamp_eq (S k) H).
  exact (le_t_S le_t_n).
Defined.

(* The path underlying 函子: 对象 at clamped indices, its
 arrows at n generating steps. （已译） *)
Definition steps_of_functor {n} {C : Category} (F : Ordinal (S n) ⟶ C) :
  OrdSteps n (fun k => F (@ord_clamp n k)) :=
  fun k H => fmap[F] (ord_clamp_step k H).

Theorem Functor_of_Steps_of_Functor {n} {C : Category} (F : Ordinal (S n) ⟶ C) :
  Functor_of_Steps (steps_of_functor F) ≈ F.
Proof.
  apply (ord_functor_equiv_from_steps
           (Functor_of_Steps (steps_of_functor F)) F
           (fun x => ord_functor_iso F (ord_clamp_id x))).
  intro k.
  rewrite (Functor_of_Steps_step (steps_of_functor F) k).
  unfold steps_of_functor; simpl.
  rewrite <- !fmap_comp.
  apply fmap_respects, le_t_irr.
Qed.

(* ---------- counting the morphisms ---------- *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition le_t_of_leb : ∀ (m n : nat), (Nat.leb m n = true) → le_t m n.
Proof.
  induction m as [| m' IH]; intros n H.
  - exact (le_t_zero n).
  - destruct n as [| n'].
    + simpl in H; discriminate.
    + exact (le_t_SS (IH n' H)).
Defined.

Definition le_t_of_le {m n : nat} (H : (m <= n)%nat) : le_t m n :=
  le_t_of_leb m n (proj2 (PeanoNat.Nat.leb_le m n) H).

Lemma le_t_to_le {m n : nat} (f : le_t m n) : (m <= n)%nat.
Proof.
  destruct (le_t_sum f) as [d Hd].
  lia.
Qed.

(* The total space all 态射 [Ordinal n], bundled endpoints. （已译） *)
Definition OrdMor (n : nat) : Type :=
  { x : Ord_obj n & { y : Ord_obj n & @hom (Ordinal n) x y } }.

Definition ord_coords {n} (m : OrdMor n) : (nat * nat)%type :=
  (ord_val (projT1 m), ord_val (projT1 (projT2 m))).

(* A 态射 determined pair endpoint indices: both 对象
 (their bounds being irrelevant) arrow between them (thinness). （已译） *)
Theorem ord_coords_inj {n} (a b : OrdMor n) : ord_coords a = ord_coords b → a = b.
Proof.
  destruct a as [x [y f]], b as [x' [y' f']].
  unfold ord_coords; simpl; intro E.
  assert (E1 : ord_val x = ord_val x') by (now inversion E).
  assert (E2 : ord_val y = ord_val y') by (now inversion E).
  pose proof (ord_obj_eq E1) as Ex.
  pose proof (ord_obj_eq E2) as Ey.
  subst x' y'.
  now rewrite (le_t_irr f f').
Qed.

(* 相关说明。 （已译） *)
Theorem ord_coords_range {n} (m : OrdMor n) :
  (le_t (fst (ord_coords m)) (snd (ord_coords m)) *
   le_t (S (snd (ord_coords m))) n)%type.
Proof.
  destruct m as [x [y f]]; simpl.
  exact (f, ord_bound y).
Qed.

Definition ord_mor_of_coords {n} (i j : nat) (f : le_t i j) (H : le_t (S j) n) :
  OrdMor n :=
  existT _ (ord_at i (le_t_trans (le_t_SS f) H))
           (existT _ (ord_at j H) f).

(* 相关说明。 （已译） *)
Theorem ord_coords_onto {n} (i j : nat) (f : le_t i j) (H : le_t (S j) n) :
  ord_coords (ord_mor_of_coords i j f H) = (i, j).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Fixpoint ord_downto (k : nat) : list nat :=
  match k with
  | O    => cons O nil
  | S k' => cons (S k') (ord_downto k')
  end.

Fixpoint ord_tri (n : nat) : nat :=
  match n with
  | O   => O
  | S k => (S k + ord_tri k)%nat
  end.

Fixpoint ord_pairs (n : nat) : list (nat * nat) :=
  match n with
  | O   => nil
  | S k => app (map (fun i => (i, k)) (ord_downto k)) (ord_pairs k)
  end.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ord_len_app {A} (l l' : list A) :
  (length (app l l') = length l + length l')%nat.
Proof. induction l as [| a l IH]; simpl; auto. Qed.

Lemma ord_len_map {A B} (f : A → B) (l : list A) :
  (length (map f l) = length l)%nat.
Proof. induction l as [| a l IH]; simpl; auto. Qed.

Lemma ord_downto_length (k : nat) : (length (ord_downto k) = S k)%nat.
Proof. induction k as [| k' IH]; simpl; auto. Qed.

Lemma ord_downto_le (k i : nat) : In i (ord_downto k) → (i <= k)%nat.
Proof.
  induction k as [| k' IH]; simpl; intros [H | H].
  - lia.
  - contradiction.
  - lia.
  - pose proof (IH H); lia.
Qed.

Lemma ord_downto_complete (k i : nat) : (i <= k)%nat → In i (ord_downto k).
Proof.
  induction k as [| k' IH]; simpl; intro H.
  - left; lia.
  - destruct (PeanoNat.Nat.eq_dec i (S k')) as [E | E].
    + left; lia.
    + right; apply IH; lia.
Qed.

Lemma ord_downto_nodup (k : nat) : NoDup (ord_downto k).
Proof.
  induction k as [| k' IH]; simpl.
  - constructor; [ simpl; tauto | constructor ].
  - constructor.
    + intro Hin.
      pose proof (ord_downto_le k' (S k') Hin); lia.
    + exact IH.
Qed.

Lemma ord_nodup_app {A} (l l' : list A) :
  NoDup l → NoDup l' → (∀ x, In x l → In x l' → False) → NoDup (app l l').
Proof.
  induction l as [| a l IH]; simpl; intros H1 H2 Hd.
  - exact H2.
  - inversion H1 as [| a' l'' Hnin Hnd]; subst.
    constructor.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * contradiction.
      * exact (Hd a (or_introl eq_refl) Hin).
    + apply IH; auto.
      intros x Hx Hx'.
      exact (Hd x (or_intror Hx) Hx').
Qed.

Lemma ord_nodup_map_inj {A B} (f : A → B) (l : list A) :
  (∀ x y, f x = f y → x = y) → NoDup l → NoDup (map f l).
Proof.
  intros Hinj Hnd.
  induction Hnd as [| a l Hnin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [b [Hb Hbin]].
      apply Hinj in Hb; subst b.
      contradiction.
    + exact IH.
Qed.

Lemma ord_pairs_length (n : nat) : (length (ord_pairs n) = ord_tri n)%nat.
Proof.
  induction n as [| k IH]; simpl; auto.
  now rewrite ord_len_app, ord_len_map, ord_downto_length, IH.
Qed.

(* 相关说明。 （已译） *)
Theorem ord_tri_closed (n : nat) : (2 * ord_tri n = n * (n + 1))%nat.
Proof.
  induction n as [| k IH]; simpl; [ reflexivity |].
  nia.
Qed.

Lemma ord_pairs_sound (n i j : nat) :
  In (i, j) (ord_pairs n) → ((i <= j)%nat /\ (j < n)%nat).
Proof.
  induction n as [| k IH]; simpl; intro Hin.
  - contradiction.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin.
      destruct Hin as [i0 [E Hi0]].
      assert (Ei : i0 = i) by (now inversion E).
      assert (Ej : k = j) by (now inversion E).
      subst i0.
      pose proof (ord_downto_le k i Hi0); lia.
    + destruct (IH Hin); lia.
Qed.

Lemma ord_pairs_complete (n i j : nat) :
  (i <= j)%nat → (j < n)%nat → In (i, j) (ord_pairs n).
Proof.
  revert i j; induction n as [| k IH]; simpl; intros i j Hij Hj.
  - lia.
  - apply in_or_app.
    destruct (PeanoNat.Nat.eq_dec j k) as [E | E].
    + left; subst j.
      apply in_map_iff.
      exists i; split; [ reflexivity |].
      apply ord_downto_complete; lia.
    + right; apply IH; lia.
Qed.

Theorem ord_pairs_nodup (n : nat) : NoDup (ord_pairs n).
Proof.
  induction n as [| k IH]; simpl.
  - constructor.
  - apply ord_nodup_app.
    + apply ord_nodup_map_inj.
      * intros x y E; now inversion E.
      * apply ord_downto_nodup.
    + exact IH.
    + intros [i j] Hin1 Hin2.
      apply in_map_iff in Hin1.
      destruct Hin1 as [i0 [E _]].
      assert (Ej : k = j) by (now inversion E).
      subst j.
      destruct (ord_pairs_sound k i k Hin2); lia.
Qed.

(* The count, assembled: [ord_coords] injection 态射 of
 [Ordinal n] ONTO elements [ord_pairs n], list without repetitions
 whose length t satisfies 2t = n(n+1). （已译） *)
Theorem ord_coords_in_pairs {n} (m : OrdMor n) : In (ord_coords m) (ord_pairs n).
Proof.
  destruct (ord_coords_range m) as [Hle Hlt].
  destruct (ord_coords m) as [i j] eqn:E; simpl in *.
  apply ord_pairs_complete.
  - exact (le_t_to_le Hle).
  - pose proof (le_t_to_le Hlt); lia.
Qed.

Theorem ord_mor_of_pair {n} (i j : nat) (Hij : (i <= j)%nat) (Hj : (j < n)%nat) :
  { m : OrdMor n & ord_coords m = (i, j) }.
Proof.
  exists (ord_mor_of_coords i j (le_t_of_le Hij) (le_t_of_le Hj)).
  reflexivity.
Qed.

Theorem ord_morphism_count (n : nat) :
  (2 * length (ord_pairs n) = n * (n + 1))%nat.
Proof. now rewrite ord_pairs_length, ord_tri_closed. Qed.

Example ord_tri_3 : ord_tri 3 = 6%nat := eq_refl.
Example ord_pairs_3 : length (ord_pairs 3) = 6%nat := eq_refl.
Example ord_tri_4 : ord_tri 4 = 10%nat := eq_refl.

(* 相关说明。 （已译） *)

Require Import Coq.Vectors.Fin.

Fixpoint fin_val {n} (i : Fin.t n) : nat :=
  match i with
  | Fin.F1   => O
  | Fin.FS j => S (fin_val j)
  end.

Fixpoint fin_bound {n} (i : Fin.t n) : le_t (S (fin_val i)) n :=
  match i as i0 in Fin.t n0 return le_t (S (fin_val i0)) n0 with
  | Fin.F1   => le_t_SS (le_t_zero _)
  | Fin.FS j => le_t_SS (fin_bound j)
  end.

Definition ord_of_fin {n} (i : Fin.t n) : Ord_obj n :=
  ord_at (fin_val i) (fin_bound i).

Fixpoint fin_of_nat (k n : nat) : le_t (S k) n → Fin.t n :=
  match n as n0 return le_t (S k) n0 → Fin.t n0 with
  | O    => fun H => False_rect _ (le_t_zero_absurd H)
  | S n' =>
      match k as k0 return le_t (S k0) (S n') → Fin.t (S n') with
      | O    => fun _ => Fin.F1
      | S k' => fun H => Fin.FS (fin_of_nat k' n' (le_t_SS_inv H))
      end
  end.

Definition fin_of_ord {n} (x : Ord_obj n) : Fin.t n :=
  fin_of_nat (ord_val x) n (ord_bound x).

Lemma fin_val_of_nat (k n : nat) (H : le_t (S k) n) :
  fin_val (fin_of_nat k n H) = k.
Proof.
  revert k H; induction n as [| n' IH]; intros k H.
  - destruct (le_t_zero_absurd H).
  - destruct k as [| k']; simpl.
    + reflexivity.
    + now rewrite IH.
Qed.

Theorem ord_of_fin_of_ord {n} (x : Ord_obj n) : ord_of_fin (fin_of_ord x) = x.
Proof.
  apply ord_obj_eq; simpl.
  apply fin_val_of_nat.
Qed.

Theorem fin_of_ord_of_fin {n} (i : Fin.t n) : fin_of_ord (ord_of_fin i) = i.
Proof.
  unfold fin_of_ord, ord_of_fin; simpl.
  induction i as [n' | n' i' IH]; simpl.
  - reflexivity.
  - f_equal.
    rewrite (le_t_irr (le_t_SS_inv (le_t_SS (fin_bound i'))) (fin_bound i')).
    exact IH.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Instance.Cat.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.

Lemma ord_0_empty (x : Ord_obj 0%nat) : False.
Proof. exact (le_t_zero_absurd (ord_bound x)). Qed.

Program Definition Ordinal_0_to : Ordinal 0%nat ⟶ _0 := {|
  fobj := fun x => False_rect _ (ord_0_empty x);
  fmap := fun x _ _ => False_rect _ (ord_0_empty x)
|}.
Solve All Obligations with (intros; destruct (ord_0_empty x)).

Program Definition Ordinal_0_iso : Ordinal 0%nat ≅[Cat] _0 := {|
  to   := Ordinal_0_to;
  from := From_0 (Ordinal 0%nat)
|}.
Solve All Obligations with
  (unshelve refine (existT _ _ _);
   [ intro x | intros x y f ];
   first [ destruct (ord_0_empty x) | destruct x ]).

Lemma ord_1_val (x : Ord_obj 1%nat) : (ord_val x = 0)%nat.
Proof.
  destruct x as [i H]; simpl.
  destruct i as [| i']; [ reflexivity |].
  destruct (le_t_zero_absurd (le_t_SS_inv H)).
Qed.

Program Definition Ordinal_1_from : _1 ⟶ Ordinal 1%nat := {|
  fobj := fun _ => ord_at 0%nat le_t_n;
  fmap := fun _ _ _ => le_t_n
|}.

Program Definition Ordinal_1_iso : Ordinal 1%nat ≅[Cat] _1 := {|
  to   := Erase (Ordinal 1%nat);
  from := Ordinal_1_from
|}.
Next Obligation.
  unshelve refine (existT _ _ _).
  - intro x; destruct x; exact iso_id.
  - intros x y f; destruct x, y; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun x => @ord_iso 1%nat (ord_at 0%nat le_t_n) x (eq_sym (ord_1_val x))).
  intros x y f; simpl.
  apply le_t_irr.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ord_two_thin {a b : TwoObj} (f g : TwoHom a b) : f = g.
Proof.
  pose proof (TwoHom_inv a b f) as Hf.
  pose proof (TwoHom_inv a b g) as Hg.
  destruct a, b; simpl in *; try contradiction; congruence.
Qed.

Definition ord_two_of (i : nat) : TwoObj :=
  match i with
  | O   => TwoX
  | S _ => TwoY
  end.

Definition ord2_map (i j : nat) : le_t i j → TwoHom (ord_two_of i) (ord_two_of j) :=
  match i as i0, j as j0
    return le_t i0 j0 → TwoHom (ord_two_of i0) (ord_two_of j0) with
  | O, O     => fun _ => TwoIdX
  | O, S _   => fun _ => TwoXY
  | S _, O   => fun f => False_rect _ (le_t_zero_absurd f)
  | S _, S _ => fun _ => TwoIdY
  end.

Program Definition Ordinal_2_to : Ordinal 2 ⟶ _2 := {|
  fobj := fun x => ord_two_of (ord_val x);
  fmap := fun x y f => ord2_map (ord_val x) (ord_val y) f
|}.
Solve All Obligations with (intros; apply ord_two_thin).

Definition ord2_obj (a : TwoObj) : Ord_obj 2 :=
  match a with
  | TwoX => ord_at 0%nat (le_t_S le_t_n)
  | TwoY => ord_at 1%nat le_t_n
  end.

Definition ord2_hom {a b : TwoObj} (f : TwoHom a b) :
  @hom (Ordinal 2) (ord2_obj a) (ord2_obj b) :=
  match f with
  | TwoIdX => le_t_n
  | TwoIdY => le_t_n
  | TwoXY  => le_t_S le_t_n
  end.

Program Definition Ordinal_2_from : _2 ⟶ Ordinal 2 := {|
  fobj := ord2_obj;
  fmap := fun _ _ f => ord2_hom f
|}.
Solve All Obligations with (intros; apply le_t_irr).

Lemma ord_2_val (x : Ord_obj 2) :
  ord_val (ord2_obj (ord_two_of (ord_val x))) = ord_val x.
Proof.
  destruct x as [i H]; simpl.
  destruct i as [| i']; [ reflexivity |].
  destruct i' as [| i'']; [ reflexivity |].
  destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H))).
Qed.

Program Definition Ordinal_2_iso : Ordinal 2 ≅[Cat] _2 := {|
  to   := Ordinal_2_to;
  from := Ordinal_2_from
|}.
Next Obligation.
  unshelve refine (existT _ _ _).
  - intro a; destruct a; exact iso_id.
  - intros a b f; apply ord_two_thin.
Qed.
Next Obligation.
  exists (fun x => ord_iso (ord_2_val x)).
  intros x y f; apply le_t_irr.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Ordinal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition _3@{o h p} : Category@{o h p} := Ordinal@{o h p} 3.
Definition _4@{o h p} : Category@{o h p} := Ordinal@{o h p} 4.

Definition three_steps {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  OrdSteps 3 X :=
  fun k =>
    match k as k0 return le_t (S k0) 3 → X k0 ~> X (S k0) with
    | O            => fun _ => f0
    | S O          => fun _ => f1
    | S (S O)      => fun _ => f2
    | S (S (S k')) => fun H =>
        False_rect _ (le_t_zero_absurd
                        (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H))))
    end.

(* Three composable morphisms give a diagram of shape 4 ... *)
Definition Functor_of_Triple {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  _4 ⟶ C := Functor_of_Steps (three_steps X f0 f1 f2).

Definition ord3_0 : Ord_obj 3 := ord_at 0%nat (le_t_S (le_t_S le_t_n)).
Definition ord3_1 : Ord_obj 3 := ord_at 1%nat (le_t_S le_t_n).
Definition ord3_2 : Ord_obj 3 := ord_at 2%nat le_t_n.

(* ... restricts three generating steps three 态射. （已译） *)
Theorem Functor_of_Triple_step0 {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  fmap[Functor_of_Triple X f0 f1 f2] (ord_step ord3_0) ≈ f0.
Proof. exact (Functor_of_Steps_step (three_steps X f0 f1 f2) ord3_0). Qed.

Theorem Functor_of_Triple_step1 {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  fmap[Functor_of_Triple X f0 f1 f2] (ord_step ord3_1) ≈ f1.
Proof. exact (Functor_of_Steps_step (three_steps X f0 f1 f2) ord3_1). Qed.

Theorem Functor_of_Triple_step2 {C : Category} (X : nat → C)
  (f0 : X 0%nat ~> X 1%nat) (f1 : X 1%nat ~> X 2%nat) (f2 : X 2%nat ~> X 3%nat) :
  fmap[Functor_of_Triple X f0 f1 f2] (ord_step ord3_2) ≈ f2.
Proof. exact (Functor_of_Steps_step (three_steps X f0 f1 f2) ord3_2). Qed.

(* 相关说明。 （已译） *)
Corollary shape_4_from_diagram {C : Category} (F : _4 ⟶ C) :
  Functor_of_Steps (steps_of_functor F) ≈ F.
Proof. exact (Functor_of_Steps_of_Functor F). Qed.

(* 相关说明。 （已译） *)
Theorem ord_4_commutes {C : Category} (F : _4 ⟶ C) (x y : Ord_obj 4)
  (f g : @hom (Ordinal 4) x y) : fmap[F] f ≈ fmap[F] g.
Proof. now rewrite (le_t_irr f g). Qed.

Theorem ord_4_triangle {C : Category} (F : _4 ⟶ C) (x y z : Ord_obj 4)
  (f : @hom (Ordinal 4) x y) (g : @hom (Ordinal 4) y z)
  (h : @hom (Ordinal 4) x z) :
  fmap[F] g ∘ fmap[F] f ≈ fmap[F] h.
Proof.
  rewrite <- fmap_comp.
  apply ord_4_commutes.
Qed.
