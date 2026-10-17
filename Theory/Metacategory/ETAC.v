(** * ETAC: the elementary language of an abstract category, and duality *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(*
 Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §3.1,
 nLab:      https://ncatlab.org/nlab/show/duality
 Wikipedia: https://en.wikipedia.org/wiki/Dual_(category_theory)

   本文件给出 ETAC 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Arrow bundles and endpoint casts *)

(* An arrow together with its endpoints: the semantic domain of the
   language's arrow variables. *)
Definition Arr (C : Category) : Type :=
  { p : obj[C] * obj[C] & fst p ~> snd p }.

Definition arr_dom {C : Category} (f : Arr C) : obj[C] := fst (projT1 f).
Definition arr_cod {C : Category} (f : Arr C) : obj[C] := snd (projT1 f).
Definition arr_map {C : Category} (f : Arr C) : arr_dom f ~> arr_cod f :=
  projT2 f.

(* Endpoint cast: transport a hom along equalities of its endpoints. *)
Definition acast {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : x ~> y) : x' ~> y' :=
  eq_rect x (fun w => w ~> y') (eq_rect y (fun z => x ~> z) f y' ey) x' ex.

Lemma acast_refl {C : Category} {x y : obj[C]} (f : x ~> y) :
  acast eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

(* Casting in the opposite category is casting with the endpoint
   equalities exchanged (design note 3). *)
Lemma acast_op {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : y ~> x) :
  @acast (C^op) x y x' y' ex ey f = @acast C y x y' x' ey ex f.
Proof.
  destruct ex, ey; reflexivity.
Qed.

(*
   Cast 代数, each law by destructing its equalities: a two-sided

   本节说明相关定义、性质与动机。 cast splits into its sides, independent side-casts commute, codomain cast crosses 复合 domain cast. Exported reusable 代数 downstream consumers [acast];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma acast_split {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : x ~> y) :
  acast ex ey f = acast eq_refl ey (acast ex eq_refl f).
Proof. destruct ex, ey; reflexivity. Qed.

Lemma acast_comm {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : x ~> y) :
  acast ex eq_refl (acast eq_refl ey f)
    = acast eq_refl ey (acast ex eq_refl f).
Proof. destruct ex, ey; reflexivity. Qed.

Lemma acast_middle {C : Category} {x y y' z : obj[C]}
  (e : y = y') (f : y' ~> z) (g : x ~> y) :
  f ∘ acast eq_refl e g ≈ acast (eq_sym e) eq_refl f ∘ g.
Proof. destruct e; simpl; reflexivity. Qed.

(* The endpoint swap: an arrow of C, read as an arrow of C^op.  The
   underlying arrow is untouched. *)
Definition op_arr {C : Category} (f : Arr C) : Arr (C^op) :=
  ((arr_cod f, arr_dom f); arr_map f).

Definition unop_arr {C : Category} (f : Arr (C^op)) : Arr C :=
  ((arr_cod f, arr_dom f); arr_map f).

Lemma op_unop_arr {C : Category} (f : Arr (C^op)) :
  op_arr (unop_arr f) = f.
Proof.
  destruct f as [[x y] f]; reflexivity.
Qed.

(*
   本节说明相关定义、性质与动机。 The three arrow-equation satisfactions, standalone: stated over.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sat_id {C : Category} (a : obj[C]) (f : Arr C) : Type :=
  { ed : arr_dom f = a
  & { ec : arr_cod f = a
    & acast ed ec (arr_map f) ≈ id[a] } }.

Definition sat_comp {C : Category} (h g f : Arr C) : Type :=
  { e1 : arr_dom f = arr_dom h
  & { e2 : arr_cod f = arr_dom g
    & { e3 : arr_cod g = arr_cod h
      & acast eq_refl e3 (arr_map g) ∘ acast e1 e2 (arr_map f)
          ≈ arr_map h } } }.

Definition sat_eqarr {C : Category} (f g : Arr C) : Type :=
  { ed : arr_dom f = arr_dom g
  & { ec : arr_cod f = arr_cod g
    & acast ed ec (arr_map f) ≈ arr_map g } }.

(*
   本节说明相关定义、性质与动机。 Bundles are propositionally their own eta-expansions; rewriting along.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma arr_eta {C : Category} (s : Arr C) :
  s = ((arr_dom s, arr_cod s); arr_map s).
Proof.
  destruct s as [[x y] m]; reflexivity.
Qed.

Lemma sat_id_op_gen {C : Category} (a x y : obj[C]) (m : x ~> y) :
  sat_id a (((x, y); m) : Arr C) →
  @sat_id (C^op) a (op_arr (((x, y); m) : Arr C)).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  destruct ed.
  revert m H; destruct ec; intros m H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_id_unop_gen {C : Category} (a x y : obj[C]) (m : x ~> y) :
  @sat_id (C^op) a (op_arr (((x, y); m) : Arr C)) →
  sat_id a (((x, y); m) : Arr C).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  destruct ed.
  revert m H; destruct ec; intros m H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_comp_op_gen {C : Category}
  (xh yh xg yg xf yf : obj[C])
  (mh : xh ~> yh) (mg : xg ~> yg) (mf : xf ~> yf) :
  sat_comp (((xh, yh); mh) : Arr C) ((xf, yf); mf) ((xg, yg); mg) →
  @sat_comp (C^op)
    (op_arr (((xh, yh); mh) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C))
    (op_arr (((xf, yf); mf) : Arr C)).
Proof.
  intros [e1 [e2 [e3 H]]]; cbn in e1, e2, e3.
  revert mh mg mf H; destruct e1, e2, e3; intros mh mg mf H.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_comp_unop_gen {C : Category}
  (xh yh xg yg xf yf : obj[C])
  (mh : xh ~> yh) (mg : xg ~> yg) (mf : xf ~> yf) :
  @sat_comp (C^op)
    (op_arr (((xh, yh); mh) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C))
    (op_arr (((xf, yf); mf) : Arr C)) →
  sat_comp (((xh, yh); mh) : Arr C) ((xf, yf); mf) ((xg, yg); mg).
Proof.
  intros [e1 [e2 [e3 H]]]; cbn in e1, e2, e3.
  revert mh mg mf H; destruct e1, e2, e3; intros mh mg mf H.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_eqarr_op_gen {C : Category}
  (xf yf xg yg : obj[C]) (mf : xf ~> yf) (mg : xg ~> yg) :
  sat_eqarr (((xf, yf); mf) : Arr C) ((xg, yg); mg) →
  @sat_eqarr (C^op)
    (op_arr (((xf, yf); mf) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C)).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  revert mf mg H; destruct ed, ec; intros mf mg H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_eqarr_unop_gen {C : Category}
  (xf yf xg yg : obj[C]) (mf : xf ~> yf) (mg : xg ~> yg) :
  @sat_eqarr (C^op)
    (op_arr (((xf, yf); mf) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C)) →
  sat_eqarr (((xf, yf); mf) : Arr C) ((xg, yg); mg).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  revert mf mg H; destruct ed, ec; intros mf mg H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_id_op {C : Category} (a : obj[C]) (f : Arr C) :
  sat_id a f → @sat_id (C^op) a (op_arr f).
Proof.
  rewrite (arr_eta f); apply sat_id_op_gen.
Qed.

Lemma sat_id_unop {C : Category} (a : obj[C]) (f : Arr C) :
  @sat_id (C^op) a (op_arr f) → sat_id a f.
Proof.
  rewrite (arr_eta f); apply sat_id_unop_gen.
Qed.

Lemma sat_comp_op {C : Category} (h g f : Arr C) :
  sat_comp h f g → @sat_comp (C^op) (op_arr h) (op_arr g) (op_arr f).
Proof.
  rewrite (arr_eta h), (arr_eta g), (arr_eta f); apply sat_comp_op_gen.
Qed.

Lemma sat_comp_unop {C : Category} (h g f : Arr C) :
  @sat_comp (C^op) (op_arr h) (op_arr g) (op_arr f) → sat_comp h f g.
Proof.
  rewrite (arr_eta h), (arr_eta g), (arr_eta f); apply sat_comp_unop_gen.
Qed.

Lemma sat_eqarr_op {C : Category} (f g : Arr C) :
  sat_eqarr f g → @sat_eqarr (C^op) (op_arr f) (op_arr g).
Proof.
  rewrite (arr_eta f), (arr_eta g); apply sat_eqarr_op_gen.
Qed.

Lemma sat_eqarr_unop {C : Category} (f g : Arr C) :
  @sat_eqarr (C^op) (op_arr f) (op_arr g) → sat_eqarr f g.
Proof.
  rewrite (arr_eta f), (arr_eta g); apply sat_eqarr_unop_gen.
Qed.

(** ** Syntax *)

(* Atoms, over de Bruijn indices into the two sorts. *)
Inductive atom : Type :=
  | ADom (f a : nat)          (* object a is the domain of arrow f *)
  | ACod (f a : nat)          (* object a is the codomain of arrow f *)
  | AId (a f : nat)           (* arrow f is the identity arrow of a *)
  | AComp (h g f : nat)       (* h is the composite g ∘ f *)
  | AEqArr (f g : nat)        (* arrows f and g are equal *)
  | AEqOb (a b : nat).        (* objects a and b are equal *)

Inductive formula : Type :=
  | FAtom (t : atom)
  | FTop
  | FBot
  | FAnd (p q : formula)
  | FOr (p q : formula)
  | FImpl (p q : formula)
  | FNot (p : formula)
  | FAllOb (p : formula)      (* binds object variable 0 *)
  | FExOb (p : formula)
  | FAllArr (p : formula)     (* binds arrow variable 0 *)
  | FExArr (p : formula).

(** ** Satisfaction *)

Section Satisfaction.

Context {C : Category}.

Definition ocons (x : obj[C]) (ρ : nat → obj[C]) : nat → obj[C] :=
  fun n => match n with O => x | S k => ρ k end.

Definition acons (s : Arr C) (σ : nat → Arr C) : nat → Arr C :=
  fun n => match n with O => s | S k => σ k end.

(* Satisfaction of an atom.  Object comparisons are Leibniz; the three
   arrow equations are ≈ under endpoint casts carried as data (design
   note 1). *)
Definition holds_atom (ρ : nat → obj[C]) (σ : nat → Arr C)
  (t : atom) : Type :=
  match t with
  | ADom f a => arr_dom (σ f) = ρ a
  | ACod f a => arr_cod (σ f) = ρ a
  | AId a f => sat_id (ρ a) (σ f)
  | AComp h g f => sat_comp (σ h) (σ g) (σ f)
  | AEqArr f g => sat_eqarr (σ f) (σ g)
  | AEqOb a b => ρ a = ρ b
  end.

Fixpoint holds (ρ : nat → obj[C]) (σ : nat → Arr C)
  (p : formula) : Type :=
  match p with
  | FAtom t => holds_atom ρ σ t
  | FTop => poly_unit
  | FBot => False
  | FAnd p q => holds ρ σ p * holds ρ σ q
  | FOr p q => holds ρ σ p + holds ρ σ q
  | FImpl p q => holds ρ σ p → holds ρ σ q
  | FNot p => holds ρ σ p → False
  | FAllOb p => ∀ x : obj[C], holds (ocons x ρ) σ p
  | FExOb p => { x : obj[C] & holds (ocons x ρ) σ p }
  | FAllArr p => ∀ s : Arr C, holds ρ (acons s σ) p
  | FExArr p => { s : Arr C & holds ρ (acons s σ) p }
  end.

End Satisfaction.

(* Satisfaction depends on environments only pointwise. *)
Lemma holds_env_ext {C : Category} (p : formula) :
  ∀ (ρ ρ' : nat → obj[C]) (σ σ' : nat → Arr C),
  (∀ n, ρ n = ρ' n) → (∀ n, σ n = σ' n) →
  holds ρ σ p → holds ρ' σ' p.
Proof.
  induction p; simpl; intros ρ ρ' σ σ' Hρ Hσ H.
  - destruct t; simpl in *;
    repeat rewrite <- (Hσ _); repeat rewrite <- (Hρ _); exact H.
  - exact H.
  - exact H.
  - exact (IHp1 _ _ _ _ Hρ Hσ (fst H), IHp2 _ _ _ _ Hρ Hσ (snd H)).
  - destruct H as [H|H].
    + left; exact (IHp1 _ _ _ _ Hρ Hσ H).
    + right; exact (IHp2 _ _ _ _ Hρ Hσ H).
  - intro Hq.
    refine (IHp2 _ _ _ _ Hρ Hσ (H _)).
    refine (IHp1 _ _ _ _ (fun n => eq_sym (Hρ n))
              (fun n => eq_sym (Hσ n)) Hq).
  - intro Hq.
    refine (H (IHp _ _ _ _ (fun n => eq_sym (Hρ n))
                 (fun n => eq_sym (Hσ n)) Hq)).
  - intro x.
    refine (IHp _ _ _ _ _ Hσ (H x)).
    intros [|n]; simpl; [ reflexivity | exact (Hρ n) ].
  - destruct H as [x H]; exists x.
    refine (IHp _ _ _ _ _ Hσ H).
    intros [|n]; simpl; [ reflexivity | exact (Hρ n) ].
  - intro s.
    refine (IHp _ _ _ _ Hρ _ (H s)).
    intros [|n]; simpl; [ reflexivity | exact (Hσ n) ].
  - destruct H as [s H]; exists s.
    refine (IHp _ _ _ _ Hρ _ H).
    intros [|n]; simpl; [ reflexivity | exact (Hσ n) ].
Qed.

(** ** Sentences: closed formulas *)

(* Well-scopedness below a pair of de Bruijn bounds, and sentences as
   the formulas closed below (0, 0) — Mac Lane's "statements".  A
   sentence's satisfaction does not depend on the environment at all. *)
Definition atom_below (ko ka : nat) (t : atom) : Prop :=
  match t with
  | ADom f a => (f < ka)%nat /\ (a < ko)%nat
  | ACod f a => (f < ka)%nat /\ (a < ko)%nat
  | AId a f => (a < ko)%nat /\ (f < ka)%nat
  | AComp h g f => (h < ka)%nat /\ (g < ka)%nat /\ (f < ka)%nat
  | AEqArr f g => (f < ka)%nat /\ (g < ka)%nat
  | AEqOb a b => (a < ko)%nat /\ (b < ko)%nat
  end.

Fixpoint closed_below (ko ka : nat) (p : formula) : Prop :=
  match p with
  | FAtom t => atom_below ko ka t
  | FTop => True
  | FBot => True
  | FAnd p q => closed_below ko ka p /\ closed_below ko ka q
  | FOr p q => closed_below ko ka p /\ closed_below ko ka q
  | FImpl p q => closed_below ko ka p /\ closed_below ko ka q
  | FNot p => closed_below ko ka p
  | FAllOb p => closed_below (S ko) ka p
  | FExOb p => closed_below (S ko) ka p
  | FAllArr p => closed_below ko (S ka) p
  | FExArr p => closed_below ko (S ka) p
  end.

Definition sentence (p : formula) : Prop := closed_below 0 0 p.

(* Satisfaction of a formula closed below the bounds depends only on the
   environments below them. *)
Lemma holds_agree {C : Category} (p : formula) :
  ∀ (ko ka : nat) (ρ ρ' : nat → obj[C]) (σ σ' : nat → Arr C),
  closed_below ko ka p →
  (∀ n, (n < ko)%nat → ρ n = ρ' n) →
  (∀ n, (n < ka)%nat → σ n = σ' n) →
  holds ρ σ p → holds ρ' σ' p.
Proof.
  induction p; simpl; intros ko ka ρ ρ' σ σ' Hc Hρ Hσ H.
  - destruct t; cbn in Hc; simpl in *.
    + destruct Hc as [Hf Ha].
      rewrite <- (Hσ f Hf), <- (Hρ a Ha); exact H.
    + destruct Hc as [Hf Ha].
      rewrite <- (Hσ f Hf), <- (Hρ a Ha); exact H.
    + destruct Hc as [Ha Hf].
      rewrite <- (Hρ a Ha), <- (Hσ f Hf); exact H.
    + destruct Hc as [Hh [Hg Hf]].
      rewrite <- (Hσ h Hh), <- (Hσ g Hg), <- (Hσ f Hf); exact H.
    + destruct Hc as [Hf Hg].
      rewrite <- (Hσ f Hf), <- (Hσ g Hg); exact H.
    + destruct Hc as [Ha Hb].
      rewrite <- (Hρ a Ha), <- (Hρ b Hb); exact H.
  - exact H.
  - exact H.
  - destruct Hc as [Hc1 Hc2].
    exact (IHp1 _ _ _ _ _ _ Hc1 Hρ Hσ (fst H),
           IHp2 _ _ _ _ _ _ Hc2 Hρ Hσ (snd H)).
  - destruct Hc as [Hc1 Hc2].
    destruct H as [H|H].
    + left; exact (IHp1 _ _ _ _ _ _ Hc1 Hρ Hσ H).
    + right; exact (IHp2 _ _ _ _ _ _ Hc2 Hρ Hσ H).
  - destruct Hc as [Hc1 Hc2].
    intro Hq.
    refine (IHp2 _ _ _ _ _ _ Hc2 Hρ Hσ (H _)).
    refine (IHp1 _ _ _ _ _ _ Hc1
              (fun n Hn => eq_sym (Hρ n Hn))
              (fun n Hn => eq_sym (Hσ n Hn)) Hq).
  - intro Hq.
    refine (H (IHp _ _ _ _ _ _ Hc
                 (fun n Hn => eq_sym (Hρ n Hn))
                 (fun n Hn => eq_sym (Hσ n Hn)) Hq)).
  - intro x.
    refine (IHp _ _ _ _ _ _ Hc _ Hσ (H x)).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hρ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ko) Hn).
  - destruct H as [x H]; exists x.
    refine (IHp _ _ _ _ _ _ Hc _ Hσ H).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hρ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ko) Hn).
  - intro sarr.
    refine (IHp _ _ _ _ _ _ Hc Hρ _ (H sarr)).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hσ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ka) Hn).
  - destruct H as [sarr H]; exists sarr.
    refine (IHp _ _ _ _ _ _ Hc Hρ _ H).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hσ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ka) Hn).
Qed.

(* A sentence's satisfaction is environment-independent. *)
Corollary holds_sentence_env_irrel {C : Category} (p : formula) :
  sentence p →
  ∀ (ρ ρ' : nat → obj[C]) (σ σ' : nat → Arr C),
  holds ρ σ p → holds ρ' σ' p.
Proof.
  intros Hs ρ ρ' σ σ' H.
  refine (holds_agree p 0 0 ρ ρ' σ σ' Hs _ _ H);
  intros n Hn; exfalso; exact (PeanoNat.Nat.nlt_0_r n Hn).
Qed.

(** ** The syntactic dual *)

(* Interchange domain with codomain, reverse composites (Mac Lane
   §II.1's table); identity, equality, and the propositional structure
   are self-dual. *)
Definition dual_atom (t : atom) : atom :=
  match t with
  | ADom f a => ACod f a
  | ACod f a => ADom f a
  | AId a f => AId a f
  | AComp h g f => AComp h f g
  | AEqArr f g => AEqArr f g
  | AEqOb a b => AEqOb a b
  end.

Fixpoint dual (p : formula) : formula :=
  match p with
  | FAtom t => FAtom (dual_atom t)
  | FTop => FTop
  | FBot => FBot
  | FAnd p q => FAnd (dual p) (dual q)
  | FOr p q => FOr (dual p) (dual q)
  | FImpl p q => FImpl (dual p) (dual q)
  | FNot p => FNot (dual p)
  | FAllOb p => FAllOb (dual p)
  | FExOb p => FExOb (dual p)
  | FAllArr p => FAllArr (dual p)
  | FExArr p => FExArr (dual p)
  end.

(* Dualizing twice is the identity, on the nose. *)
Lemma dual_atom_invol (t : atom) : dual_atom (dual_atom t) = t.
Proof. destruct t; reflexivity. Qed.

Lemma dual_invol (p : formula) : dual (dual p) = p.
Proof.
  induction p; simpl;
  try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
  try rewrite dual_atom_invol; reflexivity.
Qed.

(** ** The semantic duality lemma (Mac Lane §II.2) *)

(* Transport an arrow environment to the opposite category. *)
Definition op_env {C : Category} (σ : nat → Arr C) : nat → Arr (C^op) :=
  fun n => op_arr (σ n).

Lemma holds_dual_to {C : Category} (p : formula) :
  ∀ (ρ : nat → obj[C]) (σ : nat → Arr C),
  holds ρ σ (dual p) → @holds (C^op) ρ (op_env σ) p
with holds_dual_from {C : Category} (p : formula) :
  ∀ (ρ : nat → obj[C]) (σ : nat → Arr C),
  @holds (C^op) ρ (op_env σ) p → holds ρ σ (dual p).
Proof.
  - induction p; simpl; intros ρ σ H.
    + destruct t; simpl in *; unfold op_env, op_arr; simpl.
      * exact H.
      * exact H.
      * exact (sat_id_op _ _ H).
      * exact (sat_comp_op _ _ _ H).
      * exact (sat_eqarr_op _ _ H).
      * exact H.
    + exact H.
    + exact H.
    + exact (IHp1 _ _ (fst H), IHp2 _ _ (snd H)).
    + destruct H as [H|H]; [ left; exact (IHp1 _ _ H)
                           | right; exact (IHp2 _ _ H) ].
    + intro Hq; exact (IHp2 _ _ (H (holds_dual_from C p1 _ _ Hq))).
    + intro Hq; exact (H (holds_dual_from C p _ _ Hq)).
    + intro x; exact (IHp _ _ (H x)).
    + destruct H as [x H]; exists x; exact (IHp _ _ H).
    + intro s.
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _
                (IHp _ (acons (unop_arr s) σ) (H (unop_arr s)))).
      intros [|n]; simpl.
      * exact (op_unop_arr s).
      * reflexivity.
    + destruct H as [s H].
      exists (op_arr s).
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _
                (IHp _ (acons s σ) H)).
      intros [|n]; simpl; reflexivity.
  - induction p; simpl; intros ρ σ H.
    + destruct t; simpl in *; unfold op_env, op_arr in H; simpl in H.
      * exact H.
      * exact H.
      * exact (sat_id_unop _ _ H).
      * exact (sat_comp_unop _ _ _ H).
      * exact (sat_eqarr_unop _ _ H).
      * exact H.
    + exact H.
    + exact H.
    + exact (IHp1 _ _ (fst H), IHp2 _ _ (snd H)).
    + destruct H as [H|H]; [ left; exact (IHp1 _ _ H)
                           | right; exact (IHp2 _ _ H) ].
    + intro Hq; exact (IHp2 _ _ (H (holds_dual_to C p1 _ _ Hq))).
    + intro Hq; exact (H (holds_dual_to C p _ _ Hq)).
    + intro x; exact (IHp _ _ (H x)).
    + destruct H as [x H]; exists x; exact (IHp _ _ H).
    + intro s.
      refine (IHp _ (acons s σ) _).
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _
                (H (op_arr s))).
      intros [|n]; simpl; reflexivity.
    + destruct H as [s H].
      exists (unop_arr s).
      refine (IHp _ (acons (unop_arr s) σ) _).
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _ H).
      intros [|n]; simpl.
      * exact (eq_sym (op_unop_arr s)).
      * reflexivity.
Qed.

(* The lemma in its stated form: C satisfies the dual of Σ under an
   assignment iff C^op satisfies Σ under the transported assignment. *)
Definition holds_dual {C : Category} (p : formula)
  (ρ : nat → obj[C]) (σ : nat → Arr C) :
  holds ρ σ (dual p) ↔ @holds (C^op) ρ (op_env σ) p :=
  (holds_dual_to p ρ σ, holds_dual_from p ρ σ).

(** ** The duality principle (Mac Lane §II.1, Awodey §3.1) *)

(* A formula valid in every category under every assignment. *)
Definition valid (p : formula) : Type :=
  ∀ (C : Category) (ρ : nat → obj[C]) (σ : nat → Arr C), holds ρ σ p.

(* If Σ holds in every category, so does its dual: instantiate the
   hypothesis at C^op and transport back — no double-op unwinding
   needed (design note 3). *)
Theorem duality_principle (p : formula) : valid p → valid (dual p).
Proof.
  intros V C ρ σ.
  exact (holds_dual_from p ρ σ (V (Opposite C) ρ (op_env σ))).
Qed.

(* The principle self-composes: applying it twice returns to the
   original statement, by the syntactic involution. *)
Corollary duality_principle_invol (p : formula) :
  valid p → valid (dual (dual p)).
Proof.
  intro V; rewrite dual_invol; exact V.
Qed.

(** ** The one-functor case (maclane:II.1:remark2, scoped) *)

(*
   The one-函子 recording (design note 4): the 对象 and arrow

   本节说明相关定义、性质与动机。 actions F^op are literally those F, stated at BUNDLE level — this is definitional commutation, not statement-level theorem;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* The arrow action of a functor, on bundles. *)
Definition arr_fmap {C D : Category} (F : C ⟶ D) (s : Arr C) : Arr D :=
  ((F (arr_dom s), F (arr_cod s)); fmap[F] (arr_map s)).

Lemma arr_fmap_op {C D : Category} (F : C ⟶ D)
  (s : Arr C) :
  arr_fmap F s = unop_arr (arr_fmap (F^op) (op_arr s)).
Proof.
  destruct s as [[x y] f]; reflexivity.
Qed.
