(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Coq.Lists.List.

Generalizable All Variables.

(** * The category, under the issue's name *)

Definition CompHaus : Category := CompactHausdorffSpaces.

Example CompHaus_is_CompactHausdorffSpaces :
  CompHaus = CompactHausdorffSpaces := eq_refl.

Definition CompHaus_Incl : CompHaus ⟶ Top :=
  Incl Top CompactHausdorff_Subcategory.

Lemma CompHaus_Incl_Full : Functor.Full CompHaus_Incl.
Proof. exact (Full_Implies_Full_Functor Top _ CompactHausdorff_Full). Qed.

Lemma CompHaus_Incl_Faithful : Functor.Faithful CompHaus_Incl.
Proof. exact (Incl_Faithful Top _). Qed.

(** * A continuous bijection from a compact space to a Hausdorff space *)

Section Bijection.
Context {X Y : TopSpace} (f : X ~{Top}~> Y)
        (g : SetoidMorphism (top_carrier Y) (top_carrier X))
        (Hfg : ∀ y : Y, continuous_map f (g y) ≈ y)
        (Hgf : ∀ x : X, g (continuous_map f x) ≈ x)
        (HX : IsCompact X) (HY : IsHausdorff Y).

(* Finite intersections of a list-indexed family of opens of [Y]. *)
Fixpoint finite_inter {I : Type} (B : I → Y → Type) (l : list I) : Y → Type :=
  match l with
  | nil => fun _ => poly_unit
  | cons i l' => fun y => (B i y ∧ finite_inter B l' y)%type
  end.

Lemma finite_inter_open {I : Type} (B : I → Y → Type)
  (HB : ∀ i, IsOpen Y (B i)) (l : list I) : IsOpen Y (finite_inter B l).
Proof using.
  induction l; simpl.
  - apply open_whole.
  - apply open_inter; [apply HB | exact IHl].
Qed.

Lemma finite_inter_all {I : Type} (B : I → Y → Type) (l : list I) (y : Y) :
  (∀ i, B i y) → finite_inter B l y.
Proof using.
  induction l; simpl; intro H.
  - exact ttt.
  - split; [apply H | exact (IHl H)].
Qed.

(* The one use of [List.In], a [Prop], eliminated only into [False]. *)
Lemma finite_inter_In_False {I : Type} (B : I → Y → Type) (l : list I)
  (y : Y) :
  finite_inter B l y → ∀ i, In i l → (B i y → False) → False.
Proof using.
  induction l; simpl; intros H i Hi nb.
  - exact Hi.
  - destruct Hi as [e | Hi].
    + subst; exact (nb (fst H)).
    + exact (IHl (snd H) i Hi nb).
Qed.

Section Open.
Context (U : X → Type) (HU : IsOpen X U)
        (dU : ∀ x : X, U x + (U x → False)).

(* The complement of [U], as a type of points. *)
Definition compl_pts : Type := { c : X & U c → False }.

Section Point.
Context (y0 : Y) (hy0 : U (g y0)).

Lemma sep_nonequal (c : compl_pts) : continuous_map f (`1 c) ≈ y0 → False.
Proof using Hgf HU hy0.
  intro e. apply (`2 c).
  apply (open_proper X U HU (g y0) (`1 c)).
  - rewrite <- (Hgf (`1 c)). apply (proper_morphism g). symmetry. exact e.
  - exact hy0.
Qed.

Definition sepA (c : compl_pts) : Y → Type := `1 (HY _ y0 (sep_nonequal c)).
Definition sepB (c : compl_pts) : Y → Type :=
  `1 (`2 (HY _ y0 (sep_nonequal c))).

Lemma sepA_open (c : compl_pts) : IsOpen Y (sepA c).
Proof using. exact (fst (fst (`2 (`2 (HY _ y0 (sep_nonequal c)))))). Qed.
Lemma sepB_open (c : compl_pts) : IsOpen Y (sepB c).
Proof using. exact (snd (fst (`2 (`2 (HY _ y0 (sep_nonequal c)))))). Qed.
Lemma sepA_at (c : compl_pts) : sepA c (continuous_map f (`1 c)).
Proof using. exact (fst (fst (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))))). Qed.
Lemma sepB_at (c : compl_pts) : sepB c y0.
Proof using. exact (snd (fst (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))))). Qed.
Lemma sep_disjoint (c : compl_pts) (z : Y) : sepA c z → sepB c z → False.
Proof using. exact (snd (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))) z). Qed.

(* The sep_cover of [X]: the preimages of the separating opens, plus [U]. *)
Definition sep_cover_idx : Type := (compl_pts + poly_unit)%type.
Definition sep_cover (i : sep_cover_idx) : X → Type :=
  match i with
  | inl c => fun x => sepA c (continuous_map f x)
  | inr _ => U
  end.

(* This is where membership in [U] is decided. *)
Lemma sep_cover_covers : Covers sep_cover (fun _ => poly_unit).
Proof using HU dU f.
  split.
  - intros [c | u]; simpl.
    + exact (continuity f (sepA c) (sepA_open c)).
    + exact HU.
  - intro x; split.
    + intros _. destruct (dU x) as [u | n].
      * exists (inr ttt); exact u.
      * exists (inl (x; n)); exact (sepA_at (x; n)).
    + intros _; exact ttt.
Qed.

Definition sep_subcover : list sep_cover_idx :=
  `1 (HX sep_cover_idx sep_cover sep_cover_covers).
Definition sep_subcover_covers :
  ∀ x : X, ∃ i : sep_cover_idx, (In i sep_subcover ∧ sep_cover i x)%type :=
  `2 (HX sep_cover_idx sep_cover sep_cover_covers).

(* The [Y]-side family: the separating opens around [y0]; nothing for [U]. *)
Definition sep_fam (i : sep_cover_idx) : Y → Type :=
  match i with
  | inl c => sepB c
  | inr _ => fun _ => poly_unit
  end.

Definition nbhd : Y → Type := finite_inter sep_fam sep_subcover.

Lemma nbhd_open : IsOpen Y nbhd.
Proof using.
  apply finite_inter_open. intros [c | u]; simpl.
  - exact (sepB_open c).
  - exact (open_whole Y).
Qed.

Lemma nbhd_at : nbhd y0.
Proof using.
  apply finite_inter_all. intros [c | u]; simpl.
  - exact (sepB_at c).
  - exact ttt.
Qed.

Lemma nbhd_inside (y' : Y) : nbhd y' → U (g y').
Proof using Hfg HU dU.
  intro hn. destruct (dU (g y')) as [u | n]; [exact u | exfalso].
  destruct (sep_subcover_covers (g y')) as [i [Hin w]].
  destruct i as [c | u]; simpl in w.
  - refine (finite_inter_In_False sep_fam sep_subcover y' hn (inl c) Hin _).
    intro b. apply (sep_disjoint c y').
    + apply (open_proper Y (sepA c) (sepA_open c)
               (continuous_map f (g y')) y').
      * exact (Hfg y').
      * exact w.
    + exact b.
  - exact (n w).
Qed.

End Point.

Theorem inverse_open_of_decidable : IsOpen Y (fun y => U (g y)).
Proof using Hfg Hgf HU HX HY dU f g.
  apply (open_respects Y
           (fun y => { yp : { y0 : Y & U (g y0) } & nbhd (`1 yp) (`2 yp) y })).
  - intro y; split.
    + intros [yp hn]. exact (nbhd_inside (`1 yp) (`2 yp) y hn).
    + intro v. exists (y; v). exact (nbhd_at y v).
  - apply (open_union Y { y0 : Y & U (g y0) }
             (fun yp => nbhd (`1 yp) (`2 yp))).
    intro yp. exact (nbhd_open (`1 yp) (`2 yp)).
Qed.

End Open.

Theorem inverse_continuous_of_decidable
  (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)) :
  Continuous Y X g.
Proof using Hfg Hgf HX HY f g.
  intros U HU. exact (inverse_open_of_decidable U HU (dec U HU)).
Qed.

Definition compact_hausdorff_bijection_iso
  (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)) :
  X ≅[Top] Y.
Proof using Hfg Hgf HX HY f g.
  unshelve refine
    {| to := f
     ; from := Build_ContinuousMorphism Y X g
                 (inverse_continuous_of_decidable dec) |}.
  - intro y; simpl. exact (Hfg y).
  - intro x; simpl. exact (Hgf x).
Defined.

End Bijection.

(** * The truncated product topology: the furthest formable point of (a) *)

Section SquashProduct.

Universe o o1.
Constraint o < o1.
Context (X Y : TopSpace@{o}).

Definition sq_carrier : SetoidObject@{o o} := {|
  carrier := (carrier (top_carrier X) * carrier (top_carrier Y))%type;
  is_setoid := prod_setoid
|}.

(* A box around [p] inside [W]: opens of the factors, data at level [o1]. *)
Definition sq_boxdata (W : sq_carrier → Type@{o}) (p : sq_carrier) :
  Type@{o1} :=
  { U : carrier (top_carrier X) → Type@{o} &
  { V : carrier (top_carrier Y) → Type@{o} &
    (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
       ∧ (∀ q : sq_carrier, U (fst q) → V (snd q) → W q))%type } }.

(* Squashed into a [Prop], the box datum fits at level [o]. *)
Definition sq_open (W : sq_carrier → Type@{o}) : Type@{o} :=
  ((∀ x y : sq_carrier, x ≈ y → W x → W y)
   ∧ (∀ p : sq_carrier, W p → Powerset_squash@{o1} (sq_boxdata W p)))%type.

Lemma sq_squash_map {A B : Type@{o1}} (f : A → B) :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B.
Proof using. intros s Q k; exact (s Q (fun a => k (f a))). Qed.

Lemma sq_squash_pair {A B : Type@{o1}} :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B →
  Powerset_squash@{o1} (A * B)%type.
Proof using.
  intros a b Q k; exact (a Q (fun x => b Q (fun y => k (x, y)))).
Qed.

Definition Top_sq_product : TopSpace@{o}.
Proof using X Y.
  unshelve refine {| top_carrier := sq_carrier; IsOpen := sq_open |}.
  - (* open_respects *)
    intros U V H [Hp Hb]; split.
    + intros x y e u. apply (fst (H y)). apply (Hp x y e). apply (snd (H x)).
      exact u.
    + intros p v. apply (sq_squash_map (A := sq_boxdata U p)).
      * intros [U0 [V0 [oU [oV [u0 [v0 inside]]]]]].
        exists U0; exists V0. repeat split; try assumption.
        intros q0 a0 b0. apply (fst (H q0)). exact (inside q0 a0 b0).
      * apply Hb. apply (snd (H p)). exact v.
  - (* open_proper *)
    intros U [Hp _] x y e u. exact (Hp x y e u).
  - (* open_union *)
    intros I U HU; split.
    + intros x y e [i u]. exists i. exact (fst (HU i) x y e u).
    + intros p [i u]. apply (sq_squash_map (A := sq_boxdata (U i) p)).
      * intros [U0 [V0 [oU [oV [u0 [v0 inside]]]]]].
        exists U0; exists V0. repeat split; try assumption.
        intros q0 a0 b0. exists i. exact (inside q0 a0 b0).
      * exact (snd (HU i) p u).
  - (* open_whole *)
    split.
    + intros; exact ttt.
    + intros p _. apply Powerset_squash_intro.
      exists (fun _ => poly_unit); exists (fun _ => poly_unit).
      repeat split; try exact ttt; try apply open_whole.
  - (* open_inter *)
    intros U V [HpU HbU] [HpV HbV]; split.
    + intros x y e [u v]. split; [exact (HpU x y e u) | exact (HpV x y e v)].
    + intros p [u v].
      apply (sq_squash_map (A := (sq_boxdata U p * sq_boxdata V p)%type)).
      * intros [[U0 [V0 [oU0 [oV0 [u0 [v0 in0]]]]]]
                [U1 [V1 [oU1 [oV1 [u1 [v1 in1]]]]]]].
        exists (fun a => (U0 a ∧ U1 a)%type);
        exists (fun b => (V0 b ∧ V1 b)%type).
        split; [apply open_inter; assumption |].
        split; [apply open_inter; assumption |].
        split; [split; assumption |].
        split; [split; assumption |].
        intros q0 [a0 a1] [b0 b1].
        split; [exact (in0 q0 a0 b0) | exact (in1 q0 a1 b1)].
      * apply sq_squash_pair; [exact (HbU p u) | exact (HbV p v)].
Defined.

Definition sq_fst_map : SetoidMorphism sq_carrier (top_carrier X).
Proof using X Y.
  unshelve notypeclasses refine {| morphism := fun p : sq_carrier => fst p |}.
  intros u v Huv; exact (fst Huv).
Defined.

Definition sq_snd_map : SetoidMorphism sq_carrier (top_carrier Y).
Proof using X Y.
  unshelve notypeclasses refine {| morphism := fun p : sq_carrier => snd p |}.
  intros u v Huv; exact (snd Huv).
Defined.

Lemma sq_fst_continuous : Continuous Top_sq_product X sq_fst_map.
Proof using X Y.
  intros U HU; split.
  - intros x y [e _] u. exact (open_proper X U HU (fst x) (fst y) e u).
  - intros p u. apply Powerset_squash_intro.
    exists U; exists (fun _ => poly_unit).
    repeat split; try assumption; try apply open_whole; try exact ttt.
    intros q0 a0 _; exact a0.
Qed.

Lemma sq_snd_continuous : Continuous Top_sq_product Y sq_snd_map.
Proof using X Y.
  intros V HV; split.
  - intros x y [_ e] v. exact (open_proper Y V HV (snd x) (snd y) e v).
  - intros p v. apply Powerset_squash_intro.
    exists (fun _ => poly_unit); exists V.
    repeat split; try assumption; try apply open_whole; try exact ttt.
    intros q0 _ b0; exact b0.
Qed.

Definition Top_sq_fst : Top_sq_product ~{Top}~> X :=
  Build_ContinuousMorphism Top_sq_product X sq_fst_map sq_fst_continuous.

Definition Top_sq_snd : Top_sq_product ~{Top}~> Y :=
  Build_ContinuousMorphism Top_sq_product Y sq_snd_map sq_snd_continuous.

(* The pairing exists at the level of setoids; its CONTINUITY is what the
   probe pins as refused. *)
Definition sq_fork_map {Z : TopSpace@{o}}
  (f : Z ~{Top}~> X) (g : Z ~{Top}~> Y) :
  SetoidMorphism (top_carrier Z) sq_carrier.
Proof using X Y.
  unshelve notypeclasses refine
    {| morphism := fun z => (continuous_map f z, continuous_map g z) |}.
  intros u v Huv; split.
  - exact (proper_morphism (continuous_map f) u v Huv).
  - exact (proper_morphism (continuous_map g) u v Huv).
Defined.

End SquashProduct.

(** * The forgetful functor, and creation *)

Definition CompHaus_Forget := Top_Forget ◯ CompHaus_Incl.

Lemma CompHaus_Forget_Faithful : Functor.Faithful CompHaus_Forget.
Proof.
  constructor; intros X Y h k E.
  apply (@fmap_inj _ _ _ CompHaus_Incl_Faithful X Y h k).
  apply (@fmap_inj _ _ _ Top_Forget_Faithful _ _ _ _).
  exact E.
Qed.

(* Creation by the INCLUSION, from the generic lemma, under closure of the
   compact Hausdorff predicate under the limits of [Top]. *)
Definition CompHaus_Incl_CreatesLimit
  (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
  {J : Category} (K : J ⟶ CompHaus) : CreatesLimit K CompHaus_Incl :=
  sub_CreatesLimit CompactHausdorff_Subcategory CompactHausdorff_Full closed K.

Definition CompHaus_Complete_of
  (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
  (HT : @Complete Top) : @Complete CompHaus :=
  sub_Complete CompactHausdorff_Subcategory CompactHausdorff_Full closed HT.
