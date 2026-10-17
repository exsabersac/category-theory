Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.SlicedInverse.
Require Import Category.Structure.SlicedInverse.Strict.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/subspace+topology
 nLab:      https://ncatlab.org/nlab/show/quotient+space
 nLab:      https://ncatlab.org/nlab/show/initial+topology
 nLab:      https://ncatlab.org/nlab/show/topological+concrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

Section Subspace.

Universe o.

Context (X : PTop@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S X).

(* Mac Lane's predicate: V is open when it is the preimage along [h] of an
   open of X. *)
Definition psub_open (V : S → Prop) : Prop :=
  ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s)).

Lemma psub_open_respects (U V : S → Prop) :
  (∀ s, U s <-> V s) → psub_open U → psub_open V.
Proof.
  intros HUV [B [HB HUB]]. exists B; split; [exact HB|].
  intro s; split.
  - intro v; exact (proj1 (HUB s) (proj2 (HUV s) v)).
  - intro b; exact (proj1 (HUV s) (proj2 (HUB s) b)).
Qed.

Lemma psub_open_proper (U : S → Prop) :
  psub_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof.
  intros [B [HB HUB]] s t e u. apply (proj2 (HUB t)).
  exact (popen_proper X B HB (h s) (h t) (proper_morphism h s t e)
           (proj1 (HUB s) u)).
Qed.

(* 相关说明。 （已译） *)
Lemma psub_open_union (F : (S → Prop) → Prop) :
  (∀ V, F V → psub_open V) →
  psub_open (fun s => ex (fun V => F V /\ V s)).
Proof.
  intro HF.
  exists (fun x => ex (fun U => (POpen X U /\
                                 ex (fun V => F V /\ ∀ s, V s <-> U (h s)))
                                /\ U x)).
  split.
  - apply popen_union. intros U [HU _]; exact HU.
  - intro s; split.
    + intros [V [FV v]]. destruct (HF V FV) as [U [HU HVU]].
      exists U. split; [split; [exact HU|]|].
      * exists V; split; [exact FV|exact HVU].
      * exact (proj1 (HVU s) v).
    + intros [U [[_ [V [FV HVU]]] u]].
      exists V; split; [exact FV|exact (proj2 (HVU s) u)].
Qed.

Lemma psub_open_whole : psub_open (fun _ => True).
Proof.
  exists (fun _ => True); split; [exact (popen_whole X)|].
  intro s; exact (iff_refl _).
Qed.

Lemma psub_open_inter (U V : S → Prop) :
  psub_open U → psub_open V → psub_open (fun s => U s /\ V s).
Proof.
  intros [A [HA HUA]] [B [HB HVB]].
  exists (fun x => A x /\ B x); split.
  - exact (popen_inter X A B HA HB).
  - intro s; split.
    + intros [u v]; exact (conj (proj1 (HUA s) u) (proj1 (HVB s) v)).
    + intros [a b]; exact (conj (proj2 (HUA s) a) (proj2 (HVB s) b)).
Qed.

Definition PSub : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := psub_open;
  popen_respects := psub_open_respects;
  popen_proper   := psub_open_proper;
  popen_union    := psub_open_union;
  popen_whole    := psub_open_whole;
  popen_inter    := psub_open_inter
|}.

(* 相关说明。 （已译） *)
Example PSub_carrier : pt_carrier PSub = S := eq_refl.

Example PSub_open (V : S → Prop) :
  POpen PSub V = ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s))
  := eq_refl.

(* [h] is continuous out of the subspace. *)
Lemma psub_incl_cont : @PCont PSub X h.
Proof.
  intros U HU. exists U; split; [exact HU|].
  intro s; exact (iff_refl _).
Qed.

Definition psub_incl : PMor@{o} PSub X :=
  @Build_PMor PSub X h psub_incl_cont.

(* The 普遍性质, over ARBITRARY spaces [Z] 映射 in: setoid
 map 进入 subspace continuous exactly 复合 [h]
 is. （已译） *)
Lemma psub_universal (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z PSub g <-> @PCont Z X (setoid_morphism_compose h g).
Proof.
  split.
  - intros Hg U HU. exact (Hg _ (psub_incl_cont U HU)).
  - intros Hc V [U [HU HVU]].
    apply (popen_respects Z (fun z => U (h (g z)))).
    + intro z; exact (iff_sym (HVU (g z))).
    + exact (Hc U HU).
Qed.

(* The book's form: continuous [f : Z → X] whose underlying function
 factors [h ∘ g] has [g] continuous 进入 subspace. （已译） *)
Definition psub_lift (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  PMor@{o} Z PSub :=
  @Build_PMor Z PSub g
    (proj2 (psub_universal Z g)
       (pcont_respects (pmap f) (setoid_morphism_compose h g) Hfg (pcont f))).

Example psub_lift_map (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  pmap (psub_lift Z f g Hfg) = g := eq_refl.

Lemma psub_lift_comm (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  ∀ z, pmap (pcompose psub_incl (psub_lift Z f g Hfg)) z ≈ pmap f z.
Proof. intro z; symmetry; exact (Hfg z). Qed.

End Subspace.

(* 相关说明。 （已译） *)

Section Ex732.

Universe o.

Context (X : PTop@{o}) (P : X → Prop).

(* 相关说明。 （已译） *)
Program Definition ex732_Y : SetoidObject@{o o} := {|
  carrier := { x : X | P x };
  is_setoid := {| equiv := fun a b => proj1_sig a ≈ proj1_sig b |}
|}.
Next Obligation.
  constructor.
  - intros a; reflexivity.
  - intros a b H; symmetry; exact H.
  - intros a b c H1 H2; transitivity (proj1_sig b); assumption.
Qed.

Program Definition ex732_incl : SetoidMorphism@{o o o} ex732_Y X := {|
  morphism := fun a => proj1_sig a
|}.
Next Obligation. intros a b H; exact H. Qed.

Definition ex732_Sub : PTop@{o} := PSub X ex732_Y ex732_incl.

(* The 定义: [A ⊆ Y] open iff [A = B ∩ Y] some open [B] of
 [X]. （已译） *)
Example ex732_def (A : ex732_Y → Prop) :
  POpen ex732_Sub A
  = ex (fun B : X → Prop =>
          POpen X B /\ ∀ y : ex732_Y, A y <-> B (proj1_sig y)) := eq_refl.

(* Part 1: [Y] itself is open, [B] being the whole of [X]. *)
Lemma ex732_part1 :
  POpen X (fun _ => True)
  /\ (∀ y : ex732_Y, True <-> (fun _ : X => True) (proj1_sig y))
  /\ POpen ex732_Sub (fun _ => True).
Proof.
  split; [exact (popen_whole X)|split].
  - intro y; exact (iff_refl _).
  - exists (fun _ => True); split; [exact (popen_whole X)|].
    intro y; exact (iff_refl _).
Qed.

(* 相关说明。 （已译） *)
Lemma ex732_part2 :
  POpen ex732_Sub (fun _ => True)
  /\ (∀ A B : ex732_Y → Prop, POpen ex732_Sub A → POpen ex732_Sub B →
        POpen ex732_Sub (fun y => A y /\ B y))
  /\ (∀ (I : Type) (A : I → ex732_Y → Prop), (∀ k, POpen ex732_Sub (A k)) →
        POpen ex732_Sub (fun y => ex (fun k => A k y))).
Proof.
  split; [exact (psub_open_whole X ex732_Y ex732_incl)|split].
  - exact (psub_open_inter X ex732_Y ex732_incl).
  - intros I A HA. exact (popen_union_indexed ex732_Sub I A HA).
Qed.

(* Part 3: the inclusion is continuous. *)
Lemma ex732_part3 : @PCont ex732_Sub X ex732_incl.
Proof. exact (psub_incl_cont X ex732_Y ex732_incl). Qed.

Definition ex732_incl_mor : PMor@{o} ex732_Sub X :=
  psub_incl X ex732_Y ex732_incl.

End Ex732.

(* 相关说明。 （已译） *)

Section Quotient.

Universe o.

Context (X : PTop@{o}) (T : SetoidObject@{o o})
        (q : SetoidMorphism@{o o o} X T).

(* 相关说明。 （已译） *)
Definition pquot_open (V : T → Prop) : Prop :=
  (∀ t t' : T, t ≈ t' → V t → V t') /\ POpen X (fun x => V (q x)).

Lemma pquot_open_respects (U V : T → Prop) :
  (∀ t, U t <-> V t) → pquot_open U → pquot_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros t t' e v. apply (proj1 (H t')), (Hp t t' e), (proj2 (H t)), v.
  - exact (popen_respects X _ _ (fun x => H (q x)) Ho).
Qed.

Lemma pquot_open_proper (U : T → Prop) :
  pquot_open U → ∀ t t' : T, t ≈ t' → U t → U t'.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma pquot_open_union (F : (T → Prop) → Prop) :
  (∀ V, F V → pquot_open V) →
  pquot_open (fun t => ex (fun V => F V /\ V t)).
Proof.
  intro HF; split.
  - intros t t' e [V [FV v]]. exists V; split; [exact FV|].
    exact (proj1 (HF V FV) t t' e v).
  - apply (popen_respects X
             (fun x => ex (fun U => ex (fun V => F V /\
                                          ∀ y, U y <-> V (q y)) /\ U x))).
    + intro x; split.
      * intros [U [[V [FV HUV]] u]]. exists V.
        split; [exact FV|exact (proj1 (HUV x) u)].
      * intros [V [FV v]]. exists (fun y => V (q y)).
        split; [|exact v]. exists V; split; [exact FV|].
        intro y; exact (iff_refl _).
    + apply popen_union. intros U [V [FV HUV]].
      apply (popen_respects X (fun y => V (q y))).
      * intro y; exact (iff_sym (HUV y)).
      * exact (proj2 (HF V FV)).
Qed.

Lemma pquot_open_whole : pquot_open (fun _ => True).
Proof. split; [intros; exact I|exact (popen_whole X)]. Qed.

Lemma pquot_open_inter (U V : T → Prop) :
  pquot_open U → pquot_open V → pquot_open (fun t => U t /\ V t).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros t t' e [u v]; exact (conj (HpU t t' e u) (HpV t t' e v)).
  - exact (popen_inter X _ _ HoU HoV).
Qed.

Definition PQuot : PTop@{o} := {|
  pt_carrier     := T;
  POpen          := pquot_open;
  popen_respects := pquot_open_respects;
  popen_proper   := pquot_open_proper;
  popen_union    := pquot_open_union;
  popen_whole    := pquot_open_whole;
  popen_inter    := pquot_open_inter
|}.

Example PQuot_carrier : pt_carrier PQuot = T := eq_refl.

Example PQuot_open (V : T → Prop) :
  POpen PQuot V
  = ((∀ t t' : T, t ≈ t' → V t → V t') /\ POpen X (fun x => V (q x)))
  := eq_refl.

Lemma pquot_proj_cont : @PCont X PQuot q.
Proof. intros V HV; exact (proj2 HV). Qed.

Definition pquot_proj : PMor@{o} X PQuot :=
  @Build_PMor X PQuot q pquot_proj_cont.

(* The 普遍性质, over ARBITRARY spaces [Z] 映射 out: setoid
 map out quotient continuous exactly 复合 with
 [q] is. （已译） *)
Lemma pquot_universal (Z : PTop@{o}) (k : SetoidMorphism@{o o o} T Z) :
  @PCont PQuot Z k <-> @PCont X Z (setoid_morphism_compose k q).
Proof.
  split.
  - intros Hk W HW. exact (proj2 (Hk W HW)).
  - intros Hc W HW; split.
    + intros t t' e w.
      exact (popen_proper Z W HW (k t) (k t') (proper_morphism k t t' e) w).
    + exact (Hc W HW).
Qed.

(* 相关说明。 （已译） *)
Definition pquot_desc (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  PMor@{o} PQuot Z :=
  @Build_PMor PQuot Z k
    (proj2 (pquot_universal Z k)
       (pcont_respects (pmap f) (setoid_morphism_compose k q) Hfk (pcont f))).

Example pquot_desc_map (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  pmap (pquot_desc Z f k Hfk) = k := eq_refl.

Lemma pquot_desc_comm (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  ∀ x, pmap (pcompose (pquot_desc Z f k Hfk) pquot_proj) x ≈ pmap f x.
Proof. intro x; symmetry; exact (Hfk x). Qed.

End Quotient.

(* * ** The sliced forgetful 函子 sliced 伴随 （已译） *)

Section SliceAdjunctions.

Universes o so.
Constraint o < so.

Context (X : PTop@{o}).

Local Notation PT := PTopCat@{o so}.
Local Notation G := PForget@{o so}.

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PForget_over : @Slice PT X ⟶ @Slice Sets@{o so} (G X) :=
  Sliced G X.

(* The forgetful 函子 sliced under [X], Mac Lane's [X ↓ G]: generic
 [Cosliced] at [PForget]. （已译） *)
Definition PForget_under : @Coslice PT X ⟶ @Coslice Sets@{o so} (G X) :=
  Cosliced G X.

Example PForget_over_Sliced : PForget_over = Sliced G X := eq_refl.

Example PForget_under_Cosliced : PForget_under = Cosliced G X := eq_refl.

(* Mac Lane's [L]: subspace along each function 进入 points of
 [X]. （已译） *)
Program Definition PSub_Functor :
  @Slice Sets@{o so} (G X) ⟶ @Slice PT X := {|
  fobj := fun c => (PSub X (`1 c) (`2 c); psub_incl X (`1 c) (`2 c));
  fmap := fun c d m => ({| pmap := `1 m; pcont := _ |}; _)
|}.
Next Obligation.
  intros [S h] [S' h'] [m Hm]; simpl in *.
  apply (proj2 (psub_universal X S' h' (PSub X S h) m)).
  apply (@pcont_respects (PSub X S h) X h);
    [intro s; symmetry; exact (Hm s)|].
  exact (psub_incl_cont X S h).
Qed.
Next Obligation. intros [S h] [S' h'] [m Hm] s; simpl in *. exact (Hm s). Qed.
Next Obligation. intros c d m n H s; simpl in *. exact (H s). Qed.
Next Obligation. intros c s; simpl. reflexivity. Qed.
Next Obligation. intros c d e m n s; simpl. reflexivity. Qed.

Example PSub_Functor_obj (c : @Slice Sets@{o so} (G X)) :
  `1 (PSub_Functor c) = PSub X (`1 c) (`2 c) := eq_refl.

(* The hom-set bijection [G ↓ X ⊣ L]: map over [X] 进入 subspace
 IS underlying map, continuity coming [psub_universal]. （已译） *)
Program Definition psub_adj_iso (x : @Slice PT X)
  (y : @Slice Sets@{o so} (G X)) :
  @Isomorphism Sets
    {| carrier := @hom (@Slice Sets@{o so} (G X)) (PForget_over x) y
     ; is_setoid := @homset (@Slice Sets@{o so} (G X)) (PForget_over x) y |}
    {| carrier := @hom (@Slice PT X) x (PSub_Functor y)
     ; is_setoid := @homset (@Slice PT X) x (PSub_Functor y) |} := {|
  to   := {| morphism := fun k => ({| pmap := `1 k; pcont := _ |}; _) |};
  from := {| morphism := fun k => (pmap (`1 k); _) |}
|}.
Next Obligation.
  intros [Y g] [S h] [k Hk]; simpl in *.
  apply (proj2 (psub_universal X S h Y k)).
  apply (pcont_respects (pmap g)); [intro z; symmetry; exact (Hk z)|].
  exact (pcont g).
Qed.
Next Obligation. intros [Y g] [S h] [k Hk] z; simpl in *. exact (Hk z). Qed.
Next Obligation. intros x y k k' H z; simpl in *. exact (H z). Qed.
Next Obligation. intros [Y g] [S h] [k Hk] z; simpl in *. exact (Hk z). Qed.
Next Obligation. intros x y k k' H z; simpl in *. exact (H z). Qed.
Next Obligation. intros x y k z; simpl. reflexivity. Qed.
Next Obligation. intros x y k z; simpl. reflexivity. Qed.

(* Both transposes 恒等 underlying maps. （已译） *)
Example psub_adj_to_map (x : @Slice PT X) (y : @Slice Sets@{o so} (G X))
  (k : PForget_over x ~{@Slice Sets@{o so} (G X)}~> y) :
  pmap (`1 (to (psub_adj_iso x y) k)) = `1 k := eq_refl.

Example psub_adj_from_map (x : @Slice PT X) (y : @Slice Sets@{o so} (G X))
  (k : x ~{@Slice PT X}~> PSub_Functor y) :
  `1 (from (psub_adj_iso x y) k) = pmap (`1 k) := eq_refl.

Definition psub_adjunction : PForget_over ⊣ PSub_Functor.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PForget_over PSub_Functor
                     psub_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* [(G ↓ X) ∘ L = Id] 对象: Leibniz, after destructing pair;
 [Defined], so [id_cast] below reduces. （已译） *)
Lemma psub_obj (c : @Slice Sets@{o so} (G X)) :
  PForget_over (PSub_Functor c) = c.
Proof. destruct c; reflexivity. Defined.

Example psub_obj_pair (S : SetoidObject@{o o})
  (h : S ~{Sets@{o so}}~> G X) :
  PForget_over (PSub_Functor (S; h)) = (S; h) := eq_refl.

(* The counit 恒等, transported along [psub_obj]. （已译） *)
Lemma psub_counit (c : @Slice Sets@{o so} (G X)) :
  @counit _ _ _ _ psub_adjunction c ≈ id_cast (psub_obj c).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

(* 相关说明。 （已译） *)
Program Definition PQuot_Functor :
  @Coslice Sets@{o so} (G X) ⟶ @Coslice PT X := {|
  fobj := fun c => (PQuot X (`1 c) (`2 c); pquot_proj X (`1 c) (`2 c));
  fmap := fun c d m => ({| pmap := `1 m; pcont := _ |}; _)
|}.
Next Obligation.
  intros [T q] [T' q'] [m Hm]; simpl in *.
  apply (proj2 (pquot_universal X T q (PQuot X T' q') m)).
  apply (@pcont_respects X (PQuot X T' q') q'); [exact Hm|].
  exact (pquot_proj_cont X T' q').
Qed.
Next Obligation. intros [T q] [T' q'] [m Hm] x; simpl in *. exact (Hm x). Qed.
Next Obligation. intros c d m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros c t; simpl. reflexivity. Qed.
Next Obligation. intros c d e m n t; simpl. reflexivity. Qed.

Example PQuot_Functor_obj (c : @Coslice Sets@{o so} (G X)) :
  `1 (PQuot_Functor c) = PQuot X (`1 c) (`2 c) := eq_refl.

(* 相关说明。 （已译） *)
Program Definition pquot_adj_iso (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice PT X) (PQuot_Functor x) y
     ; is_setoid := @homset (@Coslice PT X) (PQuot_Functor x) y |}
    {| carrier := @hom (@Coslice Sets@{o so} (G X)) x (PForget_under y)
     ; is_setoid := @homset (@Coslice Sets@{o so} (G X)) x
                      (PForget_under y) |} := {|
  to   := {| morphism := fun k => (pmap (`1 k); _) |};
  from := {| morphism := fun k => ({| pmap := `1 k; pcont := _ |}; _) |}
|}.
Next Obligation. intros [T q] [Y f] [k Hk] x; simpl in *. exact (Hk x). Qed.
Next Obligation. intros x y k k' H t; simpl in *. exact (H t). Qed.
Next Obligation.
  intros [T q] [Y f] [k Hk]; simpl in *.
  apply (proj2 (pquot_universal X T q Y k)).
  apply (pcont_respects (pmap f)); [exact Hk|].
  exact (pcont f).
Qed.
Next Obligation. intros [T q] [Y f] [k Hk] x; simpl in *. exact (Hk x). Qed.
Next Obligation. intros x y k k' H t; simpl in *. exact (H t). Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.

Example pquot_adj_to_map (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X) (k : PQuot_Functor x ~{@Coslice PT X}~> y) :
  `1 (to (pquot_adj_iso x y) k) = pmap (`1 k) := eq_refl.

Example pquot_adj_from_map (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X)
  (k : x ~{@Coslice Sets@{o so} (G X)}~> PForget_under y) :
  pmap (`1 (from (pquot_adj_iso x y) k)) = `1 k := eq_refl.

Definition pquot_adjunction : PQuot_Functor ⊣ PForget_under.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PQuot_Functor PForget_under
                     pquot_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* [(X ↓ G) ∘ M = Id] on objects. *)
Lemma pquot_obj (c : @Coslice Sets@{o so} (G X)) :
  PForget_under (PQuot_Functor c) = c.
Proof. destruct c; reflexivity. Defined.

Example pquot_obj_pair (T : SetoidObject@{o o})
  (q : G X ~{Sets@{o so}}~> T) :
  PForget_under (PQuot_Functor (T; q)) = (T; q) := eq_refl.

(* The unit 恒等, transported along [pquot_obj]. （已译） *)
Lemma pquot_unit (c : @Coslice Sets@{o so} (G X)) :
  @unit _ _ _ _ pquot_adjunction c ≈ id_cast (eq_sym (pquot_obj c)).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

(* The subspace construction packaged: [L] is a right-adjoint-right-inverse
   of [G ↓ X], in Structure/SlicedInverse.v's record, which is what
   Proposition 1 consumes. *)
Definition subspace_RARI : RightAdjointRightInverse (Sliced G X) := {|
  rari_right  := PSub_Functor;
  rari_adj    := psub_adjunction;
  rari_obj    := psub_obj;
  rari_counit := psub_counit
|}.

Example subspace_RARI_right : rari_right subspace_RARI = PSub_Functor :=
  eq_refl.

(* The quotient construction packaged: [M] left-adjoint-right-inverse
 [X ↓ G], Theory/Equivalence/Strict.v's record, what the
 dual Proposition 1 所消耗. （已译） *)
Definition quotient_LARI : LeftAdjointRightInverse (Cosliced G X) := {|
  lari_left := PQuot_Functor;
  lari_adj  := pquot_adjunction;
  lari_obj  := pquot_obj;
  lari_unit := pquot_unit
|}.

Example quotient_LARI_left : lari_left quotient_LARI = PQuot_Functor :=
  eq_refl.

End SliceAdjunctions.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Notation SetsEq :=
  (@HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
     Sets_HasPullbacks).

(* 相关说明。 （已译） *)
Definition PTop_HasEqualizers@{o so + | o < so +} :
  @HasEqualizers PTopCat@{o so} :=
  @equalizers_from_sliced_RARI _ _ PForget@{o so} PForget_Faithful SetsEq
    subspace_RARI.

Example PTop_equalizer_obj@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = PSub x (`1 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g))))
  := eq_refl.

Example PTop_equalizer_arrow@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@equalizer _ PTop_HasEqualizers x y f g))
    = psub_incl x
        (`1 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g))))
  := eq_refl.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PTop_HasCoequalizers@{o so + | o < so +} :
  @HasCoequalizers PTopCat@{o so} :=
  @coequalizers_from_sliced_LARI _ _ PForget@{o so} PForget_Faithful
    Sets_HasCoequalizers quotient_LARI.

Example PTop_coequalizer_obj@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@coeq _ PTop_HasCoequalizers x y f g)
    = PQuot y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

Example PTop_coequalizer_arrow@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@coeq _ PTop_HasCoequalizers x y f g))
    = pquot_proj y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition PBool_subspace_RARI@{o so +| o < so +} :
  RightAdjointRightInverse (Sliced PForget@{o so} PBool@{o}) :=
  subspace_RARI PBool.

Definition PBool_quotient_LARI@{o so +| o < so +} :
  LeftAdjointRightInverse (Cosliced PForget@{o so} PBool@{o}) :=
  quotient_LARI PBool.

(* The 常值 map at [true] [PBool]; it differs 恒等, at
 [false]. （已译） *)
Definition pbool_true@{o} : PMor@{o} PBool PBool :=
  pdisc_mor bool_setoid_object PBool (pconst bool_setoid_object PBool true).

Lemma pbool_maps_differ@{o so | o < so +} :
  pid PBool ≈[PTopCat@{o so}] pbool_true → False.
Proof. intro H; specialize (H false); simpl in H; discriminate H. Qed.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PBool_equalizer@{o so +| o < so +} :=
  @equalizer PTopCat@{o so} PTop_HasEqualizers PBool PBool (pid PBool)
    pbool_true.

Example PBool_equalizer_obj@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = PSub PBool
        (`1 (@equalizer _ SetsEq _ _ setoid_morphism_id
               (pconst bool_setoid_object PBool true)))
        (`1 (`2 (@equalizer _ SetsEq _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true)))) := eq_refl.

Example PBool_equalizer_rari@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = `1 (rari_right PBool_subspace_RARI@{o so _ _}
            (`1 (@equalizer _ SetsEq _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true));
             `1 (`2 (@equalizer _ SetsEq _ _ setoid_morphism_id
                       (pconst bool_setoid_object PBool true))))) := eq_refl.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PBool_equalizer_points@{o so +| o < so +} (b : bool) :
  ex (fun e : pt_carrier (`1 PBool_equalizer@{o so _ _ _ _ _}) =>
        pmap (`1 (`2 PBool_equalizer@{o so _ _ _ _ _})) e = b)
  <-> b = true.
Proof.
  split.
  - intros [e He]. pose proof (fork_eq (`2 (`2 PBool_equalizer)) e) as F.
    simpl in F. rewrite <- He. exact F.
  - intros ->.
    pose (t := pdisc_mor unit_setoid_object PBool (pconst _ PBool true)
               : PPoint ~{PTopCat@{o so}}~> PBool).
    destruct (eq_desc (`2 (`2 PBool_equalizer@{o so _ _ _ _ _})) t
                (fun _ => eq_refl)) as [u Hu _].
    exists (pmap u ttt). exact (Hu ttt).
Qed.

(* 相关说明。 （已译） *)
Definition ppoint_false@{o} : PMor@{o} PPoint PBool :=
  pdisc_mor unit_setoid_object PBool (pconst unit_setoid_object PBool false).

Definition ppoint_true@{o} : PMor@{o} PPoint PBool :=
  pdisc_mor unit_setoid_object PBool (pconst unit_setoid_object PBool true).

Lemma ppoint_maps_differ@{o so | o < so +} :
  ppoint_false ≈[PTopCat@{o so}] ppoint_true → False.
Proof. intro H; specialize (H ttt); simpl in H; discriminate H. Qed.

(*
   本节说明 Subspace 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PBool_coequalizer@{o so +| o < so +} :=
  @coeq PTopCat@{o so} PTop_HasCoequalizers PPoint PBool ppoint_false
    ppoint_true.

Example PBool_coequalizer_obj@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = PQuot PBool
        (SetsCoeq (pconst unit_setoid_object PBool false)
                  (pconst unit_setoid_object PBool true))
        (sets_coeq_proj (pconst unit_setoid_object PBool false)
                        (pconst unit_setoid_object PBool true)) := eq_refl.

Example PBool_coequalizer_lari@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = `1 (lari_left PBool_quotient_LARI@{o so _ _}
            (SetsCoeq (pconst unit_setoid_object PBool false)
                      (pconst unit_setoid_object PBool true);
             sets_coeq_proj (pconst unit_setoid_object PBool false)
                            (pconst unit_setoid_object PBool true)))
  := eq_refl.

(* 相关说明。 （已译） *)
Lemma PBool_coequalizer_points@{o so +| o < so +} (b : bool) :
  @equiv _ (`1 PBool_coequalizer@{o so _ _ _ _ _ _}) b true.
Proof.
  destruct b.
  - apply cq_base. reflexivity.
  - exact (cq_glue (pconst unit_setoid_object PBool false)
                   (pconst unit_setoid_object PBool true) ttt).
Qed.
