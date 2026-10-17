Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Cocomplete.

Generalizable All Variables.

(** * The separation axioms T0, T1, T2 over [PTopCat], and their reflections *)

(*
 nLab:      https://ncatlab.org/nlab/show/separation+axioms
 nLab:      https://ncatlab.org/nlab/show/Hausdorff+space
 Wikipedia: https://en.wikipedia.org/wiki/Separation_axiom

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Separation premises and the positive separation axioms *)

(*
   本节说明 Separation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SepPremise@{o} :=
  ∀ S : Type@{o}, ((S → Prop) → Prop) → S → S → Prop.

(* T0: the two points lie in the same opens. *)
Definition prem_T0@{o} : SepPremise@{o} :=
  fun S O x y => ∀ U, O U → (U x <-> U y).

(* T1: every open containing the first point contains the second. *)
Definition prem_T1@{o} : SepPremise@{o} :=
  fun S O x y => ∀ U, O U → U x → U y.

(* T2: no two opens separate the points: every open about the first meets
   every open about the second. *)
Definition prem_T2@{o} : SepPremise@{o} :=
  fun S O x y => ∀ U V, O U → O V → U x → V y → ex (fun z => U z /\ V z).

Definition PSep@{o} (prem : SepPremise@{o}) (X : PTop@{o}) : Type@{o} :=
  ∀ x y : X, prem _ (POpen X) x y → x ≈ y.

Definition PT0@{o} (X : PTop@{o}) : Type@{o} := PSep@{o} prem_T0@{o} X.
Definition PT1@{o} (X : PTop@{o}) : Type@{o} := PSep@{o} prem_T1@{o} X.

(* The two points of a space cannot be separated by disjoint opens. *)
Definition PNotSep@{o} (X : PTop@{o}) (x y : X) : Prop :=
  prem_T2@{o} _ (POpen X) x y.

(* Hausdorff, in the positive form: points that no two opens separate are
   equal. *)
Definition PHaus@{o} (X : PTop@{o}) : Type@{o} := PSep@{o} prem_T2@{o} X.

Example PHaus_unfold@{o} (X : PTop@{o}) :
  PHaus X = (∀ x y : X, PNotSep X x y → x ≈ y) := eq_refl.

(* The classical Hausdorff axiom, the negative form, which Mac Lane uses
   without defining it (book p. 158, §VI.9): distinct points have
   disjoint neighbourhoods. *)
Definition PIsHausdorff@{o} (X : PTop@{o}) : Prop :=
  ∀ x y : X, (x ≈ y → False) →
    ex (fun U => ex (fun V => POpen X U /\ POpen X V /\ U x /\ V y /\
                              ∀ z, U z → V z → False)).

(** ** The chain T2 ⇒ T1 ⇒ T0 *)

Lemma PSep_mono@{o} (pa pb : SepPremise@{o})
  (h : ∀ S O x y, pa S O x y → pb S O x y) (X : PTop@{o}) :
  PSep pb X → PSep pa X.
Proof. intros Hb x y p. exact (Hb x y (h _ _ x y p)). Qed.

Lemma prem_T0_T1@{o} S O x y : prem_T0@{o} S O x y → prem_T1@{o} S O x y.
Proof. intros H U HU. exact (proj1 (H U HU)). Qed.

Lemma prem_T1_T2@{o} S O x y : prem_T1@{o} S O x y → prem_T2@{o} S O x y.
Proof. intros H U V HU HV u v. exists y. exact (conj (H U HU u) v). Qed.

Corollary PHaus_PT1@{o} (X : PTop@{o}) : PHaus X → PT1 X.
Proof. exact (PSep_mono prem_T1 prem_T2 prem_T1_T2 X). Qed.

Corollary PT1_PT0@{o} (X : PTop@{o}) : PT1 X → PT0 X.
Proof. exact (PSep_mono prem_T0 prem_T1 prem_T0_T1 X). Qed.

(** ** The laws a premise needs *)

(* [sl_anti]: fewer opens relate more pairs.  [sl_pull]: the premise read
   through the opens pulled back along a function is carried forward by
   it.  [sl_equiv]: equal points satisfy the premise. *)
Record SepLaws@{o} (prem : SepPremise@{o}) : Prop := {
  sl_anti : ∀ (S : Type@{o}) (O O' : (S → Prop) → Prop),
      (∀ U, O U → O' U) → ∀ x y, prem S O' x y → prem S O x y;
  sl_pull : ∀ (S S' : Type@{o}) (f : S → S') (O' : (S' → Prop) → Prop)
      (x y : S),
      prem S (fun U => ex (fun W => O' W /\ ∀ s, U s <-> W (f s))) x y →
      prem S' O' (f x) (f y);
  sl_equiv : ∀ (X : PTop@{o}) (x y : X), x ≈ y → prem _ (POpen X) x y
}.

Lemma prem_T0_laws@{o} : SepLaws@{o} prem_T0@{o}.
Proof.
  constructor.
  - intros S O O' sub x y H U HU. exact (H U (sub U HU)).
  - intros S S' f O' x y H W HW.
    exact (H (fun s => W (f s)) (ex_intro _ W (conj HW (fun s => iff_refl _)))).
  - intros X x y e U HU; split; intro u.
    + exact (popen_proper X U HU x y e u).
    + exact (popen_proper X U HU y x (symmetry e) u).
Qed.

Lemma prem_T1_laws@{o} : SepLaws@{o} prem_T1@{o}.
Proof.
  constructor.
  - intros S O O' sub x y H U HU. exact (H U (sub U HU)).
  - intros S S' f O' x y H W HW.
    exact (H (fun s => W (f s)) (ex_intro _ W (conj HW (fun s => iff_refl _)))).
  - intros X x y e U HU u. exact (popen_proper X U HU x y e u).
Qed.

Lemma prem_T2_laws@{o} : SepLaws@{o} prem_T2@{o}.
Proof.
  constructor.
  - intros S O O' sub x y H U V HU HV. exact (H U V (sub U HU) (sub V HV)).
  - intros S S' f O' x y H W1 W2 H1 H2 w1 w2.
    destruct (H (fun s => W1 (f s)) (fun s => W2 (f s))
                (ex_intro _ W1 (conj H1 (fun s => iff_refl _)))
                (ex_intro _ W2 (conj H2 (fun s => iff_refl _))) w1 w2)
      as [z [a b]].
    exists (f z). exact (conj a b).
  - intros X x y e U V HU HV u v. exists y.
    exact (conj (popen_proper X U HU x y e u) v).
Qed.

(* The premise pulled back along a continuous map: what [sl_pull] and
   [sl_anti] give together, for the opens of two spaces. *)
Lemma sep_pull_cont@{o} (prem : SepPremise@{o}) (L : SepLaws@{o} prem)
  (X Y : PTop@{o}) (f : PMor@{o} X Y) (x y : X) :
  prem _ (POpen X) x y → prem _ (POpen Y) (pmap f x) (pmap f y).
Proof.
  intro Hp.
  apply (sl_pull _ L _ _ (fun s => pmap f s) (POpen Y) x y).
  apply (sl_anti _ L _ _ (POpen X)); [|exact Hp].
  intros U [W [HW HUW]].
  apply (popen_respects X (fun s => W (pmap f s))).
  - intro s; exact (iff_sym (HUW s)).
  - exact (pcont f W HW).
Qed.

(** ** Full subcategories of spaces *)

(* The full subcategory of [PTopCat] on the spaces with a property. *)
Definition PFullSub@{o so | o < so +} (Pr : PTop@{o} → Type@{o}) :
  Subcategory@{so o o o} PTopCat@{o so} :=
  @Build_Subcategory@{so o o o} PTopCat@{o so} Pr
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Lemma PFullSub_Full@{o so | o < so +} (Pr : PTop@{o} → Type@{o}) :
  Construction.Subcategory.Full@{so o o o so} PTopCat@{o so} (PFullSub Pr).
Proof. intros x y ox oy g; exact I. Qed.

(** ** The largest separated quotient, directly *)

Section Quot.

Universe o.

Variable prem : SepPremise@{o}.
Variable L : SepLaws@{o} prem.

Context (X : PTop@{o}).

Local Notation P := (carrier (pt_carrier X)).

(* The opens of X saturated for a relation. *)
Definition sep_qopen (R : P → P → Prop) (U : P → Prop) : Prop :=
  POpen X U /\ ∀ a b, R a b → U a → U b.

(* A separating relation: an equivalence coarser than the points' own,
   which the premise read in the saturated opens forces. *)
Definition SepRel (R : P → P → Prop) : Prop :=
  (∀ a, R a a) /\ (∀ a b, R a b → R b a) /\
  (∀ a b c, R a b → R b c → R a c) /\
  (∀ a b : P, a ≈ b → R a b) /\
  (∀ a b, prem P (sep_qopen R) a b → R a b).

(* Their intersection, a proposition by impredicativity. *)
Definition sepeq (a b : P) : Prop := ∀ R, SepRel R → R a b.

Lemma sepeq_refl (a : P) : sepeq a a.
Proof. intros R HR. exact (proj1 HR a). Qed.

Lemma sepeq_sym (a b : P) : sepeq a b → sepeq b a.
Proof. intros e R HR. exact (proj1 (proj2 HR) a b (e R HR)). Qed.

Lemma sepeq_trans (a b c : P) : sepeq a b → sepeq b c → sepeq a c.
Proof.
  intros e1 e2 R HR.
  exact (proj1 (proj2 (proj2 HR)) a b c (e1 R HR) (e2 R HR)).
Qed.

Lemma sepeq_of_equiv (a b : P) : a ≈ b → sepeq a b.
Proof. intros e R HR. exact (proj1 (proj2 (proj2 (proj2 HR))) a b e). Qed.

Definition sep_setoid : SetoidObject@{o o} :=
  {| carrier := P;
     is_setoid := {| equiv := sepeq;
                     setoid_equiv := Build_Equivalence sepeq sepeq_refl
                                       sepeq_sym sepeq_trans |} |}.

Definition sep_q :
  @SetoidMorphism@{o o o} _ (is_setoid (pt_carrier X)) _
    (is_setoid sep_setoid) :=
  @Build_SetoidMorphism _ (is_setoid (pt_carrier X)) _ (is_setoid sep_setoid)
    (fun x => x) sepeq_of_equiv.

(* The quotient: X's points under [sepeq], with the quotient topology. *)
Definition SepQuot : PTop@{o} := PQuot X sep_setoid sep_q.

Lemma SepQuot_sep : PSep prem SepQuot.
Proof using L.
  intros x y H R HR.
  apply (proj2 (proj2 (proj2 (proj2 HR)))).
  apply (sl_anti _ L P (sep_qopen R) (POpen SepQuot)); [|exact H].
  intros U [HU HsU]. split.
  - intros t t' e u. exact (HsU t t' (e R HR) u).
  - exact HU.
Qed.

Section Med.

Context (H : PTop@{o}) (HH : PSep prem H) (f : PMor@{o} X H).

(* The kernel of [f], read through the premise: a proposition, and
   equivalent to [pmap f a ≈ pmap f b] since [H] is separated. *)
Definition sep_ker (a b : P) : Prop :=
  prem _ (POpen H) (pmap f a) (pmap f b).

Lemma sep_ker_to (a b : P) : sep_ker a b → pmap f a ≈ pmap f b.
Proof using HH. exact (HH _ _). Qed.

Lemma sep_ker_of (a b : P) : pmap f a ≈ pmap f b → sep_ker a b.
Proof using L. exact (sl_equiv _ L H _ _). Qed.

Lemma sep_ker_SepRel : SepRel sep_ker.
Proof using L HH.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intro a. apply sep_ker_of. reflexivity.
  - intros a b e. apply sep_ker_of. symmetry. exact (sep_ker_to a b e).
  - intros a b c e1 e2. apply sep_ker_of.
    transitivity (pmap f b);
      [exact (sep_ker_to _ _ e1)|exact (sep_ker_to _ _ e2)].
  - intros a b e. apply sep_ker_of. exact (proper_morphism (pmap f) a b e).
  - intros a b Hp. unfold sep_ker.
    apply (sl_pull _ L P _ (fun s => pmap f s) (POpen H) a b).
    apply (sl_anti _ L P _ (sep_qopen sep_ker)); [|exact Hp].
    intros U [W [HW HUW]]. split.
    + apply (popen_respects X (fun s => W (pmap f s))).
      * intro s; exact (iff_sym (HUW s)).
      * exact (pcont f W HW).
    + intros a' b' e u. apply (proj2 (HUW b')). apply (proj1 (HUW a')) in u.
      exact (popen_proper H W HW _ _ (sep_ker_to a' b' e) u).
Qed.

Lemma sepquot_med_resp (a b : P) : sepeq a b → pmap f a ≈ pmap f b.
Proof using L HH.
  intro e. exact (sep_ker_to a b (e sep_ker sep_ker_SepRel)).
Qed.

Definition sepquot_med_setoid :
  @SetoidMorphism@{o o o} _ (is_setoid sep_setoid) _
    (is_setoid (pt_carrier H)) :=
  @Build_SetoidMorphism _ (is_setoid sep_setoid) _ (is_setoid (pt_carrier H))
    (fun a => pmap f a) sepquot_med_resp.

Definition sepquot_med : PMor@{o} SepQuot H :=
  pquot_desc X sep_setoid sep_q H f sepquot_med_setoid
    (fun x => reflexivity (pmap f x)).

End Med.

End Quot.

Section Reflection.

Universes o so.
Constraint o < so.

Variable prem : SepPremise@{o}.
Variable L : SepLaws@{o} prem.

(* The full subcategory of separated spaces, and the reflection into it. *)
Definition PSepSub : Subcategory PTopCat@{o so} := PFullSub (PSep prem).

Definition PSepSpaces : Category := Sub PTopCat@{o so} PSepSub.

Definition PSepObj (X : PTopCat@{o so}) : PSepSpaces :=
  (SepQuot prem X; SepQuot_sep prem L X).

Definition sep_proj (X : PTopCat@{o so}) :
  X ~{PTopCat@{o so}}~> Incl PTopCat@{o so} PSepSub (PSepObj X) :=
  pquot_proj X (sep_setoid prem X) (sep_q prem X).

Definition sep_universal (X : PTopCat@{o so}) :
  ∀ (d : PSepSpaces) (f : X ~{PTopCat@{o so}}~> Incl PTopCat@{o so} PSepSub d),
    ∃! g : PSepObj X ~{PSepSpaces}~> d,
      f ≈ fmap[Incl PTopCat@{o so} PSepSub] g ∘ sep_proj X.
Proof using L.
  intros d f.
  unshelve eexists.
  - exact (sepquot_med prem L X (`1 d) (`2 d) f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl. exact (Hg x).
Defined.

Definition sep_ua (X : PTopCat@{o so}) :
  @UniversalArrow PTopCat@{o so} PSepSpaces X (Incl PTopCat@{o so} PSepSub) :=
  @universal_arrow_from_UMP PTopCat@{o so} PSepSpaces X
    (Incl PTopCat@{o so} PSepSub) (PSepObj X) (sep_proj X) (sep_universal X).

Definition PSep_reflector : PTopCat@{o so} ⟶ PSepSpaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl PTopCat@{o so} PSepSub) sep_ua.

Definition PSep_adj : PSep_reflector ⊣ Incl PTopCat@{o so} PSepSub :=
  AdjunctionFromUniversalArrows (Incl PTopCat@{o so} PSepSub) sep_ua.

Definition PSep_Reflective : Reflective PSepSub :=
  @Build_Reflective PTopCat@{o so} PSepSub (PFullSub_Full _) PSep_reflector
    PSep_adj.

End Reflection.

(** ** Restricting a reflection to an intermediate full subcategory *)

(* If B ⊆ A are full subcategories of C and B is reflective in C, then B,
   read as a full subcategory of A, is reflective in A: reflect in C and
   read the result back in A. *)
Section Restrict.

(*
   本节说明 Separation 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes co ch sa sah sb fa ra rb rc rd.

Context {C : Category@{co ch ch}} (SA : Subcategory@{co ch sa sah} C)
  (SB : Subcategory@{co ch sb ch} C)
  (fullA : Construction.Subcategory.Full@{co ch sa sah fa} C SA)
  (sub : ∀ x : C, sobj C SB x → sobj C SA x)
  (RB : Reflective@{ra rb rc rd co sb ch} SB).

Definition restrict_sub : Subcategory (Sub C SA) :=
  @Build_Subcategory (Sub C SA) (fun X => sobj C SB (`1 X))
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Lemma restrict_full : Construction.Subcategory.Full (Sub C SA) restrict_sub.
Proof. intros x y ox oy g; exact I. Qed.

Definition restrict_obj (X : Sub C SA) : Sub (Sub C SA) restrict_sub :=
  ((`1 (reflector RB (`1 X)); sub _ (`2 (reflector RB (`1 X))));
   `2 (reflector RB (`1 X))).

Definition restrict_unit (X : Sub C SA) :
  X ~{Sub C SA}~> Incl (Sub C SA) restrict_sub (restrict_obj X) :=
  (@unit _ _ _ _ (reflective_adj RB) (`1 X); fullA _ _ _ _ _).

Definition restrict_universal (X : Sub C SA) :
  ∀ (d : Sub (Sub C SA) restrict_sub)
    (f : X ~{Sub C SA}~> Incl (Sub C SA) restrict_sub d),
    ∃! g : restrict_obj X ~{Sub (Sub C SA) restrict_sub}~> d,
      f ≈ fmap[Incl (Sub C SA) restrict_sub] g ∘ restrict_unit X.
Proof using fullA.
  intros d f.
  pose (dB := (`1 (`1 d); `2 d) : Sub C SB).
  pose (g0 := from (@adj _ _ _ _ (reflective_adj RB) (`1 X) dB) (`1 f)).
  unshelve eexists.
  - exact ((`1 g0; fullA _ _ _ _ _); I).
  - change (`1 f ≈ `1 g0 ∘ @unit _ _ _ _ (reflective_adj RB) (`1 X)).
    transitivity (to (@adj _ _ _ _ (reflective_adj RB) (`1 X) dB) g0).
    + symmetry.
      exact (@from_adj_comp_law _ _ _ _ (reflective_adj RB) _ dB (`1 f)).
    + exact (@to_adj_unit _ _ _ _ (reflective_adj RB) _ _ g0).
  - intros g' Hg'.
    pose (g'B := (`1 (`1 g'); reflective_full RB _ _ _ _ _)
                 : reflector RB (`1 X) ~{Sub C SB}~> dB).
    assert (E : g'B ≈ g0).
    { apply (snd (@adj_univ _ _ _ _ (reflective_adj RB) _ _ g'B (`1 f))).
      transitivity (`1 (`1 g') ∘ @unit _ _ _ _ (reflective_adj RB) (`1 X)).
      - exact (@to_adj_unit _ _ _ _ (reflective_adj RB) _ _ g'B).
      - symmetry. exact Hg'. }
    symmetry. exact E.
Defined.

Definition restrict_ua (X : Sub C SA) :
  @UniversalArrow (Sub C SA) (Sub (Sub C SA) restrict_sub) X
    (Incl (Sub C SA) restrict_sub) :=
  @universal_arrow_from_UMP (Sub C SA) (Sub (Sub C SA) restrict_sub) X
    (Incl (Sub C SA) restrict_sub) (restrict_obj X) (restrict_unit X)
    (restrict_universal X).

Definition restrict_reflector : Sub C SA ⟶ Sub (Sub C SA) restrict_sub :=
  LeftAdjointFunctorFromUniversalArrows (Incl (Sub C SA) restrict_sub)
    restrict_ua.

Definition restrict_adj :
  restrict_reflector ⊣ Incl (Sub C SA) restrict_sub :=
  AdjunctionFromUniversalArrows (Incl (Sub C SA) restrict_sub) restrict_ua.

Definition restrict_Reflective : Reflective restrict_sub :=
  @Build_Reflective (Sub C SA) restrict_sub restrict_full restrict_reflector
    restrict_adj.

End Restrict.

(** ** The reflections into T0, T1 and T2 spaces, and Exercise 4 at n = 0, 1 *)

Definition PT0_Reflective@{o so +} :
  Reflective (PSepSub@{o so} prem_T0@{o}) :=
  PSep_Reflective prem_T0 prem_T0_laws.

Definition PT1_Reflective@{o so +} :
  Reflective (PSepSub@{o so} prem_T1@{o}) :=
  PSep_Reflective prem_T1 prem_T1_laws.

Definition PT2_Reflective@{o so +} :
  Reflective (PSepSub@{o so} prem_T2@{o}) :=
  PSep_Reflective prem_T2 prem_T2_laws.

(* Mac Lane's Exercise 4 at n = 0: Top_1 → Top_0, T1 spaces in T0 spaces. *)
Definition PT1_in_PT0_Reflective@{o so +} :
  Reflective (restrict_sub (PSepSub@{o so} prem_T0@{o})
                           (PSepSub@{o so} prem_T1@{o})) :=
  restrict_Reflective (PSepSub prem_T0) (PSepSub prem_T1)
    (PFullSub_Full _) PT1_PT0 PT1_Reflective.

(* Mac Lane's Exercise 4 at n = 1: Top_2 → Top_1, Hausdorff spaces in T1
   spaces. *)
Definition PHaus_in_PT1_Reflective@{o so +} :
  Reflective (restrict_sub (PSepSub@{o so} prem_T1@{o})
                           (PSepSub@{o so} prem_T2@{o})) :=
  restrict_Reflective (PSepSub prem_T1) (PSepSub prem_T2)
    (PFullSub_Full _) PHaus_PT1 PT2_Reflective.

(** ** Readbacks of the direct reflection *)

(* The quotient keeps X's points, coarsens their equality to [sepeq], and
   the reflector and its unit compute to it on the nose. *)
Example SepQuot_carrier@{o} (prem : SepPremise@{o}) (X : PTop@{o}) :
  carrier (pt_carrier (SepQuot prem X)) = carrier (pt_carrier X) := eq_refl.

Example SepQuot_equiv@{o} (prem : SepPremise@{o}) (X : PTop@{o})
  (a b : carrier (pt_carrier X)) :
  @equiv _ (is_setoid (pt_carrier (SepQuot prem X))) a b = sepeq prem X a b
  := eq_refl.

Example PSep_reflector_obj@{o so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X : PTopCat@{o so}) :
  `1 (fobj[PSep_reflector prem L] X) = SepQuot prem X := eq_refl.

Example PSep_unit_point@{o so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) (X : PTopCat@{o so}) (x : carrier (pt_carrier X)) :
  pmap (@unit _ _ _ _ (PSep_adj prem L) X) x = x := eq_refl.

(* The restricted reflection computes the same way: Exercise 4's reflector
   at n = 0 sends a T0 space to its largest T1 quotient, and its unit is
   the identity on points. *)
Example PT1_in_PT0_obj@{o so +}
  (X : Sub PTopCat@{o so} (PSepSub@{o so} prem_T0@{o})) :
  `1 (`1 (fobj[reflector PT1_in_PT0_Reflective] X)) = SepQuot prem_T1 (`1 X)
  := eq_refl.

Example PT1_in_PT0_unit_point@{o so +}
  (X : Sub PTopCat@{o so} (PSepSub@{o so} prem_T0@{o}))
  (x : carrier (pt_carrier (`1 X))) :
  pmap (`1 (@unit _ _ _ _ (reflective_adj PT1_in_PT0_Reflective) X)) x = x
  := eq_refl.

(** ** A retract of a separated space is separated *)

Lemma PSep_retract@{o} (prem : SepPremise@{o}) (L : SepLaws@{o} prem)
  (X R : PTop@{o}) (u : PMor@{o} X R) (e : PMor@{o} R X)
  (Heu : ∀ x, pmap e (pmap u x) ≈ x) : PSep prem R → PSep prem X.
Proof.
  intros HR x y Hp.
  transitivity (pmap e (pmap u x)); [symmetry; exact (Heu x)|].
  transitivity (pmap e (pmap u y)); [|exact (Heu y)].
  refine (proper_morphism (pmap e) _ _ (HR _ _ _)).
  exact (sep_pull_cont prem L X R u x y Hp).
Qed.

(** ** Every inclusion is strict *)

(* Not T0: the indiscrete two-point space of Instance/Top/Cocomplete.v. *)
Lemma PTwoIndisc_not_PT0@{o} : PT0 PTwoIndisc@{o} → False.
Proof.
  intro H.
  assert (Hp : prem_T0 _ (POpen PTwoIndisc@{o}) true false).
  { intros U HU; split; intro u; exact (HU _ _ u). }
  pose proof (H _ _ Hp) as e. simpl in e. discriminate e.
Qed.

(* T0 but not T1: Sierpiński space, the two points with [true] open. *)
Section Sierpinski.

Universe o.

Definition sier_open (U : bool_setoid_object@{o o} → Prop) : Prop :=
  U false → U true.

Lemma sier_open_respects (U V : bool_setoid_object@{o o} → Prop) :
  (∀ x, U x <-> V x) → sier_open U → sier_open V.
Proof. intros H HU v. apply (proj1 (H true)), HU, (proj2 (H false)), v. Qed.

Lemma sier_open_proper (U : bool_setoid_object@{o o} → Prop) :
  sier_open U → ∀ x y : bool_setoid_object@{o o}, x ≈ y → U x → U y.
Proof. intros _ x y e u. simpl in e. subst y. exact u. Qed.

Lemma sier_open_union (F : (bool_setoid_object@{o o} → Prop) → Prop) :
  (∀ U, F U → sier_open U) → sier_open (fun x => ex (fun U => F U /\ U x)).
Proof. intros HF [U [FU u]]. exists U. exact (conj FU (HF U FU u)). Qed.

Lemma sier_open_whole : sier_open (fun _ => True).
Proof. intros _; exact I. Qed.

Lemma sier_open_inter (U V : bool_setoid_object@{o o} → Prop) :
  sier_open U → sier_open V → sier_open (fun x => U x /\ V x).
Proof. intros HU HV [u v]. exact (conj (HU u) (HV v)). Qed.

Definition PSierpinski : PTop@{o} := {|
  pt_carrier     := bool_setoid_object@{o o};
  POpen          := sier_open;
  popen_respects := sier_open_respects;
  popen_proper   := sier_open_proper;
  popen_union    := sier_open_union;
  popen_whole    := sier_open_whole;
  popen_inter    := sier_open_inter
|}.

Lemma PSierpinski_PT0 : PT0 PSierpinski.
Proof.
  intros x y H. change (x = y).
  assert (Ho : POpen PSierpinski (fun z => z = true))
    by (intros _; reflexivity).
  destruct (H _ Ho) as [a b].
  destruct x, y; try reflexivity.
  - symmetry. exact (a eq_refl).
  - exact (b eq_refl).
Qed.

Lemma PSierpinski_not_PT1 : PT1 PSierpinski → False.
Proof.
  intro H.
  assert (Hp : prem_T1 _ (POpen PSierpinski) false true).
  { intros U HU u. exact (HU u). }
  pose proof (H _ _ Hp) as e. simpl in e. discriminate e.
Qed.

End Sierpinski.

(* T1 but not T2: the cofinite topology on the naturals, whose nonempty
   opens are the sets containing a tail [N, ∞).  The arithmetic is proved
   from the prelude alone. *)
Section NatArith.

Local Open Scope nat_scope.

Lemma sep_le_trans@{} (a b c : nat) : a <= b → b <= c → a <= c.
Proof.
  intros H1 H2. induction H2 as [|c _ IH]; [exact H1|exact (le_S _ _ IH)].
Qed.

Lemma sep_le_add_r@{} (n m : nat) : n <= n + m.
Proof.
  induction n as [|n IH]; simpl; [exact (le_0_n m)|exact (le_n_S _ _ IH)].
Qed.

Lemma sep_le_add_l@{} (n m : nat) : m <= n + m.
Proof. induction n as [|n IH]; simpl; [exact (le_n m)|exact (le_S _ _ IH)]. Qed.

Lemma sep_not_succ_le@{} (n : nat) : S n <= n → False.
Proof.
  induction n as [|n IH]; intro H.
  - inversion H.
  - exact (IH (le_S_n _ _ H)).
Qed.

End NatArith.

Section Cofinite.

Universe o.

Local Open Scope nat_scope.

Definition pnat_setoid : SetoidObject@{o o} :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Definition cof_open (U : pnat_setoid → Prop) : Prop :=
  ∀ x, U x → ex (fun N => ∀ z, N <= z → U z).

Lemma cof_open_respects (U V : pnat_setoid → Prop) :
  (∀ x, U x <-> V x) → cof_open U → cof_open V.
Proof.
  intros H HU x v. destruct (HU x (proj2 (H x) v)) as [N HN].
  exists N. intros z Hz. exact (proj1 (H z) (HN z Hz)).
Qed.

Lemma cof_open_proper (U : pnat_setoid → Prop) :
  cof_open U → ∀ x y : pnat_setoid, x ≈ y → U x → U y.
Proof. intros _ x y e u. simpl in e. subst y. exact u. Qed.

Lemma cof_open_union (F : (pnat_setoid → Prop) → Prop) :
  (∀ U, F U → cof_open U) → cof_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x [U [FU u]]. destruct (HF U FU x u) as [N HN].
  exists N. intros z Hz. exists U. exact (conj FU (HN z Hz)).
Qed.

Lemma cof_open_whole : cof_open (fun _ => True).
Proof. intros x _. exists 0. intros; exact I. Qed.

Lemma cof_open_inter (U V : pnat_setoid → Prop) :
  cof_open U → cof_open V → cof_open (fun x => U x /\ V x).
Proof.
  intros HU HV x [u v].
  destruct (HU x u) as [N HN], (HV x v) as [M HM].
  exists (N + M). intros z Hz. split.
  - exact (HN z (sep_le_trans _ _ _ (sep_le_add_r N M) Hz)).
  - exact (HM z (sep_le_trans _ _ _ (sep_le_add_l N M) Hz)).
Qed.

Definition PCofinite : PTop@{o} := {|
  pt_carrier     := pnat_setoid;
  POpen          := cof_open;
  popen_respects := cof_open_respects;
  popen_proper   := cof_open_proper;
  popen_union    := cof_open_union;
  popen_whole    := cof_open_whole;
  popen_inter    := cof_open_inter
|}.

(* The open "x, or the tail above x + y": if it must contain y, then
   y = x, the tail lying strictly above y. *)
Lemma PCofinite_PT1 : PT1 PCofinite.
Proof.
  intros x y H. change (x = y).
  assert (Ho : POpen PCofinite (fun z => x = z \/ S (x + y) <= z)).
  { intros w _. exists (S (x + y)). intros z Hz. right. exact Hz. }
  destruct (H _ Ho (or_introl eq_refl)) as [e|l]; [exact e|].
  exfalso. apply (sep_not_succ_le y).
  exact (sep_le_trans _ _ _ (le_n_S _ _ (sep_le_add_l x y)) l).
Qed.

(* Any two nonempty opens meet, above both tails. *)
Lemma PCofinite_not_PHaus : PHaus PCofinite → False.
Proof.
  intro H.
  assert (Hp : PNotSep PCofinite 0 1).
  { intros U V HU HV u v.
    destruct (HU 0 u) as [N HN], (HV 1 v) as [M HM].
    exists (N + M). split.
    - exact (HN _ (sep_le_add_r N M)).
    - exact (HM _ (sep_le_add_l N M)). }
  pose proof (H _ _ Hp) as e. simpl in e. discriminate e.
Qed.

End Cofinite.

(* The discrete two-point space is Hausdorff: its equality is Leibniz, and
   the two singletons are open. *)
Lemma PBool_PHaus@{o} : PHaus PBool@{o}.
Proof.
  intros a b H. change (a = b).
  destruct (H (fun z => z = a) (fun z => z = b)) as [z [za zb]].
  - intros x y e hx. change (x = y) in e. congruence.
  - intros x y e hx. change (x = y) in e. congruence.
  - reflexivity.
  - reflexivity.
  - congruence.
Qed.

(** ** The classical negative Hausdorff axiom against the positive one *)

(* Negative to positive, given that the points' equality is stable under
   double negation. *)
Lemma PIsHausdorff_PHaus@{o} (X : PTop@{o})
  (stab : ∀ x y : X, ((x ≈ y → False) → False) → x ≈ y) :
  PIsHausdorff X → PHaus X.
Proof.
  intros H x y Hp. apply stab. intro ne.
  destruct (H x y ne) as [U [V [HU [HV [u [v d]]]]]].
  destruct (Hp U V HU HV u v) as [z [a b]].
  exact (d z a b).
Qed.

(* Positive to negative, given excluded middle for propositions, as a
   hypothesis. *)
Lemma PHaus_PIsHausdorff@{o} (lem : ∀ P : Prop, P \/ (P → False))
  (X : PTop@{o}) : PHaus X → PIsHausdorff X.
Proof.
  intros H x y ne.
  destruct (lem (ex (fun U => ex (fun V => POpen X U /\ POpen X V /\ U x /\
                                  V y /\ ∀ z, U z → V z → False))))
    as [e|n]; [exact e|].
  exfalso. apply ne. apply H. intros U V HU HV u v.
  destruct (lem (ex (fun z => U z /\ V z))) as [e|m]; [exact e|].
  exfalso. apply n. exists U, V. repeat split; auto.
  intros z a b. apply m. exists z. auto.
Qed.

(* Unconditionally, each form gives the other's conclusion only under a
   negation. *)
Lemma PIsHausdorff_PHaus_nn@{o} (X : PTop@{o}) (H : PIsHausdorff X)
  (x y : X) : PNotSep X x y → (x ≈ y → False) → False.
Proof.
  intros Hp ne.
  destruct (H x y ne) as [U [V [HU [HV [u [v d]]]]]].
  destruct (Hp U V HU HV u v) as [z [a b]].
  exact (d z a b).
Qed.

Lemma PHaus_distinct_not_notsep@{o} (X : PTop@{o}) (H : PHaus X) (x y : X) :
  (x ≈ y → False) → PNotSep X x y → False.
Proof. intros ne Hp. exact (ne (H x y Hp)). Qed.

(* A Hausdorff space's equality is propositional: [PNotSep] is a
   proposition equivalent to it. *)
Definition PHaus_PropEquiv@{o} (X : PTop@{o}) (hX : PHaus X) :
  PropEquiv (is_setoid (pt_carrier X)) :=
  {| pequiv := PNotSep X;
     pequiv_to := hX;
     pequiv_from := sl_equiv _ prem_T2_laws X |}.
