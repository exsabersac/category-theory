Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.GAFT.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Coequalizer.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Colimit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.

Generalizable All Variables.

(** * Hausdorff spaces: Mac Lane §V.9 Proposition 2, Exercises 4 and 5 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Hausdorff+space
 nLab:      https://ncatlab.org/nlab/show/separation+axioms
 nLab:      https://ncatlab.org/nlab/show/normal+space
 Wikipedia: https://en.wikipedia.org/wiki/Separation_axiom

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Closure under limits *)

(* The legs of a limiting cone carry the premise forward and are jointly
   injective on points, so a limit of separated spaces is separated. *)
Lemma plimit_PSep@{j o so +| o < so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone T) (HN : IsLimitCone N) (HT : ∀ k, PSep prem (T k)) :
  PSep prem (vertex_obj[N]).
Proof.
  intros x y Hp.
  apply (plimit_points_jointly_monic T N HN).
  intro k. apply HT.
  exact (sep_pull_cont prem L _ _ (cone_leg N k) x y Hp).
Qed.

Definition PSep_closed@{o so +| o < so +} (prem : SepPremise@{o})
  (L : SepLaws@{o} prem) : ClosedUnderLimits (PSepSub@{o so} prem) :=
  fun J K N HN =>
    plimit_PSep prem L (Incl PTopCat@{o so} (PSepSub prem) ◯ K) N HN
      (fun k => `2 (K k)).

(** ** Presentations of quotients of a space *)

(* A presentation of a quotient of X on X's own points: an equivalence
   [R] coarser than X's equality, and a topology [T] on (X, R) coarser
   than X's.  Mac Lane's "quotient set of X with some topology". *)
Section Presentation.

Universe o.

Context (X : PTop@{o}).

Local Notation P := (carrier (pt_carrier X)).

Record TopPresentation (R : P → P → Prop) (T : (P → Prop) → Prop) : Prop := {
  pres_refl : ∀ a, R a a;
  pres_sym : ∀ a b, R a b → R b a;
  pres_trans : ∀ a b c, R a b → R b c → R a c;
  pres_base : ∀ a b : P, a ≈ b → R a b;
  pres_respects : ∀ U V : P → Prop, (∀ x, U x <-> V x) → T U → T V;
  pres_proper : ∀ U, T U → ∀ a b, R a b → U a → U b;
  pres_union : ∀ F : (P → Prop) → Prop, (∀ U, F U → T U) →
               T (fun x => ex (fun U => F U /\ U x));
  pres_whole : T (fun _ => True);
  pres_inter : ∀ U V, T U → T V → T (fun x => U x /\ V x);
  pres_cont : ∀ U, T U → POpen X U
}.

Section AtPresentation.

Context (R : P → P → Prop) (T : (P → Prop) → Prop)
  (v : TopPresentation R T).

Definition pres_setoid : SetoidObject@{o o} :=
  {| carrier := P;
     is_setoid := {| equiv := R;
                     setoid_equiv :=
                       Build_Equivalence R (pres_refl _ _ v)
                         (pres_sym _ _ v) (pres_trans _ _ v) |} |}.

Definition pres_space : PTop@{o} := {|
  pt_carrier     := pres_setoid;
  POpen          := T;
  popen_respects := pres_respects _ _ v;
  popen_proper   := pres_proper _ _ v;
  popen_union    := pres_union _ _ v;
  popen_whole    := pres_whole _ _ v;
  popen_inter    := pres_inter _ _ v
|}.

Definition pres_proj : PMor@{o} X pres_space :=
  @Build_PMor X pres_space
    (@Build_SetoidMorphism _ (is_setoid (pt_carrier X)) _
       (is_setoid pres_setoid) (fun x => x) (pres_base _ _ v))
    (pres_cont _ _ v).

End AtPresentation.

(*
   本节说明始/终对象、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Image.

Context (Y : PTop@{o}) (k : Y → Y → Prop)
  (k_of : ∀ y y' : Y, y ≈ y' → k y y') (k_to : ∀ y y' : Y, k y y' → y ≈ y')
  (h : PMor@{o} X Y).

Definition img_rel (a b : P) : Prop := k (pmap h a) (pmap h b).

Definition img_top (U : P → Prop) : Prop :=
  ex (fun W => POpen Y W /\ ∀ x, U x <-> W (pmap h x)).

Lemma img_valid : TopPresentation img_rel img_top.
Proof using k_of k_to.
  constructor.
  - intro a. apply k_of. reflexivity.
  - intros a b e. apply k_of. symmetry. exact (k_to _ _ e).
  - intros a b c e1 e2. apply k_of.
    transitivity (pmap h b); [exact (k_to _ _ e1)|exact (k_to _ _ e2)].
  - intros a b e. apply k_of. exact (proper_morphism (pmap h) a b e).
  - intros U V HUV [W [HW HUW]]. exists W. split; [exact HW|].
    intro x. split; intro u.
    + exact (proj1 (HUW x) (proj2 (HUV x) u)).
    + exact (proj1 (HUV x) (proj2 (HUW x) u)).
  - intros U [W [HW HUW]] a b e u.
    apply (proj2 (HUW b)).
    exact (popen_proper Y W HW _ _ (k_to _ _ e) (proj1 (HUW a) u)).
  - intros F HF.
    exists (fun y => ex (fun U => ex (fun W => (F U /\ POpen Y W /\
                    (∀ x, U x <-> W (pmap h x))) /\ W y))).
    split.
    + apply (popen_respects Y
               (fun y => ex (fun W => ex (fun U => F U /\ POpen Y W /\
                    (∀ x, U x <-> W (pmap h x))) /\ W y))).
      * intro y. split.
        -- intros [W [[U HU] w]]. exists U, W. exact (conj HU w).
        -- intros [U [W [HU w]]]. exists W. split; [exists U; exact HU|exact w].
      * apply popen_union. intros W [U [_ [HW _]]]. exact HW.
    + intro x. split.
      * intros [U [FU u]]. destruct (HF U FU) as [W [HW HUW]].
        exists U, W. split; [exact (conj FU (conj HW HUW))|].
        exact (proj1 (HUW x) u).
      * intros [U [W [[FU [_ HUW]] w]]]. exists U. split; [exact FU|].
        exact (proj2 (HUW x) w).
  - exists (fun _ => True). split; [exact (popen_whole Y)|].
    intro x; split; intros; exact I.
  - intros U V [W1 [H1 E1]] [W2 [H2 E2]].
    exists (fun y => W1 y /\ W2 y). split; [exact (popen_inter Y _ _ H1 H2)|].
    intro x. split.
    + intros [u v]. exact (conj (proj1 (E1 x) u) (proj1 (E2 x) v)).
    + intros [u v]. exact (conj (proj2 (E1 x) u) (proj2 (E2 x) v)).
  - intros U [W [HW HUW]].
    apply (popen_respects X (fun x => W (pmap h x))).
    + intro x; exact (iff_sym (HUW x)).
    + exact (pcont h W HW).
Qed.

Definition img_space : PTop@{o} := pres_space img_rel img_top img_valid.

(* The image maps into Y by [h] itself. *)
Definition img_mor : PMor@{o} img_space Y :=
  @Build_PMor img_space Y
    (@Build_SetoidMorphism _ (is_setoid (pres_setoid img_rel img_top img_valid))
       _ (is_setoid (pt_carrier Y)) (fun x => pmap h x)
       (fun a b e => k_to _ _ e))
    (fun W HW => ex_intro _ W (conj HW (fun x => iff_refl _))).

End Image.

End Presentation.

(** ** Mac Lane's solution set: the Hausdorff quotients of X *)

(*
   本节说明 Hausdorff 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PSolIdx@{o | Set < o +} (Pr : PTop@{o} → Type@{o}) (X : PTop@{o}) :
  Type@{o} :=
  { R : X → X → Prop & { T : (X → Prop) → Prop &
    { v : TopPresentation X R T & Pr (pres_space X R T v) } } }.

Section Sols.

Universes o so.
Constraint Set < o.
Constraint o < so.

Variable Pr : PTop@{o} → Type@{o}.
Variable ker : ∀ Y : PTop@{o}, Y → Y → Prop.
Variable ker_of : ∀ (Y : PTop@{o}) (y y' : Y), y ≈ y' → ker Y y y'.
Variable ker_to : ∀ Y : PTop@{o}, Pr Y → ∀ y y' : Y, ker Y y y' → y ≈ y'.
Variable pr_img : ∀ (X Y : PTop@{o}) (hY : Pr Y) (h : PMor@{o} X Y),
    Pr (img_space X Y (ker Y) (ker_of Y) (ker_to Y hY) h).

Context (X : PTop@{o}).

Definition psol_obj (i : PSolIdx Pr X) : Sub PTopCat@{o so} (PFullSub Pr) :=
  (pres_space X (`1 i) (`1 (`2 i)) (`1 (`2 (`2 i))); `2 (`2 (`2 i))).

Definition psol_arr (i : PSolIdx Pr X) :
  X ~{PTopCat@{o so}}~> Incl PTopCat@{o so} (PFullSub Pr) (psol_obj i) :=
  pres_proj X (`1 i) (`1 (`2 i)) (`1 (`2 (`2 i))).

Definition PFull_sols : SolutionSet (Incl PTopCat@{o so} (PFullSub Pr)) X.
Proof using ker_of ker_to pr_img.
  refine {| sol_index := PSolIdx Pr X; sol_obj := psol_obj;
            sol_arr := psol_arr |}.
  intros c h.
  exists (img_rel X (`1 c) (ker (`1 c)) h;
          (img_top X (`1 c) h;
           (img_valid X (`1 c) (ker (`1 c)) (ker_of (`1 c))
              (ker_to (`1 c) (`2 c)) h;
            pr_img X (`1 c) (`2 c) h))).
  exists (img_mor X (`1 c) (ker (`1 c)) (ker_of (`1 c))
            (ker_to (`1 c) (`2 c)) h; I).
  intro x; simpl; reflexivity.
Defined.

End Sols.

(** ** The reflector by the general adjoint functor theorem *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PFull_left_adjoint_GAFT@{o so +| Set < o, o < so +}
  (Pr : PTop@{o} → Type@{o}) (ker : ∀ Y : PTop@{o}, Y → Y → Prop)
  (ker_of : ∀ (Y : PTop@{o}) (y y' : Y), y ≈ y' → ker Y y y')
  (ker_to : ∀ Y : PTop@{o}, Pr Y → ∀ y y' : Y, ker Y y y' → y ≈ y')
  (closed : ClosedUnderLimits (PFullSub@{o so} Pr))
  (pr_img : ∀ (X Y : PTop@{o}) (hY : Pr Y) (h : PMor@{o} X Y),
      Pr (img_space X Y (ker Y) (ker_of Y) (ker_to Y hY) h)) :
  { F : PTopCat@{o so} ⟶ Sub PTopCat@{o so} (PFullSub Pr) &
    F ⊣ Incl PTopCat@{o so} (PFullSub Pr) } :=
  GAFT (Incl PTopCat@{o so} (PFullSub Pr))
    (sub_Complete (PFullSub Pr) (PFullSub_Full Pr) closed PTop_Complete)
    (Continuous_PreservesImageLimit
       (creates_limits_continuous (Incl PTopCat@{o so} (PFullSub Pr))
          PTop_Complete
          (sub_CreatesAllLimits (PFullSub Pr) (PFullSub_Full Pr) closed)))
    (PFull_sols Pr ker ker_of ker_to pr_img).

Definition PFull_Reflective_GAFT@{o so +| Set < o, o < so +}
  (Pr : PTop@{o} → Type@{o}) (ker : ∀ Y : PTop@{o}, Y → Y → Prop)
  (ker_of : ∀ (Y : PTop@{o}) (y y' : Y), y ≈ y' → ker Y y y')
  (ker_to : ∀ Y : PTop@{o}, Pr Y → ∀ y y' : Y, ker Y y y' → y ≈ y')
  (closed : ClosedUnderLimits (PFullSub@{o so} Pr))
  (pr_img : ∀ (X Y : PTop@{o}) (hY : Pr Y) (h : PMor@{o} X Y),
      Pr (img_space X Y (ker Y) (ker_of Y) (ker_to Y hY) h)) :
  Reflective (PFullSub@{o so} Pr) :=
  @Build_Reflective PTopCat@{o so} (PFullSub Pr) (PFullSub_Full Pr)
    (projT1 (PFull_left_adjoint_GAFT Pr ker ker_of ker_to closed pr_img))
    (projT2 (PFull_left_adjoint_GAFT Pr ker ker_of ker_to closed pr_img)).

(* For a separation premise the kernel is the premise itself, and the
   image of a map into a separated space is separated. *)
Lemma PSep_img@{o} (prem : SepPremise@{o}) (L : SepLaws@{o} prem)
  (X Y : PTop@{o}) (hY : PSep prem Y) (h : PMor@{o} X Y) :
  PSep prem (img_space X Y (prem _ (POpen Y)) (sl_equiv _ L Y) hY h).
Proof.
  intros a b Hp.
  exact (sl_pull _ L _ _ (fun s => pmap h s) (POpen Y) a b Hp).
Qed.

Definition PSep_reflective_GAFT@{o so +| Set < o, o < so +}
  (prem : SepPremise@{o}) (L : SepLaws@{o} prem) :
  Reflective (PSepSub@{o so} prem) :=
  PFull_Reflective_GAFT (PSep prem) (fun Y => prem _ (POpen Y))
    (fun Y => sl_equiv _ L Y) (fun Y hY => hY) (PSep_closed prem L)
    (PSep_img prem L).

(** ** Haus: completeness and the reflector *)

Definition Haus_Sub@{o so | o < so +} : Subcategory@{so o o o} PTopCat@{o so} :=
  PSepSub@{o so} prem_T2@{o}.

Definition Haus@{o so | o < so +} : Category@{so o o} :=
  Sub@{so o o o so o so} PTopCat@{o so} Haus_Sub@{o so}.

(* Mac Lane's Proposition 2, first sentence: Haus is complete, at every
   shape universe at or below the points', as [PTopCat] is. *)
Definition Haus_Complete@{r s o so +| s <= o, o < so, o <= r +} :
  @Complete@{r s o so} Haus@{o so} :=
  sub_Complete Haus_Sub (PFullSub_Full _) (PSep_closed prem_T2 prem_T2_laws)
    PTop_Complete.

Definition Haus_Incl_continuous@{o so +| o < so +} :
  ContinuousFunctor (Incl PTopCat@{o so} Haus_Sub@{o so}) :=
  creates_limits_continuous (Incl PTopCat@{o so} Haus_Sub) PTop_Complete
    (sub_CreatesAllLimits Haus_Sub (PFullSub_Full _)
       (PSep_closed prem_T2 prem_T2_laws)).

(* The issue's pinned name: the reflection of Haus in [PTopCat], its
   reflector obtained BY the general adjoint functor theorem. *)
Definition Haus_reflective@{o so +| Set < o, o < so +} :
  Reflective Haus_Sub@{o so} :=
  PSep_reflective_GAFT prem_T2 prem_T2_laws.

(* The largest Hausdorff quotient, directly (Instance/Top/Separation.v),
   is the same reflector up to natural isomorphism. *)
Definition Haus_reflectors_iso@{o so +| Set < o, o < so +} :
  reflector (Haus_reflective : Reflective Haus_Sub@{o so})
    ≈ reflector (PT2_Reflective : Reflective Haus_Sub@{o so}) :=
  left_adjoint_iso (Incl PTopCat@{o so} Haus_Sub)
    (reflector Haus_reflective) (reflector PT2_Reflective)
    (reflective_adj Haus_reflective) (reflective_adj PT2_Reflective).

(* "If X is already Hausdorff, we may take HX = X": up to isomorphism, the
   counit at a Hausdorff space. *)
Definition Haus_counit_iso@{o so +| Set < o, o < so +} (X : Haus@{o so}) :
  reflector Haus_reflective (Incl PTopCat@{o so} Haus_Sub X) ≅[Haus@{o so}] X :=
  reflective_counit_iso Haus_reflective X.

(*
   本节说明 Hausdorff 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Haus_unit_surjective_direct@{o so +| o < so +}
  (X : PTopCat@{o so})
  (y : carrier (pt_carrier (`1 (fobj[reflector PT2_Reflective] X)))) :
  { x : carrier (pt_carrier X) &
    pmap (@unit _ _ _ _ (reflective_adj PT2_Reflective) X) x ≈ y }.
Proof. exists y. reflexivity. Defined.

(*
   本节说明 Hausdorff 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Haus_unit_surjective@{o so +| Set < o, o < so +}
  (X : PTopCat@{o so})
  (y : carrier (pt_carrier (`1 (fobj[reflector Haus_reflective] X)))) :
  { x : carrier (pt_carrier X) &
    pmap (@unit _ _ _ _ (reflective_adj Haus_reflective) X) x ≈ y }.
Proof.
  pose (A := reflective_adj (Haus_reflective : Reflective Haus_Sub@{o so})).
  pose (B := reflective_adj (PT2_Reflective : Reflective Haus_Sub@{o so})).
  pose (RX := fobj[reflector Haus_reflective] X).
  pose (DX := fobj[reflector PT2_Reflective] X).
  pose (psi := from (@adj _ _ _ _ A X DX) (@unit _ _ _ _ B X)).
  pose (phi := from (@adj _ _ _ _ B X RX) (@unit _ _ _ _ A X)).
  assert (H2 : fmap[Incl PTopCat@{o so} Haus_Sub] phi ∘ @unit _ _ _ _ B X
                 ≈ @unit _ _ _ _ A X).
  { transitivity (to (@adj _ _ _ _ B X RX) phi).
    - symmetry. exact (@to_adj_unit _ _ _ _ B _ _ phi).
    - exact (@from_adj_comp_law _ _ _ _ B _ _ (@unit _ _ _ _ A X)). }
  assert (H1 : fmap[Incl PTopCat@{o so} Haus_Sub] psi ∘ @unit _ _ _ _ A X
                 ≈ @unit _ _ _ _ B X).
  { transitivity (to (@adj _ _ _ _ A X DX) psi).
    - symmetry. exact (@to_adj_unit _ _ _ _ A _ _ psi).
    - exact (@from_adj_comp_law _ _ _ _ A _ _ (@unit _ _ _ _ B X)). }
  assert (H3 : phi ∘ psi ≈ id[RX]).
  { transitivity (from (@adj _ _ _ _ A X RX) (@unit _ _ _ _ A X)).
    - apply (snd (@adj_univ _ _ _ _ A _ _ (phi ∘ psi) (@unit _ _ _ _ A X))).
      rewrite (@to_adj_unit _ _ _ _ A _ _ (phi ∘ psi)).
      rewrite fmap_comp, <- comp_assoc.
      transitivity (fmap[Incl PTopCat@{o so} Haus_Sub] phi ∘ @unit _ _ _ _ B X);
        [|exact H2].
      apply compose_respects; [reflexivity|exact H1].
    - exact (@from_adj_unit _ _ _ _ A X). }
  exists (pmap (`1 psi) y).
  transitivity (pmap (`1 phi) (pmap (`1 psi) y)).
  - symmetry. exact (H2 (pmap (`1 psi) y)).
  - exact (H3 y).
Defined.

(* Riehl §4.7 Exercise ii, and Mac Lane's "it follows that Haus has all
   small colimits": cocompleteness by transfer along the reflection. *)
Definition Haus_Cocomplete@{o so +| Set < o, o < so +} :
  @Cocomplete Haus@{o so} :=
  reflective_Cocomplete Haus_reflective PTop_Cocomplete.

(* The same transfer along the direct reflector, which needs no [Set < o];
   its colimit apex is the largest Hausdorff quotient of the colimit in
   [PTopCat], on the nose. *)
Definition Haus_Cocomplete_direct@{o so +| o < so +} :
  @Cocomplete Haus@{o so} :=
  reflective_Cocomplete PT2_Reflective PTop_Cocomplete.

Example Haus_colimit_apex@{o so +| o < so +} (J : Category@{o o o})
  (K : J ⟶ Haus@{o so}) :
  colimit_apex (Haus_Cocomplete_direct J K)
    = fobj[reflector PT2_Reflective]
        (colimit_apex (PTop_Cocomplete J (Incl PTopCat@{o so} Haus_Sub ◯ K)))
  := eq_refl.

(* "as does the forgetful functor Haus → Set": the reflection of the
   discrete space. *)
Definition Haus_Forget_left_adjoint@{o so +| Set < o, o < so +} :
  (reflector (Haus_reflective : Reflective Haus_Sub@{o so}) ◯ PDisc@{o so})
    ⊣ (PForget@{o so} ◯ Incl PTopCat@{o so} Haus_Sub@{o so}) :=
  Adjunction_Compose PDisc_PForget (reflective_adj Haus_reflective).

Definition Haus_Forget_left_adjoint_direct@{o so +| o < so +} :
  (reflector (PT2_Reflective : Reflective Haus_Sub@{o so}) ◯ PDisc@{o so})
    ⊣ (PForget@{o so} ◯ Incl PTopCat@{o so} Haus_Sub@{o so}) :=
  Adjunction_Compose PDisc_PForget (reflective_adj PT2_Reflective).

(** ** A coproduct of Hausdorff spaces is Hausdorff *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Coproduct.

Universes o i u.
Constraint i <= o.

Context (Ix : Type@{i}) (X : Ix → PTop@{o}).

Local Notation F := (fun k => pt_carrier (X k)).

(* A summand is open: its preimage along each injection is constant. *)
Lemma psigma_summand_open (k : Ix) :
  POpen (PSigma@{o i u} Ix X) (fun p => projT1 p = k).
Proof.
  refine (conj _ _).
  - intros [a x] [b y] [e _] h. simpl in *. exact (eq_trans (eq_sym e) h).
  - intro k'. exact (popen_const (X k') (k' = k)).
Qed.

(* The image of a predicate on a summand: the points of that summand, read
   along a proof that they lie in it, at which the predicate holds. *)
Definition psigma_img (k : Ix) (U : X k → Prop)
  (p : carrier (pt_carrier (PSigma@{o i u} Ix X))) : Prop :=
  ex (fun e : projT1 p = k =>
        U (eq_rect _ (fun j => carrier (F j)) (projT2 p) k e)).

Lemma psigma_img_open (k : Ix) (U : X k → Prop) (HU : POpen (X k) U) :
  POpen (PSigma@{o i u} Ix X) (psigma_img k U).
Proof.
  refine (conj _ _).
  - intros [a x] [b y] [e0 H0] [e h]. simpl in *.
    destruct e0. simpl in H0. subst a.
    exists eq_refl. simpl in *.
    exact (popen_proper (X k) U HU x y H0 h).
  - intro k'.
    apply (popen_respects (X k')
             (fun x => ex (fun W => ex (fun e : k' = k =>
                  ∀ z, W z <-> U (eq_rect _ (fun j => carrier (F j)) z k e))
                  /\ W x))).
    + intro x. split.
      * intros [W [[e HW] w]]. exists e. exact (proj1 (HW x) w).
      * intros [e u].
        exists (fun z => U (eq_rect _ (fun j => carrier (F j)) z k e)).
        split; [exists e; intro z; exact (iff_refl _)|exact u].
    + apply popen_union. intros W [e HW].
      apply (popen_respects (X k')
               (fun z => U (eq_rect _ (fun j => carrier (F j)) z k e))).
      * intro z. exact (iff_sym (HW z)).
      * subst k'. exact HU.
Qed.

Lemma PHaus_coproduct (uip : ∀ (k : Ix) (e : k = k), e = eq_refl)
  (HX : ∀ k, PHaus (X k)) : PHaus (PSigma@{o i u} Ix X).
Proof.
  intros [a x] [b y] Hp.
  assert (e : a = b).
  { destruct (Hp (fun p => projT1 p = a) (fun p => projT1 p = b)
                (psigma_summand_open a) (psigma_summand_open b)
                eq_refl eq_refl) as [z [za zb]].
    exact (eq_trans (eq_sym za) zb). }
  subst b.
  refine (existT _ eq_refl _). simpl.
  apply (HX a). intros U V HU HV u v.
  destruct (Hp (psigma_img a U) (psigma_img a V)
              (psigma_img_open a U HU) (psigma_img_open a V HV)
              (ex_intro _ eq_refl u) (ex_intro _ eq_refl v))
    as [[c z] [[e1 h1] [e2 h2]]].
  simpl in *. subst c.
  rewrite (uip a e2) in h2.
  exists z. exact (conj h1 h2).
Qed.

End Coproduct.

(* Hedberg's theorem: a type with decidable equality has only [eq_refl] as
   a loop. *)
Lemma sep_dec_uip@{i} (A : Type@{i})
  (dec : ∀ a b : A, sumbool (a = b) (a = b → False)) (a : A) (e : a = a) :
  e = eq_refl.
Proof.
  pose (nu := fun (b : A) (p : a = b) =>
          match dec a b with left q => q | right n => False_ind _ (n p) end).
  assert (Hc : ∀ b (p q : a = b), nu b p = nu b q).
  { intros b p q. unfold nu. destruct (dec a b) as [r|n];
      [reflexivity|destruct (n p)]. }
  assert (Hl : ∀ b (p : a = b),
            eq_trans (eq_sym (nu a eq_refl)) (nu b p) = p).
  { intros b p. destruct p. destruct (nu a eq_refl). reflexivity. }
  transitivity (eq_trans (eq_sym (nu a eq_refl)) (nu a e)).
  - symmetry. exact (Hl a e).
  - rewrite (Hc a e eq_refl). exact (Hl a eq_refl).
Qed.

(* So a coproduct of Hausdorff spaces over an index with decidable
   equality, [bool] for a binary coproduct among them, is Hausdorff. *)
Corollary PHaus_coproduct_dec@{o i u +| i <= o, o < u +} (Ix : Type@{i})
  (X : Ix → PTop@{o}) (dec : ∀ a b : Ix, sumbool (a = b) (a = b → False))
  (HX : ∀ k, PHaus (X k)) : PHaus (PSigma@{o i u} Ix X).
Proof. exact (PHaus_coproduct Ix X (sep_dec_uip Ix dec) HX). Qed.

(** ** T0 and T1 spaces by the same argument *)

Definition PT0_reflective_GAFT@{o so +| Set < o, o < so +} :
  Reflective (PSepSub@{o so} prem_T0@{o}) :=
  PSep_reflective_GAFT prem_T0 prem_T0_laws.

Definition PT1_reflective_GAFT@{o so +| Set < o, o < so +} :
  Reflective (PSepSub@{o so} prem_T1@{o}) :=
  PSep_reflective_GAFT prem_T1 prem_T1_laws.

(** ** Regular spaces: Exercise 4 at n = 2 *)

(* The closure of a predicate for a family of opens: the points each open
   neighbourhood of which meets it. *)
Definition PClosureIn@{o} (S : Type@{o}) (O : (S → Prop) → Prop)
  (W : S → Prop) (y : S) : Prop :=
  ∀ Z, O Z → Z y → ex (fun z => Z z /\ W z).

(* Regularity, positively: every open neighbourhood of a point contains
   the closure of a smaller one. *)
Definition PRegOpens@{o} (S : Type@{o}) (O : (S → Prop) → Prop) : Prop :=
  ∀ U, O U → ∀ x, U x →
    ex (fun V => O V /\ V x /\ ∀ y, PClosureIn S O V y → U y).

Definition PReg@{o} (X : PTop@{o}) : Prop := PRegOpens _ (POpen X).

(* T3: regular and Hausdorff. *)
Definition PT3@{o} (X : PTop@{o}) : Type@{o} := (PHaus X * PReg X)%type.

(* A regular T0 space is Hausdorff, so T3 is also "regular and T0". *)
Lemma PReg_PT0_PHaus@{o} (X : PTop@{o}) : PReg X → PT0 X → PHaus X.
Proof.
  intros HR H0 x y Hp. apply H0. intros U HU. split; intro u.
  - destruct (HR U HU x u) as [V [HV [v Hc]]].
    apply Hc. intros Z HZ z.
    destruct (Hp V Z HV HZ v z) as [w [a b]]. exists w. exact (conj b a).
  - destruct (HR U HU y u) as [V [HV [v Hc]]].
    apply Hc. intros Z HZ z.
    destruct (Hp Z V HZ HV z v) as [w [a b]]. exists w. exact (conj a b).
Qed.

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma plimit_PReg@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (N : Cone T) (HN : IsLimitCone N)
  (HT : ∀ k, PReg (T k)) : PReg (vertex_obj[N]).
Proof.
  intros U HU x u.
  pose (Cls := fun W : vertex_obj[N] → Prop =>
    POpen (vertex_obj[N]) W /\
    ∀ z, W z → ex (fun V => POpen (vertex_obj[N]) V /\ V z /\
                   ∀ y, PClosureIn _ (POpen (vertex_obj[N])) V y → W y)).
  assert (HCls : Cls U).
  { pose proof (proj1 (PTop_limit_open_iff_initial T N HN U) HU) as HI.
    refine (HI Cls _ _).
    - split; [|split; [|split]].
      + intros U1 U2 E [H1 H2]. split.
        * exact (popen_respects _ U1 U2 E H1).
        * intros z w2. destruct (H2 z (proj2 (E z) w2)) as [V [HV [v Hc]]].
          exists V. split; [exact HV|]. split; [exact v|].
          intros y cy. exact (proj1 (E y) (Hc y cy)).
      + intros F HF. split.
        * apply popen_union. intros W FW. exact (proj1 (HF W FW)).
        * intros z [W [FW w]].
          destruct (proj2 (HF W FW) z w) as [V [HV [v Hc]]].
          exists V. split; [exact HV|]. split; [exact v|].
          intros y cy. exists W. exact (conj FW (Hc y cy)).
      + split; [exact (popen_whole _)|].
        intros z _. exists (fun _ => True).
        split; [exact (popen_whole _)|]. split; [exact I|]. intros; exact I.
      + intros U1 U2 [H1 C1] [H2 C2].
        split; [exact (popen_inter _ _ _ H1 H2)|].
        intros z [w1 w2].
        destruct (C1 z w1) as [V1 [HV1 [v1 K1]]].
        destruct (C2 z w2) as [V2 [HV2 [v2 K2]]].
        exists (fun s => V1 s /\ V2 s).
        split; [exact (popen_inter _ _ _ HV1 HV2)|].
        split; [exact (conj v1 v2)|].
        intros y cy. split.
        * apply K1. intros Z HZ zy.
          destruct (cy Z HZ zy) as [w [a [b _]]]. exists w. exact (conj a b).
        * apply K2. intros Z HZ zy.
          destruct (cy Z HZ zy) as [w [a [_ b]]]. exists w. exact (conj a b).
    - intros W [k [U' [HU' HW]]]. split.
      + apply (popen_respects _ (fun s => U' (pmap (cone_leg N k) s))).
        * intro s. exact (iff_sym (HW s)).
        * exact (pcont (cone_leg N k) U' HU').
      + intros z w.
        destruct (HT k U' HU' (pmap (cone_leg N k) z) (proj1 (HW z) w))
          as [V' [HV' [v' Hc']]].
        exists (fun s => V' (pmap (cone_leg N k) s)).
        split; [exact (pcont (cone_leg N k) V' HV')|].
        split; [exact v'|].
        intros y cy. apply (proj2 (HW y)). apply Hc'.
        intros Z HZ zy.
        destruct (cy (fun s => Z (pmap (cone_leg N k) s))
                    (pcont (cone_leg N k) Z HZ) zy) as [w' [a b]].
        exists (pmap (cone_leg N k) w'). exact (conj a b). }
  exact (proj2 HCls x u).
Qed.

Definition PT3_closed@{o so +| o < so +} :
  ClosedUnderLimits (PFullSub@{o so} PT3@{o}) :=
  fun J K N HN =>
    (plimit_PSep prem_T2 prem_T2_laws
       (Incl PTopCat@{o so} (PFullSub PT3) ◯ K) N HN (fun k => fst (`2 (K k))),
     plimit_PReg (Incl PTopCat@{o so} (PFullSub PT3) ◯ K) N HN
       (fun k => snd (`2 (K k)))).

(* The image presentation of a map into a regular space is regular: its
   opens are the preimages of opens. *)
Lemma img_PReg@{o} (X Y : PTop@{o}) (k : Y → Y → Prop)
  (k_of : ∀ y y' : Y, y ≈ y' → k y y') (k_to : ∀ y y' : Y, k y y' → y ≈ y')
  (h : PMor@{o} X Y) : PReg Y → PReg (img_space X Y k k_of k_to h).
Proof.
  intros HY U [W [HW HUW]] x u.
  destruct (HY W HW (pmap h x) (proj1 (HUW x) u)) as [V' [HV' [v' Hc]]].
  exists (fun s => V' (pmap h s)). split.
  - exists V'. split; [exact HV'|]. intro s. exact (iff_refl _).
  - split; [exact v'|].
    intros y cy. apply (proj2 (HUW y)). apply Hc.
    intros Z HZ zy.
    destruct (cy (fun s => Z (pmap h s))
                (ex_intro _ Z (conj HZ (fun s => iff_refl _))) zy)
      as [w [a b]].
    exists (pmap h w). exact (conj a b).
Qed.

Definition PT3_img@{o} (X Y : PTop@{o}) (hY : PT3 Y) (h : PMor@{o} X Y) :
  PT3 (img_space X Y (prem_T2 _ (POpen Y)) (sl_equiv _ prem_T2_laws Y)
         (fst hY) h) :=
  (PSep_img prem_T2 prem_T2_laws X Y (fst hY) h,
   img_PReg X Y _ _ _ h (snd hY)).

(* The reflection of T3 spaces in all spaces, by the same argument. *)
Definition PT3_reflective_GAFT@{o so +| Set < o, o < so +} :
  Reflective (PFullSub@{o so} PT3@{o}) :=
  PFull_Reflective_GAFT PT3 (fun Y => prem_T2 _ (POpen Y))
    (fun Y => sl_equiv _ prem_T2_laws Y) (fun Y hY => fst hY) PT3_closed
    PT3_img.

(* The discrete two-point space is T3: a point's singleton is open and is
   its own closure. *)
Lemma PBool_PReg@{o} : PReg PBool@{o}.
Proof.
  intros U HU x u. exists (fun z => z = x). split.
  - intros a b e h. change (a = b) in e. congruence.
  - split; [reflexivity|].
    intros y cy.
    assert (Hy : POpen PBool@{o} (fun z => z = y)).
    { intros a b e h. change (a = b) in e. congruence. }
    destruct (cy _ Hy eq_refl) as [z [e1 e2]].
    subst. exact u.
Qed.

Definition PBool_PT3@{o} : PT3 PBool@{o} := (PBool_PHaus, PBool_PReg).

(** ** Strictness: a Hausdorff space that is not regular *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive comb_pt@{} : Set :=
  | comb_inf : comb_pt
  | comb_k : nat → comb_pt
  | comb_c : nat → nat → comb_pt.

Section Comb.

Universe o.

Local Open Scope nat_scope.

Definition comb_setoid : SetoidObject@{o o} :=
  {| carrier := comb_pt; is_setoid := eq_Setoid comb_pt |}.

Definition comb_open (U : comb_setoid → Prop) : Prop :=
  (U comb_inf → ex (fun N => ∀ n m, N <= n → U (comb_c n m))) /\
  (∀ n, U (comb_k n) → ex (fun M => ∀ m, M <= m → U (comb_c n m))).

Lemma comb_open_respects (U V : comb_setoid → Prop) :
  (∀ x, U x <-> V x) → comb_open U → comb_open V.
Proof.
  intros H [H1 H2]. split.
  - intro v. destruct (H1 (proj2 (H comb_inf) v)) as [N HN].
    exists N. intros n m l. exact (proj1 (H _) (HN n m l)).
  - intros n v. destruct (H2 n (proj2 (H (comb_k n)) v)) as [M HM].
    exists M. intros m l. exact (proj1 (H _) (HM m l)).
Qed.

Lemma comb_open_proper (U : comb_setoid → Prop) :
  comb_open U → ∀ x y : comb_setoid, x ≈ y → U x → U y.
Proof. intros _ x y e u. simpl in e. subst y. exact u. Qed.

Lemma comb_open_union (F : (comb_setoid → Prop) → Prop) :
  (∀ U, F U → comb_open U) → comb_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF. split.
  - intros [U [FU u]]. destruct (proj1 (HF U FU) u) as [N HN].
    exists N. intros n m l. exists U. exact (conj FU (HN n m l)).
  - intros n [U [FU u]]. destruct (proj2 (HF U FU) n u) as [M HM].
    exists M. intros m l. exists U. exact (conj FU (HM m l)).
Qed.

Lemma comb_open_whole : comb_open (fun _ => True).
Proof. split; [intros _; exists 0|intros n _; exists 0]; intros; exact I. Qed.

Lemma comb_open_inter (U V : comb_setoid → Prop) :
  comb_open U → comb_open V → comb_open (fun x => U x /\ V x).
Proof.
  intros [U1 U2] [V1 V2]. split.
  - intros [u v]. destruct (U1 u) as [N HN], (V1 v) as [N' HN'].
    exists (N + N'). intros n m l. split.
    + exact (HN n m (sep_le_trans _ _ _ (sep_le_add_r N N') l)).
    + exact (HN' n m (sep_le_trans _ _ _ (sep_le_add_l N N') l)).
  - intros n [u v]. destruct (U2 n u) as [M HM], (V2 n v) as [M' HM'].
    exists (M + M'). intros m l. split.
    + exact (HM m (sep_le_trans _ _ _ (sep_le_add_r M M') l)).
    + exact (HM' m (sep_le_trans _ _ _ (sep_le_add_l M M') l)).
Qed.

Definition PComb : PTop@{o} := {|
  pt_carrier     := comb_setoid;
  POpen          := comb_open;
  popen_respects := comb_open_respects;
  popen_proper   := comb_open_proper;
  popen_union    := comb_open_union;
  popen_whole    := comb_open_whole;
  popen_inter    := comb_open_inter
|}.

(* The basic neighbourhoods: a tooth point alone, a spine point with the
   tail of its tooth, and [comb_inf] with the teeth from [N] on. *)
Lemma comb_open_c (n m : nat) : POpen PComb (fun z => z = comb_c n m).
Proof. split; [intro e; discriminate e|intros k e; discriminate e]. Qed.

Lemma comb_open_k (n M : nat) :
  POpen PComb (fun z => z = comb_k n \/ ex (fun m => M <= m /\ z = comb_c n m)).
Proof.
  split.
  - intros [e|[m [_ e]]]; discriminate e.
  - intros k [e|[m [_ e]]]; [|discriminate e].
    injection e as <-. exists M. intros m l. right. exists m.
    exact (conj l eq_refl).
Qed.

Lemma comb_open_inf (N : nat) :
  POpen PComb (fun z => z = comb_inf \/
                        ex (fun n => ex (fun m => N <= n /\ z = comb_c n m))).
Proof.
  split.
  - intros _. exists N. intros n m l. right. exists n, m.
    exact (conj l eq_refl).
  - intros k [e|[n [m [_ e]]]]; discriminate e.
Qed.

Lemma PComb_PHaus : PHaus PComb.
Proof.
  intros x y H. change (x = y).
  destruct x as [|a|a b], y as [|a'|a' b']; try reflexivity.
  - destruct (H _ _ (comb_open_inf (S a')) (comb_open_k a' 0)
                (or_introl eq_refl) (or_introl eq_refl))
      as [z [[e|[n [m [l e]]]] [e'|[m' [_ e']]]]];
      subst z; try discriminate e'.
    injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
  - destruct (H _ _ (comb_open_inf (S a')) (comb_open_c a' b')
                (or_introl eq_refl) eq_refl)
      as [z [[e|[n [m [l e]]]] e']]; subst z; try discriminate e'.
    injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
  - destruct (H _ _ (comb_open_k a 0) (comb_open_inf (S a))
                (or_introl eq_refl) (or_introl eq_refl))
      as [z [[e|[m [_ e]]] [e'|[n [m' [l e']]]]]];
      subst z; try discriminate e'.
    injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
  - destruct (H _ _ (comb_open_k a 0) (comb_open_k a' 0)
                (or_introl eq_refl) (or_introl eq_refl))
      as [z [[e|[m [_ e]]] [e'|[m' [_ e']]]]]; subst z.
    + exact e'.
    + discriminate e'.
    + discriminate e'.
    + injection e' as <- _. reflexivity.
  - destruct (H _ _ (comb_open_k a (S b')) (comb_open_c a' b')
                (or_introl eq_refl) eq_refl)
      as [z [[e|[m [l e]]] e']]; subst z; try discriminate e'.
    injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
  - destruct (H _ _ (comb_open_c a b) (comb_open_inf (S a))
                eq_refl (or_introl eq_refl))
      as [z [e [e'|[n [m [l e']]]]]]; subst z; try discriminate e'.
    injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
  - destruct (H _ _ (comb_open_c a b) (comb_open_k a' (S b))
                eq_refl (or_introl eq_refl))
      as [z [e [e'|[m [l e']]]]]; subst z; try discriminate e'.
    injection e' as <- <-. exfalso. exact (sep_not_succ_le _ l).
  - destruct (H _ _ (comb_open_c a b) (comb_open_c a' b') eq_refl eq_refl)
      as [z [e e']]. subst z. exact e'.
Qed.

(* The complement of the spine is an open neighbourhood of [comb_inf];
   the closure of any smaller one meets the spine. *)
Lemma PComb_not_PReg : PReg PComb → False.
Proof.
  intro HR.
  pose (U := fun z : comb_pt =>
               match z with comb_k _ => False | _ => True end).
  assert (HU : POpen PComb U).
  { split.
    - intros _. exists 0. intros; exact I.
    - intros n u. destruct u. }
  destruct (HR U HU comb_inf I) as [V [[HV1 _] [v Hc]]].
  destruct (HV1 v) as [N HN].
  apply (Hc (comb_k N)).
  intros Z [_ HZ] z. destruct (HZ N z) as [M HM].
  exists (comb_c N M). split.
  - exact (HM M (le_n M)).
  - exact (HN N M (le_n N)).
Qed.

End Comb.

(** ** Exercise 4: the successive inclusions, by the adjoint functor theorem *)

(* n = 0: Top_1 → Top_0, the T1 spaces among the T0 spaces. *)
Definition PT1_in_PT0_reflective_GAFT@{o so +| Set < o, o < so +} :
  Reflective (restrict_sub (PSepSub@{o so} prem_T0@{o})
                           (PSepSub@{o so} prem_T1@{o})) :=
  restrict_Reflective (PSepSub prem_T0) (PSepSub prem_T1) (PFullSub_Full _)
    PT1_PT0 PT1_reflective_GAFT.

(* n = 1: Top_2 → Top_1, the Hausdorff spaces among the T1 spaces. *)
Definition Haus_in_PT1_reflective_GAFT@{o so +| Set < o, o < so +} :
  Reflective (restrict_sub (PSepSub@{o so} prem_T1@{o}) Haus_Sub@{o so}) :=
  restrict_Reflective (PSepSub prem_T1) Haus_Sub (PFullSub_Full _)
    PHaus_PT1 Haus_reflective.

(* n = 2: Top_3 → Top_2, the regular Hausdorff spaces among the Hausdorff
   spaces. *)
Definition PT3_in_Haus_reflective_GAFT@{o so +| Set < o, o < so +} :
  Reflective (restrict_sub Haus_Sub@{o so} (PFullSub@{o so} PT3@{o})) :=
  restrict_Reflective Haus_Sub (PFullSub PT3) (PFullSub_Full _)
    (fun X p => fst p) PT3_reflective_GAFT.

(* The issue's pinned name: the reflections of Exercise 4 that are
   delivered, n = 0, 1, 2, each produced by [GAFT]. *)
Definition separation_axiom_reflections@{o so +| Set < o, o < so +} :
  (Reflective (restrict_sub (PSepSub@{o so} prem_T0@{o})
                            (PSepSub@{o so} prem_T1@{o}))
   * Reflective (restrict_sub (PSepSub@{o so} prem_T1@{o}) Haus_Sub@{o so})
   * Reflective (restrict_sub Haus_Sub@{o so} (PFullSub@{o so} PT3@{o})))%type
  :=
  (PT1_in_PT0_reflective_GAFT, Haus_in_PT1_reflective_GAFT,
   PT3_in_Haus_reflective_GAFT).

(** ** Exercise 5: a coequalizer of Hausdorff spaces that is not Hausdorff *)

Section Ex5Spaces.

Universe o.

Local Open Scope nat_scope.

(* Two Hausdorff spaces: the discrete naturals, and the convergent sequence
   ℕ∞ of Instance/Top/Complete.v. *)
Definition PNat : PTop@{o} := PDiscrete pnat_setoid@{o}.

Lemma PNat_PHaus : PHaus PNat.
Proof.
  intros x y H. change (x = y).
  destruct (H (fun z => z = x) (fun z => z = y)) as [z [e1 e2]].
  - intros a b e u; simpl in e; subst; reflexivity.
  - intros a b e u; simpl in e; subst; reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. congruence.
Qed.

(* The tail above [n] is a neighbourhood of the limit point. *)
Lemma PConv_tail_open (n : nat) :
  POpen PConv@{o} (fun z => match z with None => True | Some k => n < k end).
Proof. intros _. exists (S n). intros m Hm. exact Hm. Qed.

Lemma PConv_PHaus : PHaus PConv@{o}.
Proof.
  intros x y H. simpl.
  destruct x as [n|], y as [m|].
  - destruct (H (fun z => z = Some n) (fun z => z = Some m)) as [z [e1 e2]].
    + intro e; discriminate e.
    + intro e; discriminate e.
    + reflexivity.
    + reflexivity.
    + congruence.
  - exfalso.
    destruct (H (fun z => z = Some n) _ (fun e => ltac:(discriminate e))
                (PConv_tail_open n) eq_refl I) as [z [e1 e2]].
    subst z. exact (sep_not_succ_le n e2).
  - exfalso.
    destruct (H _ (fun z => z = Some m) (PConv_tail_open m)
                (fun e => ltac:(discriminate e)) I eq_refl) as [z [e1 e2]].
    subst z. exact (sep_not_succ_le m e1).
  - reflexivity.
Qed.

(* The classical negative Hausdorff axiom holds of ℕ∞ as well. *)
Lemma PConv_PIsHausdorff : PIsHausdorff PConv@{o}.
Proof.
  intros x y Hne.
  destruct x as [n|], y as [m|].
  - exists (fun z => z = Some n), (fun z => z = Some m).
    repeat split.
    + intro e; discriminate e.
    + intro e; discriminate e.
    + intros z e1 e2. apply Hne. simpl. congruence.
  - exists (fun z => z = Some n),
           (fun z => match z with None => True | Some k => n < k end).
    repeat split.
    + intro e; discriminate e.
    + exact (PConv_tail_open n).
    + intros z e1 e2. subst z. exact (sep_not_succ_le n e2).
  - exists (fun z => match z with None => True | Some k => m < k end),
           (fun z => z = Some m).
    repeat split.
    + exact (PConv_tail_open m).
    + intro e; discriminate e.
    + intros z e1 e2. subst z. exact (sep_not_succ_le m e1).
  - exfalso. apply Hne. reflexivity.
Qed.

(* The parallel pair n ↦ 2n, n ↦ 2n + 2 from ℕ into ℕ∞: its coequalizer
   glues the even points of the sequence to one point, which the limit
   point cannot be separated from. *)
Definition glue_f_set :
  @SetoidMorphism@{o o o} _ (is_setoid pnat_setoid@{o}) _
    (is_setoid (pt_carrier PConv@{o})) :=
  @Build_SetoidMorphism _ (is_setoid pnat_setoid@{o}) _
    (is_setoid (pt_carrier PConv@{o})) (fun n : nat => Some (n + n))
    (fun a b (e : a = b) => f_equal (fun n : nat => Some (n + n)) e).

Definition glue_g_set :
  @SetoidMorphism@{o o o} _ (is_setoid pnat_setoid@{o}) _
    (is_setoid (pt_carrier PConv@{o})) :=
  @Build_SetoidMorphism _ (is_setoid pnat_setoid@{o}) _
    (is_setoid (pt_carrier PConv@{o})) (fun n : nat => Some (S (S (n + n))))
    (fun a b (e : a = b) => f_equal (fun n : nat => Some (S (S (n + n)))) e).

(* The generated relation never relates a point of the sequence to the
   limit point. *)
Lemma glue_none_inv (a b : option nat) :
  coeq_rel glue_f_set glue_g_set a b → (a = None <-> b = None).
Proof.
  intro H.
  induction H as [b1 b2 e | n | b1 b2 _ IH | b1 b2 b3 _ IH1 _ IH2].
  - simpl in e. subst. exact (iff_refl _).
  - split; intro e; discriminate e.
  - split; [exact (proj2 IH)|exact (proj1 IH)].
  - split; intro e;
      [exact (proj1 IH2 (proj1 IH1 e))|exact (proj2 IH1 (proj2 IH2 e))].
Qed.

End Ex5Spaces.

Section Ex5Arith.

Local Open Scope nat_scope.

Lemma double_succ@{} (k : nat) : S k + S k = S (S (k + k)).
Proof. simpl. f_equal. symmetry. exact (plus_n_Sm k k). Qed.

End Ex5Arith.

Section Ex5.

Universes o so.
Constraint o < so.

Local Open Scope nat_scope.

Definition glue_f : PNat ~{PTopCat@{o so}}~> PConv@{o} :=
  pdisc_mor pnat_setoid PConv glue_f_set.

Definition glue_g : PNat ~{PTopCat@{o so}}~> PConv@{o} :=
  pdisc_mor pnat_setoid PConv glue_g_set.

(* The coequalizer in [PTopCat], as the tree chooses it. *)
Definition glue_coeq :=
  @coeq PTopCat@{o so} PTop_HasCoequalizers PNat PConv glue_f glue_g.

Definition GlueQ : PTopCat@{o so} := `1 glue_coeq.

Definition glue_q : PConv@{o} ~{PTopCat@{o so}}~> GlueQ := `1 (`2 glue_coeq).

Definition glue_IsCoequalizer :
  @IsCoequalizer PTopCat@{o so} PNat PConv glue_f glue_g GlueQ glue_q :=
  `2 (`2 glue_coeq).

Lemma GlueQ_points_apart : @equiv _ (pt_carrier GlueQ) (Some 0) None → False.
Proof.
  intro H.
  pose proof (glue_none_inv _ _ H) as [_ Hb].
  discriminate (Hb eq_refl).
Qed.

(* Every neighbourhood of the limit point holds a tail of the sequence,
   so an even point, glued to [Some 0]. *)
Lemma GlueQ_notsep : PNotSep GlueQ (Some 0) None.
Proof.
  intros U V [HUr HUo] [HVr HVo] u v.
  destruct (HVo v) as [N HN].
  assert (Hall : ∀ k, U (Some (k + k))).
  { induction k as [|k IH]; [exact u|].
    apply (HUr (Some (k + k))); [|exact IH].
    rewrite double_succ.
    exact (cq_glue glue_f_set glue_g_set k). }
  exists (Some (N + N)). split.
  - exact (Hall N).
  - apply HN. exact (sep_le_add_r N N).
Qed.

(* The book's "a coequalizer in Top of Hausdorff spaces need not be
   Hausdorff", in both forms. *)
Theorem GlueQ_not_PHaus : PHaus GlueQ → False.
Proof. intro H. exact (GlueQ_points_apart (H _ _ GlueQ_notsep)). Qed.

Theorem GlueQ_not_PIsHausdorff : PIsHausdorff GlueQ → False.
Proof.
  intro H.
  destruct (H (Some 0) None GlueQ_points_apart)
    as [U [V [HU [HV [u [v Hd]]]]]].
  destruct (GlueQ_notsep U V HU HV u v) as [z [a b]].
  exact (Hd z a b).
Qed.

(* Mac Lane: "a coequalizer in Haus is the largest Hausdorff quotient of
   the coequalizer in Top".  The direct reflection glues exactly the pair
   that [GlueQ] keeps apart. *)
Lemma GlueQ_reflection_glues : sepeq prem_T2 GlueQ (Some 0) None.
Proof.
  intros R HR.
  apply (proj2 (proj2 (proj2 (proj2 HR)))).
  apply (sl_anti _ prem_T2_laws _ _ (POpen GlueQ)); [|exact GlueQ_notsep].
  intros U [HU _]. exact HU.
Qed.

Local Notation HausC := (Sub PTopCat@{o so} Haus_Sub@{o so}).
Local Notation Inc := (Incl PTopCat@{o so} Haus_Sub@{o so}).

Definition HNat : HausC := (PNat; PNat_PHaus).
Definition HConv : HausC := (PConv@{o}; PConv_PHaus).
Definition glue_f_h : HNat ~{HausC}~> HConv := (glue_f; I).
Definition glue_g_h : HNat ~{HausC}~> HConv := (glue_g; I).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Haus_inclusion_no_right_adjoint (R : PTopCat@{o so} ⟶ HausC)
  (A : Inc ⊣ R) : False.
Proof.
  pose (q' := to (@adj _ _ _ _ A HConv GlueQ) glue_q).
  assert (Hc : q' ∘ glue_f_h ≈ q' ∘ glue_g_h).
  { pose proof (@to_adj_nat_l _ _ _ _ A HNat HConv GlueQ glue_q glue_f_h)
      as E1.
    pose proof (@to_adj_nat_l _ _ _ _ A HNat HConv GlueQ glue_q glue_g_h)
      as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A HNat GlueQ)) _ _
                  (cofork glue_IsCoequalizer)) as E3.
    exact (transitivity (symmetry E1) (transitivity E3 E2)). }
  destruct (coeq_desc glue_IsCoequalizer (z := Inc (R GlueQ)) (fmap[Inc] q') Hc)
    as [u Hu _].
  pose (eps := from (@adj _ _ _ _ A (R GlueQ) GlueQ) id).
  assert (Heq : eps ∘ fmap[Inc] q' ≈ glue_q).
  { pose proof (@from_adj_nat_l _ _ _ _ A HConv (R GlueQ) GlueQ id q') as F1.
    pose proof (proper_morphism (from (@adj _ _ _ _ A HConv GlueQ)) _ _
                  (@id_left _ _ _ q')) as F2.
    pose proof (iso_from_to (@adj _ _ _ _ A HConv GlueQ) glue_q) as F3.
    exact (transitivity (symmetry F1) (transitivity F2 F3)). }
  destruct (coeq_desc glue_IsCoequalizer (z := GlueQ) glue_q
              (cofork glue_IsCoequalizer)) as [w _ Hw].
  assert (Hret : eps ∘ u ≈ id).
  { transitivity w.
    - symmetry. apply Hw.
      rewrite <- comp_assoc. rewrite Hu. exact Heq.
    - apply Hw. apply id_left. }
  apply GlueQ_not_PHaus.
  exact (PSep_retract prem_T2 prem_T2_laws GlueQ (`1 (R GlueQ)) u eps
           (fun x => Hret x) (`2 (R GlueQ))).
Qed.

(*
   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Haus_forget_no_right_adjoint (R : Sets@{o so} ⟶ HausC)
  (A : PForget@{o so} ◯ Inc ⊣ R) : False.
Proof.
  pose (HF := PForget@{o so} ◯ Inc).
  pose (SQ := SetsCoeq (fmap[HF] glue_f_h) (fmap[HF] glue_g_h)).
  pose (s := sets_coeq_proj (fmap[HF] glue_f_h) (fmap[HF] glue_g_h)).
  pose (HS := sets_coeq_IsCoequalizer (fmap[HF] glue_f_h) (fmap[HF] glue_g_h)).
  pose (q' := to (@adj _ _ _ _ A HConv SQ) s).
  assert (Hc : q' ∘ glue_f_h ≈ q' ∘ glue_g_h).
  { pose proof (@to_adj_nat_l _ _ _ _ A HNat HConv SQ s glue_f_h) as E1.
    pose proof (@to_adj_nat_l _ _ _ _ A HNat HConv SQ s glue_g_h) as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A HNat SQ)) _ _
                  (cofork HS)) as E3.
    exact (transitivity (symmetry E1) (transitivity E3 E2)). }
  pose (eps := from (@adj _ _ _ _ A (R SQ) SQ) id).
  assert (Heq : eps ∘ fmap[HF] q' ≈ s).
  { pose proof (@from_adj_nat_l _ _ _ _ A HConv (R SQ) SQ id q') as F1.
    pose proof (proper_morphism (from (@adj _ _ _ _ A HConv SQ)) _ _
                  (@id_left _ _ _ q')) as F2.
    pose proof (iso_from_to (@adj _ _ _ _ A HConv SQ) s) as F3.
    exact (transitivity (symmetry F1) (transitivity F2 F3)). }
  assert (Hq : pmap (`1 q') (Some 0) ≈ pmap (`1 q') None).
  { refine ((`2 (R SQ) : PHaus (`1 (R SQ))) _ _ _).
    intros U V HU HV u0 v0.
    destruct (pcont (`1 q') V HV v0) as [N HN].
    assert (Hall : ∀ k, U (pmap (`1 q') (Some (k + k)))).
    { induction k as [|k IH]; [exact u0|].
      apply (popen_proper _ U HU (pmap (`1 q') (Some (k + k)))); [|exact IH].
      rewrite double_succ.
      exact (Hc k). }
    exists (pmap (`1 q') (Some (N + N))). split.
    - exact (Hall N).
    - apply HN. exact (sep_le_add_r N N). }
  assert (Hrel : @equiv _ SQ (Some 0) None).
  { transitivity (eps (pmap (`1 q') (Some 0))).
    { symmetry. exact (Heq (Some 0)). }
    transitivity (eps (pmap (`1 q') None)).
    { exact (proper_morphism eps _ _ Hq). }
    exact (Heq None). }
  pose proof (glue_none_inv (Some 0) None Hrel) as [_ Hb].
  discriminate (Hb eq_refl).
Qed.

End Ex5.
