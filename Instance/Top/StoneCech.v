Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Adjunction.GAFT.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/Stone-Cech+compactification
 nLab:  https://ncatlab.org/nlab/show/Tychonoff+theorem
 Paper: M. H. Stone, "Applications of the theory of Boolean rings to
 Paper: E. Čech, "On bicompact spaces", Ann. of Math. 38 (1937), 823–844

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** * Discrete spaces: separation, and compactness as finite enumerability *)

Lemma Discrete_Hausdorff@{h o +| o < h +} (A : SetoidObject@{o o}) :
  IsHausdorff@{h o o o} (Discrete_Top@{o o} A).
Proof.
  intros x y nxy.
  exists (fun z => z ≈ x). exists (fun z => z ≈ y).
  refine ((_, _), ((_, _), _)); simpl.
  - intros u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
  - intros u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
  - reflexivity.
  - reflexivity.
  - intros z Hx Hy. apply nxy. exact (transitivity (symmetry Hx) Hy).
Qed.

(* A finite enumeration of a setoid: a list meeting every class. *)
Definition FinEnum@{o +} (A : SetoidObject@{o o}) : Type@{o} :=
  ∃ l : list A, ∀ x : A, ∃ y : A, (In y l ∧ x ≈ y)%type.

(* Every open cover of a finitely enumerable discrete space has a finite
   subcover: one covering index per listed point. *)
Lemma Discrete_Compact_of_FinEnum@{o +} (A : SetoidObject@{o o})
  (F : FinEnum A) : IsCompact (Discrete_Top@{o o} A).
Proof.
  intros I U HU.
  destruct F as [l Hl].
  exists (map (fun y => `1 (fst (snd HU y) ttt)) l).
  intro x. destruct (Hl x) as [y [Hin Hxy]].
  exists (`1 (fst (snd HU y) ttt)). split.
  - exact (in_map (fun y => `1 (fst (snd HU y) ttt)) l y Hin).
  - exact (fst HU _ y x (symmetry Hxy) (`2 (fst (snd HU y) ttt))).
Qed.

(* Conversely, the cover by the singleton classes has a finite subcover,
   which is a finite enumeration. *)
Lemma FinEnum_of_Discrete_Compact@{o +} (A : SetoidObject@{o o})
  (C : IsCompact (Discrete_Top@{o o} A)) : FinEnum A.
Proof.
  destruct (C A (fun a z => z ≈ a)) as [l Hl].
  - split.
    + intros a u v Huv Hu. exact (transitivity (symmetry Huv) Hu).
    + intro x; split.
      * intros _. exists x. reflexivity.
      * intros _. exact ttt.
  - exists l. exact Hl.
Qed.

(* The finiteness premise is a real restriction: discrete ℕ is not
   compact. *)
Definition sc_nat_setoid@{o +} : SetoidObject@{o o} :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Lemma sc_in_le_fold_max@{} (l : list nat) (y : nat) :
  In y l → le y (fold_right Nat.max O l).
Proof.
  induction l as [|a l IH]; simpl; intro H; [contradiction|].
  destruct H as [<-|H].
  - apply Nat.le_max_l.
  - etransitivity; [exact (IH H)|apply Nat.le_max_r].
Qed.

Lemma nat_not_FinEnum@{o +} :
  FinEnum (sc_nat_setoid : SetoidObject@{o o}) → False.
Proof.
  intros [l Hl].
  destruct (Hl (S (fold_right Nat.max O l))) as [y [Hin Hy]].
  simpl in Hy. subst y.
  exact (Nat.nle_succ_diag_l _ (sc_in_le_fold_max l _ Hin)).
Qed.

Theorem Discrete_nat_not_compact@{o +} :
  IsCompact (Discrete_Top@{o o} sc_nat_setoid) → False.
Proof. intro C. exact (nat_not_FinEnum (FinEnum_of_Discrete_Compact _ C)). Qed.

(* The two-point and one-point discrete spaces as objects of [CompHaus],
   at every carrier universe. *)
Lemma bool_FinEnum@{o +} : FinEnum bool_setoid_object@{o o}.
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | reflexivity].
  - exists false. split; [right; left; reflexivity | reflexivity].
Qed.

Definition Bool_CH@{o +} : CompHaus :=
  (Bool_Discrete@{o}; (Discrete_Compact_of_FinEnum _ bool_FinEnum,
                       Discrete_Hausdorff _)).

Definition Point_CH@{o +} : CompHaus :=
  (Point_Top@{o}; (Point_Compact, Discrete_Hausdorff _)).

(** * The finite case: the discrete space is its own compactification *)

Definition Discrete_CH@{o +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  CompHaus :=
  (Discrete_Top@{o o} X;
     (Discrete_Compact_of_FinEnum X FX, Discrete_Hausdorff X)).

Definition sc_fin_unit@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget (Discrete_CH X FX) :=
  @id Sets (Setoid_Lift@{o h} X).

(* A map out of the lifted setoid, read back at the points' universe. *)
Definition sc_unlift@{o h +} (X : SetoidObject@{o o}) {d : CompHaus}
  (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  SetoidMorphism@{o o o} X (top_carrier (`1 d)) :=
  @Build_SetoidMorphism (carrier X) (is_setoid X)
    (carrier (top_carrier (`1 d))) (is_setoid (top_carrier (`1 d)))
    (fun x => f x) (fun a b e => proper_morphism f a b e).

Definition sc_fin_ext@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X)
  {d : CompHaus} (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  Discrete_CH X FX ~{CompHaus}~> d :=
  (Build_ContinuousMorphism (Discrete_Top X) (`1 d) (sc_unlift X f)
     (out_of_discrete_continuous X (`1 d) (sc_unlift X f)); I).

Definition sc_fin_ump@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X)
  (d : CompHaus) (f : Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget d) :
  ∃! g : Discrete_CH X FX ~{CompHaus}~> d,
    f ≈ fmap[CompHaus_Forget] g ∘ sc_fin_unit X FX.
Proof.
  unshelve refine {| unique_obj := sc_fin_ext X FX f |}.
  - intro x. simpl. apply reflexive_lift.
  - intros v Hv x. simpl. exact (Hv x).
Defined.

Definition StoneCech_finite@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget :=
  universal_arrow_from_UMP _ _ (Discrete_CH X FX) (sc_fin_unit X FX)
    (sc_fin_ump X FX).

Example StoneCech_finite_obj@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  @arrow_obj Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = Discrete_CH X FX := eq_refl.

Example StoneCech_finite_unit@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX := eq_refl.

(** * The reduction: continuity is free, and so is the solution set *)

(* An element [n] of a cone over [CompHaus_Forget ◯ G] is a cone over [G]
   from the one-point space. *)
Definition sc_pt_cone@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N]) : Cone G.
Proof.
  refine {| vertex_obj := Point_CH;
            coneFrom := @Build_ACone _ _ Point_CH G
              (fun x => ((top_point (`1 (G x)) (cone_leg N x n); I)
                          : Point_CH ~{CompHaus}~> G x)) _ |}.
  intros x y f t. simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f n).
Defined.

Definition sc_pres_pt@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N]) :
  carrier (top_carrier (`1 (vertex_obj[L]))) :=
  continuous_map (`1 (limit_med (limit_is_alimit L) (sc_pt_cone G N n))) ttt.

Lemma sc_pt_const_med@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) (n : vertex_obj[N])
  (p : carrier (top_carrier (`1 (vertex_obj[L]))))
  (Hp : ∀ x : J, continuous_map (`1 (limit_leg (limit_is_alimit L) x)) p
                 ≈ cone_leg N x n) :
  sc_pres_pt G L N n ≈ p.
Proof.
  unfold sc_pres_pt.
  refine (limit_med_unique (limit_is_alimit L) (sc_pt_cone G N n)
           (top_point (`1 (vertex_obj[L])) p; I) _ ttt).
  intros x t. simpl. exact (Hp x).
Qed.

Definition sc_pres_map@{j h +} {J : Category@{j h h}} (G : J ⟶ CompHaus)
  (L : Limit G) (N : Cone (CompHaus_Forget ◯ G)) :
  vertex_obj[N] ~{Sets}~> CompHaus_Forget L.
Proof.
  unshelve refine {| morphism := sc_pres_pt G L N |}.
  intros n n' e.
  apply sc_pt_const_med. intro x.
  transitivity (cone_leg N x n').
  - exact (limit_med_commutes (limit_is_alimit L) (sc_pt_cone G N n') x ttt).
  - symmetry. exact (proper_morphism (cone_leg N x) n n' e).
Defined.

Theorem CompHaus_Forget_PreservesImageLimit@{h s +} :
  @PreservesImageLimit CompHaus Sets@{h s} CompHaus_Forget.
Proof.
  intros J G L N.
  unshelve refine {| unique_obj := sc_pres_map G L N |}.
  - intros x n.
    exact (limit_med_commutes (limit_is_alimit L) (sc_pt_cone G N n) x ttt).
  - intros v Hv n. simpl.
    apply sc_pt_const_med. intro x. exact (Hv x n).
Qed.

(* Every object with every arrow: legal at the hom universe, because the
   whole object type of [CompHaus] lives there. *)
Definition taut_sols@{h s +} (d : obj[Sets@{h s}]) :
  SolutionSet CompHaus_Forget d.
Proof.
  unshelve refine
    {| sol_index := { K : CompHaus & d ~{Sets}~> CompHaus_Forget K };
       sol_obj := fun p => `1 p;
       sol_arr := fun p => `2 p |}.
  intros c h. exists (c; h). exists id.
  intro x. simpl. apply reflexive_lift.
Defined.

(* GAFT with completeness as the one remaining hypothesis.  That hypothesis
   is refuted under [IEM] (Refutations.v); this is the measured reduction,
   not a construction. *)
Definition GAFT_CompHaus_only_complete@{h s +}
  (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(** * Exercise 4 at the level of universal arrows *)

Theorem unit_injective_of_separated@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, (∀ (K : CompHaus)
                 (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
              → x ≈ y) →
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y.
Proof.
  intros Hsep x y E. apply Hsep. intros K f.
  pose proof (unique_property (ump_universal_arrows UA f)) as H.
  rewrite (H x), (H y). simpl.
  exact (proper_morphism
           (continuous_map (`1 (unique_obj (ump_universal_arrows UA f))))
           _ _ E).
Qed.

Theorem separated_of_unit_injective@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y) →
  ∀ x y : X, (∀ (K : CompHaus)
                (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
             → x ≈ y.
Proof. intros Hinj x y H. apply Hinj. exact (H _ (@arrow _ _ _ _ UA)). Qed.

(* The characteristic map of a point, into the two-point space. *)
Definition sc_chi@{o h +} (X : SetoidObject@{o o})
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) (x : X) :
  Setoid_Lift@{o h} X ~{Sets}~> CompHaus_Forget Bool_CH.
Proof.
  unshelve refine {| morphism := fun z => if dec z x then true else false |}.
  intros a b e. simpl.
  destruct (dec a x) as [ha|na], (dec b x) as [hb|nb]; try reflexivity.
  - exfalso. apply nb. exact (transitivity (symmetry e) ha).
  - exfalso. apply na. exact (transitivity e hb).
Defined.

Theorem unit_injective_of_dec@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget)
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) :
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y.
Proof.
  apply unit_injective_of_separated.
  intros x y H.
  pose proof (H Bool_CH (sc_chi X dec x)) as Hc. simpl in Hc.
  destruct (dec x x) as [_|n]; [| destruct (n (reflexivity x))].
  destruct (dec y x) as [hy|ny]; [exact (symmetry hy) | discriminate Hc].
Qed.

(* Non-vacuity: the premises are met by a universal arrow built above. *)
Definition sc_bool_dec@{o +} (x y : bool_setoid_object@{o o}) :
  (x ≈ y) + ((x ≈ y) → False).
Proof.
  destruct x, y; simpl;
    [left; reflexivity | right; discriminate | right; discriminate
    | left; reflexivity].
Defined.

Definition StoneCech_finite_bool_injective@{o h +} :=
  unit_injective_of_dec bool_setoid_object@{o o}
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
     : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} bool_setoid_object@{o o})
         CompHaus_Forget)
    sc_bool_dec.

(** * Exercise 4 at a space: the unit of the inclusion *)

(* The maps from [X] into [K] separate the points of [X].  At [K] = [0,1]
   this is the point-separating half of complete regularity. *)
Definition KSeparated@{h o +} (K : CompHaus) (X : Top@{h o}) : Type@{h} :=
  ∀ x y : top_carrier X,
    (∀ k : X ~{Top}~> CompHaus_Incl K, continuous_map k x ≈ continuous_map k y)
    → x ≈ y.

Theorem StoneCech_unit_injective_completely_regular@{h o +}
  (K : CompHaus) (X : Top@{h o}) (HX : KSeparated K X)
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl) :
  ∀ x y : top_carrier X,
    continuous_map (@arrow _ _ _ _ UA) x
      ≈ continuous_map (@arrow _ _ _ _ UA) y
    → x ≈ y.
Proof.
  intros x y E. apply HX. intro k.
  pose proof (unique_property (ump_universal_arrows UA k)) as H.
  rewrite (H x), (H y). simpl.
  exact (proper_morphism
           (continuous_map (`1 (unique_obj (ump_universal_arrows UA k))))
           _ _ E).
Qed.

(*
   本节说明 StoneCech 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem KSeparated_of_unit_injective@{h o +} (K : CompHaus)
  (sepK : ∀ (Y : CompHaus) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X.
Proof.
  intros x y Hk. apply Hinj.
  apply (sepK (@arrow_obj _ _ _ _ UA)). intro k.
  exact (Hk (fmap[CompHaus_Incl] k ∘ @arrow _ _ _ _ UA)).
Qed.

(*
   本节说明 StoneCech 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem KSeparated_of_unit_injective_local@{h o +} (K : CompHaus)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (sepK : ∀ p q : top_carrier (`1 (@arrow_obj _ _ _ _ UA)),
            (∀ k : @arrow_obj _ _ _ _ UA ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X.
Proof.
  intros x y Hk. apply Hinj.
  apply sepK. intro k.
  exact (Hk (fmap[CompHaus_Incl] k ∘ @arrow _ _ _ _ UA)).
Qed.

(* Non-vacuity of the pair of premises: at a compact Hausdorff space the
   identity is universal, and the space is separated by itself. *)
Definition CompHaus_Incl_universal@{h o +} (K : CompHaus) :
  UniversalArrow (C:=Top@{h o}) (CompHaus_Incl K) CompHaus_Incl.
Proof.
  unshelve refine (universal_arrow_from_UMP _ _ K id _).
  intros d f.
  unshelve refine {| unique_obj := (f; I) |}.
  - intro x. reflexivity.
  - intros v Hv x. simpl in *. exact (Hv x).
Defined.

Example CompHaus_Incl_universal_obj@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K) = K
  := eq_refl.

Lemma KSeparated_self@{h o +} (K : CompHaus) :
  KSeparated K (CompHaus_Incl K : obj[Top@{h o}]).
Proof. intros x y H. exact (H id). Qed.

Definition StoneCech_unit_injective_at_CompHaus@{h o +} (K : CompHaus) :=
  StoneCech_unit_injective_completely_regular K
    (CompHaus_Incl K : obj[Top@{h o}]) (KSeparated_self K)
    (CompHaus_Incl_universal K).

(* Non-vacuity of the local converse: its three premises are met at the
   identity universal arrow, the injectivity of the unit by the theorem
   just applied. *)
Definition KSeparated_of_unit_injective_local_at_CompHaus@{h o +}
  (K : CompHaus) : KSeparated K (CompHaus_Incl K : obj[Top@{h o}]) :=
  KSeparated_of_unit_injective_local K (CompHaus_Incl K : obj[Top@{h o}])
    (CompHaus_Incl_universal K) (fun p q H => H id)
    (StoneCech_unit_injective_at_CompHaus K).
