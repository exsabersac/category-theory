Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.

Generalizable All Variables.

(** * Hausdorff spaces over the Type-valued [Top] *)

(*
 nLab:      https://ncatlab.org/nlab/show/Hausdorff+space

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Separation premises with Type-valued opens *)

(* Only the premise is truncated to a proposition; the opens stay
   Type-valued, as in Instance/Top.v. *)
Definition TSepPremise@{o} :=
  ∀ S : Type@{o}, ((S → Type@{o}) → Type@{o}) → S → S → Prop.

(* T2: every open about the first point meets every open about the second,
   the meeting point truncated. *)
Definition tprem_T2@{o} : TSepPremise@{o} :=
  fun S O x y => ∀ U V, O U → O V → U x → V y →
    inhabited { z : S & (U z * V z)%type }.

Definition TSep@{o} (prem : TSepPremise@{o}) (X : TopSpace@{o}) : Type@{o} :=
  ∀ x y : X, prem _ (IsOpen X) x y → x ≈ y.

Record TSepLaws@{o} (prem : TSepPremise@{o}) : Prop := {
  tl_pull : ∀ (S S' : Type@{o}) (f : S → S') (O : (S → Type@{o}) → Type@{o})
      (O' : (S' → Type@{o}) → Type@{o}),
      (∀ W, O' W → O (fun s => W (f s))) →
      ∀ x y, prem S O x y → prem S' O' (f x) (f y);
  tl_equiv : ∀ (X : TopSpace@{o}) (x y : X), x ≈ y → prem _ (IsOpen X) x y
}.

Lemma tprem_T2_laws@{o} : TSepLaws@{o} tprem_T2@{o}.
Proof.
  constructor.
  - intros S S' f O O' sub x y H W1 W2 H1 H2 w1 w2.
    destruct (H _ _ (sub W1 H1) (sub W2 H2) w1 w2) as [[z [a b]]].
    exact (inhabits (f z; (a, b))).
  - intros X x y e U V HU HV u v.
    exact (inhabits (y; (open_proper X U HU x y e u, v))).
Qed.

(** ** The largest separated quotient *)

Section TQuotient.

Universe o.

Variable prem : TSepPremise@{o}.
Variable L : TSepLaws@{o} prem.

Context (X : TopSpace@{o}).

Local Notation P := (carrier (top_carrier X)).

Definition tsep_qopen (R : P → P → Prop) (U : P → Type@{o}) : Type@{o} :=
  (IsOpen X U * (∀ a b, R a b → U a → U b))%type.

Definition TSepRel (R : P → P → Prop) : Prop :=
  (∀ a, R a a) /\ (∀ a b, R a b → R b a) /\
  (∀ a b c, R a b → R b c → R a c) /\
  (∀ a b : P, a ≈ b → R a b) /\
  (∀ a b, prem P (tsep_qopen R) a b → R a b).

Definition tsepeq (a b : P) : Prop := ∀ R, TSepRel R → R a b.

Lemma tsepeq_refl (a : P) : tsepeq a a.
Proof. intros R HR. exact (proj1 HR a). Qed.

Lemma tsepeq_sym (a b : P) : tsepeq a b → tsepeq b a.
Proof. intros e R HR. exact (proj1 (proj2 HR) a b (e R HR)). Qed.

Lemma tsepeq_trans (a b c : P) : tsepeq a b → tsepeq b c → tsepeq a c.
Proof.
  intros e1 e2 R HR.
  exact (proj1 (proj2 (proj2 HR)) a b c (e1 R HR) (e2 R HR)).
Qed.

Lemma tsepeq_of_equiv (a b : P) : a ≈ b → tsepeq a b.
Proof. intros e R HR. exact (proj1 (proj2 (proj2 (proj2 HR))) a b e). Qed.

Definition tsep_setoid : SetoidObject@{o o} :=
  {| carrier := P;
     is_setoid := {| equiv := tsepeq;
                     setoid_equiv := Build_Equivalence tsepeq tsepeq_refl
                                       tsepeq_sym tsepeq_trans |} |}.

Definition tsep_q :
  @SetoidMorphism@{o o o} _ (is_setoid (top_carrier X)) _
    (is_setoid tsep_setoid) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier X)) _ (is_setoid tsep_setoid)
    (fun x => x) tsepeq_of_equiv.

Definition TSepQuot : TopSpace@{o} := TQuot X tsep_setoid tsep_q.

Lemma TSepQuot_sep : TSep prem TSepQuot.
Proof using L.
  intros x y H R HR.
  apply (proj2 (proj2 (proj2 (proj2 HR)))).
  apply (tl_pull _ L P P (fun s => s) (IsOpen TSepQuot) (tsep_qopen R));
    [|exact H].
  intros U [HU HsU]. split.
  - intros t t' e u. exact (HsU t t' (e R HR) u).
  - exact HU.
Qed.

Section TMed.

Context (H : TopSpace@{o}) (HH : TSep prem H) (f : ContinuousMorphism X H).

Definition tsep_ker (a b : P) : Prop :=
  prem _ (IsOpen H) (continuous_map f a) (continuous_map f b).

Lemma tsep_ker_to (a b : P) :
  tsep_ker a b → continuous_map f a ≈ continuous_map f b.
Proof using HH. exact (HH _ _). Qed.

Lemma tsep_ker_of (a b : P) :
  continuous_map f a ≈ continuous_map f b → tsep_ker a b.
Proof using L. exact (tl_equiv _ L H _ _). Qed.

Lemma tsep_ker_TSepRel : TSepRel tsep_ker.
Proof using L HH.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intro a. apply tsep_ker_of. reflexivity.
  - intros a b e. apply tsep_ker_of. symmetry. exact (tsep_ker_to a b e).
  - intros a b c e1 e2. apply tsep_ker_of.
    transitivity (continuous_map f b);
      [exact (tsep_ker_to _ _ e1)|exact (tsep_ker_to _ _ e2)].
  - intros a b e. apply tsep_ker_of.
    exact (proper_morphism (continuous_map f) a b e).
  - intros a b Hp. unfold tsep_ker.
    apply (tl_pull _ L P _ (fun s => continuous_map f s)
             (tsep_qopen tsep_ker) (IsOpen H)); [|exact Hp].
    intros W HW. split.
    + exact (continuity f W HW).
    + intros a' b' e u.
      exact (open_proper H W HW _ _ (tsep_ker_to a' b' e) u).
Qed.

Lemma tsep_med_resp (a b : P) :
  tsepeq a b → continuous_map f a ≈ continuous_map f b.
Proof using L HH.
  intro e. exact (tsep_ker_to a b (e tsep_ker tsep_ker_TSepRel)).
Qed.

Definition tsep_med_setoid :
  @SetoidMorphism@{o o o} _ (is_setoid tsep_setoid) _
    (is_setoid (top_carrier H)) :=
  @Build_SetoidMorphism _ (is_setoid tsep_setoid) _ (is_setoid (top_carrier H))
    (fun a => continuous_map f a) tsep_med_resp.

Definition tsep_med : ContinuousMorphism TSepQuot H :=
  tquot_desc X tsep_setoid tsep_q H f tsep_med_setoid
    (fun x => reflexivity (continuous_map f x)).

End TMed.

End TQuotient.

Section TReflection.

Universes o h.
Constraint o < h.

Variable prem : TSepPremise@{o}.
Variable L : TSepLaws@{o} prem.

Definition TSepSub : Subcategory@{h h o h} Top@{h o} :=
  @Build_Subcategory@{h h o h} Top@{h o}
    (fun X => TSep prem X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TSepSpaces : Category := Sub Top@{h o} TSepSub.

Lemma TSep_Full : Construction.Subcategory.Full Top@{h o} TSepSub.
Proof. intros x y ox oy g; exact I. Qed.

Definition TSepObj (X : Top@{h o}) : TSepSpaces :=
  (TSepQuot prem X; TSepQuot_sep prem L X).

Definition tsep_proj (X : Top@{h o}) :
  X ~{Top@{h o}}~> Incl Top@{h o} TSepSub (TSepObj X) :=
  tquot_proj X (tsep_setoid prem X) (tsep_q prem X).

Definition tsep_universal (X : Top@{h o}) :
  ∀ (d : TSepSpaces) (f : X ~{Top@{h o}}~> Incl Top@{h o} TSepSub d),
    ∃! g : TSepObj X ~{TSepSpaces}~> d,
      f ≈ fmap[Incl Top@{h o} TSepSub] g ∘ tsep_proj X.
Proof using L.
  intros d f.
  unshelve eexists.
  - exact (tsep_med prem L X (`1 d) (`2 d) f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl. exact (Hg x).
Defined.

Definition tsep_ua (X : Top@{h o}) :
  @UniversalArrow Top@{h o} TSepSpaces X (Incl Top@{h o} TSepSub) :=
  @universal_arrow_from_UMP Top@{h o} TSepSpaces X (Incl Top@{h o} TSepSub)
    (TSepObj X) (tsep_proj X) (tsep_universal X).

Definition TSep_reflector : Top@{h o} ⟶ TSepSpaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl Top@{h o} TSepSub) tsep_ua.

Definition TSep_adj : TSep_reflector ⊣ Incl Top@{h o} TSepSub :=
  AdjunctionFromUniversalArrows (Incl Top@{h o} TSepSub) tsep_ua.

Definition TSep_Reflective : Reflective TSepSub :=
  @Build_Reflective Top@{h o} TSepSub TSep_Full TSep_reflector TSep_adj.

End TReflection.

(* The direct Hausdorff reflection over the Type-valued [Top]. *)
Definition TopT2_Reflective@{o h +| o < h +} :
  Reflective (TSepSub@{o h} tprem_T2@{o}) :=
  TSep_Reflective tprem_T2 tprem_T2_laws.

(* Instance/Top.v's [IsHausdorff], the classical negative form, gives this
   T2 only under a double negation. *)
Lemma IsHausdorff_TSep2_nn@{o +} (X : TopSpace@{o}) (HX : IsHausdorff X)
  (x y : X) : tprem_T2 _ (IsOpen X) x y → ¬ ¬ inhabited (x ≈ y).
Proof.
  intros Hp Hne.
  destruct (HX x y (fun e => Hne (inhabits e))) as [U [V [[HU HV] [[u v] Hd]]]].
  destruct (Hp U V HU HV u v) as [[z [a b]]].
  exact (Hd z a b).
Qed.

(** ** The adjoint functor theorem at the Type-valued inclusion *)

(*
   本节说明 TypeValued 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tophaus_bool_hausdorff@{t p q o +| p < t, q < t, p <= o, q <= o,
    o <= t +} : IsHausdorff@{t p q o} Bool_Discrete@{o}.
Proof.
  intros x y nxy.
  exists (fun z : bool => z = x). exists (fun z : bool => z = y).
  refine ((_, _), ((_, _), _)); simpl.
  - intros u v Huv Hu. simpl in Huv. congruence.
  - intros u v Huv Hu. simpl in Huv. congruence.
  - reflexivity.
  - reflexivity.
  - intros z Hx Hy. apply nxy. simpl. congruence.
Qed.

Lemma tophaus_point_hausdorff@{t p q o +| p < t, q < t, p <= o, q <= o,
    o <= t +} : IsHausdorff@{t p q o} Point_Top@{o}.
Proof. intros x y nxy. destruct x, y. destruct (nxy (reflexivity _)). Qed.

(*
   本节说明 TypeValued 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TopHaus_Bool@{c hh h t s a o p q +} :
  HausdorffSpaces@{c hh h t s a o p q} :=
  (Bool_Discrete@{o}; tophaus_bool_hausdorff@{t p q o}).

Definition TopHaus_Point@{c hh h t s a o p q +} :
  HausdorffSpaces@{c hh h t s a o p q} :=
  (Point_Top@{o}; tophaus_point_hausdorff@{t p q o}).

Definition tophaus_pt_bool@{c hh h t s a o p q +} (b : bool) :
  TopHaus_Point@{c hh h t s a o p q}
    ~{HausdorffSpaces@{c hh h t s a o p q}}~>
  TopHaus_Bool@{c hh h t s a o p q} :=
  (top_point Bool_Discrete@{o} b; I).

(* #455's arrow index of [Top], restricted to the Hausdorff spaces. *)
Definition TopHaus_ArrowIndex_of_Top@{s h o c +}
  (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (HausdorffSpaces : Category@{c h h}) :=
  @Build_ArrowIndex (HausdorffSpaces : Category@{c h h}) (ai_index AIT)
    (fun x y f => ai_enc AIT (`1 f))
    (fun x y m d => (ai_dec AIT m (`1 d); I))
    (fun x y f d => ai_dec_enc AIT (`1 f) (`1 d)).

(* Freyd's argument: a complete category with an arrow index is thin, and
   the two points of [Bool_Discrete] are two arrows out of the point. *)
Theorem TopHaus_not_complete@{r s c hh h t sh a o p q +}
  (AI : ArrowIndex@{s c hh} HausdorffSpaces@{c hh h t sh a o p q})
  (comp : @Complete@{r s hh c} HausdorffSpaces@{c hh h t sh a o p q}) :
  False.
Proof.
  exact (freyd_no_separated_pair AI (tophaus_pt_bool true)
           (tophaus_pt_bool false) _ _
           (complete_iprod comp (fun _ : ai_index AI => TopHaus_Bool))
           (fun f => continuous_map (`1 f) ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

Theorem TopHaus_not_complete_below_IEM@{e r s c h t sh a o p q +| o < h,
    o < s, h <= c +} (E : IEM@{e})
  (comp : @Complete@{r s h c} HausdorffSpaces@{c h h t sh a o p q}) :
  False.
Proof.
  exact (TopHaus_not_complete
           (TopHaus_ArrowIndex_of_Top
              (Top_ArrowIndex_transport@{s o s h}
                 (canonical_ArrowIndex
                    (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))))
           comp).
Qed.

(* [GAFT] at the Type-valued inclusion is formable ... *)
Definition GAFT_TopHaus@{h o +| o < h +}
  (comp : @Complete (Sub Top@{h o} Hausdorff_Subcategory))
  (cont : @PreservesImageLimit _ _ (Incl Top@{h o} Hausdorff_Subcategory))
  (sols : ∀ X : Top@{h o},
      SolutionSet (Incl Top@{h o} Hausdorff_Subcategory) X) :
  { H : Top@{h o} ⟶ Sub Top@{h o} Hausdorff_Subcategory &
    H ⊣ Incl Top@{h o} Hausdorff_Subcategory } :=
  GAFT (Incl Top@{h o} Hausdorff_Subcategory) comp cont sols.

(* ... and vacuous under informative excluded middle: its completeness
   premise is refuted.  The hypotheses are those of [GAFT_TopHaus] at
   every one of its universe instances. *)
Theorem GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6 +| o < h, h < u1,
    h < u6, u2 < u, u3 < u, u2 <= o, u3 <= o, o <= u, u <= u4, h <= u4,
    u0 <= h, u4 <= u6 +} (E : IEM@{e})
  (comp : @Complete@{h h h u4}
            (Sub@{h h u u0 u4 h u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3}))
  (cont : @PreservesImageLimit@{u4 h h h u6 h u1 h} _ _
            (Incl@{h h u u0 u4 u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3}))
  (sols : ∀ X : Top@{h o},
      SolutionSet@{h h u4 h}
        (Incl@{h h u u0 u4 u1} Top@{h o}
           Hausdorff_Subcategory@{h u0 o u u2 u3}) X) :
  False.
Proof.
  pose proof (GAFT_TopHaus@{h o u u0 u1 u2 u3 u4 _ u6} comp cont sols) as _.
  exact (TopHaus_not_complete_below_IEM E comp).
Qed.
