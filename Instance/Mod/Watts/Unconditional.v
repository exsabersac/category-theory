(* * * Watt's 定理 no 假设: every additive T : (R-Mod)^op ⟶ Ab
 carrying colimits limits Hom(−, A) （已译） *)

(*
 Book:      Mac Lane, ibid., §V.6 Theorem 3 and Definition 3 — the
 nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab:      https://ncatlab.org/nlab/show/representable+functor

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.AbCategory.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Functor.Representable.Additive.

Generalizable All Variables.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive MSObj@{u} (X : Type@{u}) : Type@{u} :=
  | ms_mod
  | ms_free
  | ms_gen (m : X).

Arguments ms_mod {X}.
Arguments ms_free {X}.
Arguments ms_gen {X} m.

Definition MSHom@{u} {X : Type@{u}} (i j : MSObj@{u} X) : Type@{u} :=
  match i, j with
  | ms_mod, ms_mod => poly_unit@{u}
  | ms_free, ms_free => poly_unit@{u}
  | ms_gen m, ms_gen m' => m = m'
  | ms_gen _, ms_mod => poly_unit@{u}
  | ms_gen _, ms_free => poly_unit@{u}
  | _, _ => False
  end.

Definition ms_id@{u} {X : Type@{u}} (i : MSObj@{u} X) : MSHom i i.
Proof. destruct i; simpl; first [ exact ttt | reflexivity ]. Defined.

Definition ms_comp@{u} {X : Type@{u}} {i j k : MSObj@{u} X} :
  MSHom j k → MSHom i j → MSHom i k.
Proof.
  destruct i, j, k; simpl; intros g f;
    first [ exact ttt | contradiction | exact (eq_trans f g) ].
Defined.

#[local] Obligation Tactic := idtac.

Program Definition MultiSpan@{u} (X : Type@{u}) : Category@{u u u} := {|
  obj := MSObj@{u} X;
  hom := @MSHom@{u} X;
  homset := fun i j => {| equiv := fun _ _ => True |};
  id := @ms_id@{u} X;
  compose := fun i j k => @ms_comp@{u} X i j k
|}.
Solve All Obligations with
  (intros;
   first [ constructor; repeat intro; exact I | repeat intro; exact I ]).

(* 相关说明。 （已译） *)
Section MSDiagram.

Universes o h.

Context {X : Type@{h}} {C : Category@{o h h}} (A B G : C)
        (u : X → G ~{C}~> A) (v : X → G ~{C}~> B).

Definition ms_fobj (i : MSObj@{h} X) : C :=
  match i with ms_mod => A | ms_free => B | ms_gen _ => G end.

Definition ms_fmap {i j : MSObj@{h} X} :
  MSHom i j → ms_fobj i ~{C}~> ms_fobj j.
Proof using u v.
  destruct i as [| | m], j as [| | m']; simpl; intro f;
    first [ exact id | contradiction | exact (u m) | exact (v m) ].
Defined.

Program Definition ms_diagram : MultiSpan@{h} X ⟶ C := {|
  fobj := ms_fobj;
  fmap := fun i j f => ms_fmap f
|}.
Next Obligation.
  intros i j f g _.
  destruct i as [| | m], j as [| | m']; simpl in *;
    first [ contradiction | reflexivity ].
Qed.
Next Obligation.
  intro i; destruct i; simpl; reflexivity.
Qed.
Next Obligation.
  intros i j k f g.
  destruct i as [| | m], j as [| | m'], k as [| | m'']; simpl in *;
    try contradiction; solve [ subst; cat ].
Qed.

End MSDiagram.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sets_limit_point@{j c s +}
  {J : Category@{j c c}} {F : J ⟶ Sets@{c s}} (N : Cone F) (HN : IsLimitCone N)
  (e : ∀ i : J, carrier (F i))
  (He : ∀ (i i' : J) (f : i ~{J}~> i'), fmap[F] f (e i) ≈ e i') :
  { v : carrier (vertex_obj[N]) & ∀ i : J, cone_leg N i v ≈ e i }.
Proof.
  unshelve epose (P := @Build_Cone J Sets F unit_setoid_object
           (@Build_ACone J Sets unit_setoid_object F
              (fun i => {| morphism := fun _ => e i |}) _)).
  - intros w w' _; reflexivity.
  - intros i i' f w; simpl; exact (He i i' f).
  - destruct (HN P) as [w Hw _].
    exists (w ttt).
    intro i; exact (Hw i ttt).
Defined.

(* 相关说明。 （已译） *)

Definition ew_Gen@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} : obj[RMod@{o x a p c} R] :=
  @FreeModObject R unit_setoid_object@{c c}.

Definition ew_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} : carrier (cmon_setoid (@ew_Gen@{a c p o x} R)) :=
  @fv_gen R unit_setoid_object@{c c} ttt.

(* 相关说明。 （已译） *)
Definition ew_ev@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  @ew_Gen@{a c p o x} R ~{RMod@{o x a p c} R}~> M.
Proof.
  refine (@fv_extend R unit_setoid_object@{c c} M
            {| morphism := fun _ => m |}).
  intros ? ? ?; reflexivity.
Defined.

Example ew_ev_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_ev@{a c p o x} m)) ew_g0 = m := eq_refl.

(* 相关说明。 （已译） *)

Section Covering.

(*
   本节说明 Unconditional 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes a c p o x s w w0 w1.
Constraint Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, c < w,
  o <= w1, x <= w1.

Context {R : RingObject@{a c p}}.
Context (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}).
Context (contK : ContinuousFunctor K).

#[local] Notation Gen := (@ew_Gen@{a c p o x} R).
#[local] Notation g0 := (@ew_g0@{a c p o x} R).

(* The ONE fixed 对象: coproduct copies [Gen], one per element
 [K Gen], taken [RMod_Cocomplete_via_GAFT]. （已译） *)
Definition ew_Idx : Type@{c} := carrier (K Gen).

Definition ew_CopD : DiscreteCat@{c c c} ew_Idx ⟶ RMod@{o x a p c} R :=
  DiscreteCat_Functor@{c c c o c c w} (fun _ => Gen).

Definition ew_CC : @Cocomplete@{c c c o} (RMod@{o x a p c} R) :=
  RMod_Cocomplete_via_GAFT@{a c p o x c w0 w1} R.

Definition ew_CopL : Colimit ew_CopD := ew_CC _ ew_CopD.

Definition ew_Cop : obj[RMod@{o x a p c} R] :=
  vertex_obj[@limit_cone _ _ _ ew_CopL].

Definition ew_inj (i : ew_Idx) : Gen ~{RMod@{o x a p c} R}~> ew_Cop :=
  cone_leg (@limit_cone _ _ _ ew_CopL) i.

(* 相关说明。 （已译） *)
Definition ew_y0_ex :
  { w : carrier (K ew_Cop)
  & ∀ i : ew_Idx, @fmap _ _ K ew_Cop Gen (ew_inj i) w ≈ i }.
Proof using contK.
  destruct (sets_limit_point (FCone K (@limit_cone _ _ _ ew_CopL))
              (contK _ _ (@limit_cone _ _ _ ew_CopL) (limit_limitcone ew_CopL))
              (fun i : ew_Idx => i)) as [w Hw].
  - intros i i' f; destruct f; simpl.
    exact (@fmap_id _ _ K Gen _).
  - exists w; exact Hw.
Defined.

Definition ew_y0 : carrier (K ew_Cop) := projT1 ew_y0_ex.

Definition ew_y0_leg (i : ew_Idx) :
  @fmap _ _ K ew_Cop Gen (ew_inj i) ew_y0 ≈ i :=
  projT2 ew_y0_ex i.

Section AtElement.

Context (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M)).

(* 相关说明。 （已译） *)
Definition ew_am (m : carrier (cmon_setoid M)) : ew_Idx :=
  @fmap _ _ K M Gen (ew_ev m) x0.

(* 相关说明。 （已译） *)
Definition ew_PD :
  MultiSpan@{c} (carrier (cmon_setoid M)) ⟶ RMod@{o x a p c} R :=
  ms_diagram@{o c w} M ew_Cop Gen
    (fun m => ew_ev m) (fun m => ew_inj (ew_am m)).

Definition ew_PL : Colimit ew_PD := ew_CC _ ew_PD.

Definition ew_P : obj[RMod@{o x a p c} R] :=
  vertex_obj[@limit_cone _ _ _ ew_PL].

Definition ew_pM : M ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) ms_mod.

Definition ew_pF : ew_Cop ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) ms_free.

Definition ew_pG (m : carrier (cmon_setoid M)) :
  Gen ~{RMod@{o x a p c} R}~> ew_P :=
  cone_leg (@limit_cone _ _ _ ew_PL) (ms_gen m).

Lemma ew_pM_ev (m : carrier (cmon_setoid M)) : ew_pM ∘ ew_ev m ≈ ew_pG m.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ ew_PL))
           ms_mod (ms_gen m) ttt).
Qed.

Lemma ew_pF_inj (m : carrier (cmon_setoid M)) :
  ew_pF ∘ ew_inj (ew_am m) ≈ ew_pG m.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ (@limit_cone _ _ _ ew_PL))
           ms_free (ms_gen m) ttt).
Qed.

(* 相关说明。 （已译） *)
Lemma ew_key (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom ew_pF) (cmon_map (rm_hom (ew_inj (ew_am m))) g0)
    ≈ cmon_map (rm_hom ew_pM) m.
Proof.
  pose proof (ew_pF_inj m g0) as H1; pose proof (ew_pM_ev m g0) as H2.
  simpl in H1, H2.
  exact (Equivalence_Transitive _ _ _ H1 (Equivalence_Symmetric _ _ H2)).
Qed.

(* 相关说明。 （已译） *)
Definition ew_efam (i : MultiSpan@{c} (carrier (cmon_setoid M))) :
  carrier ((K ◯ ew_PD^op) i).
Proof using contK.
  destruct i as [| | m]; [ exact x0 | exact ew_y0 | exact (ew_am m) ].
Defined.

Definition ew_e_ex :
  { w : carrier (K ew_P)
  & ∀ i, cone_leg (FCone K (@limit_cone _ _ _ ew_PL)) i w ≈ ew_efam i }.
Proof using contK.
  refine (sets_limit_point (FCone K (@limit_cone _ _ _ ew_PL))
            (contK _ _ (@limit_cone _ _ _ ew_PL) (limit_limitcone ew_PL))
            ew_efam _).
  intros i i' f.
  destruct i as [| | m], i' as [| | m']; simpl in f |- *;
    try contradiction;
    first [ exact (@fmap_id _ _ K _ _)
          | reflexivity
          | exact (ew_y0_leg _)
          | (subst; exact (@fmap_id _ _ K _ _)) ].
Defined.

Definition ew_e : carrier (K ew_P) := projT1 ew_e_ex.

Lemma ew_e_leg : @fmap _ _ K ew_P M ew_pM ew_e ≈ x0.
Proof using contK. exact (projT2 ew_e_ex ms_mod). Qed.

(* 相关说明。 （已译） *)
Definition ew_N : PSubmodule ew_Cop := pker ew_pF.

Definition ew_Q : obj[RMod@{o x a p c} R] := QuotientMod (psm_sub ew_N).

Definition ew_k : ew_Q ~{RMod@{o x a p c} R}~> ew_P.
Proof.
  refine (mquot_med (psm_sub ew_N) (existT _ ew_pF _)).
  intros z Hz; exact (pequiv_to _ _ Hz).
Defined.

Lemma ew_qrel_of (z z' : carrier (cmon_setoid ew_Cop)) :
  cmon_map (rm_hom ew_pF) z ≈ cmon_map (rm_hom ew_pF) z' →
  mquot_rel (psm_sub ew_N) z z'.
Proof.
  intro H; constructor; simpl.
  apply pequiv_from.
  rewrite (ab_map_sub (rm_hom ew_pF) z z').
  apply (snd (ab_sub_eq_zero_iff _ _ _)); exact H.
Qed.

(* 相关说明。 （已译） *)
Definition ew_tfun (m : carrier (cmon_setoid M)) :
  carrier (cmon_setoid ew_Cop) :=
  cmon_map (rm_hom (ew_inj (ew_am m))) g0.

Definition ew_t : M ~{RMod@{o x a p c} R}~> ew_Q.
Proof.
  unshelve econstructor; [unshelve econstructor; [unshelve econstructor|..]|].
  - exact ew_tfun.
  - intros m m' Hm; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key m), (ew_key m'); now rewrite Hm.
  - apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (cmon_zero M)).
    rewrite (cmon_map_zero (rm_hom ew_pM)).
    symmetry; exact (cmon_map_zero (rm_hom ew_pF)).
  - intros m m'; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (cmon_plus M m m')).
    rewrite (cmon_map_plus (rm_hom ew_pF)).
    rewrite (ew_key m), (ew_key m').
    exact (cmon_map_plus (rm_hom ew_pM) m m').
  - intros r m; apply ew_qrel_of; unfold ew_tfun.
    rewrite (ew_key (rm_smul M r m)).
    rewrite (rm_map_smul ew_pF).
    rewrite (ew_key m).
    exact (rm_map_smul ew_pM r m).
Defined.

Example ew_t_at (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom ew_t) m = cmon_map (rm_hom (ew_inj (ew_am m))) g0 := eq_refl.

Lemma ew_k_t : ew_k ∘ ew_t ≈ ew_pM.
Proof. intro m; simpl; exact (ew_key m). Qed.

Definition ew_eQ : carrier (K ew_Q) := @fmap _ _ K ew_P ew_Q ew_k ew_e.

Lemma ew_t_covers : @fmap _ _ K ew_Q M ew_t ew_eQ ≈ x0.
Proof using contK.
  unfold ew_eQ.
  pose proof (@fmap_comp _ _ K ew_P ew_Q M ew_t ew_k ew_e) as Hc; simpl in Hc.
  pose proof (@fmap_respects _ _ K ew_P M (ew_k ∘ ew_t) ew_pM ew_k_t ew_e)
    as Hr;
    simpl in Hr.
  rewrite <- ew_e_leg.
  exact (Equivalence_Transitive _ _ _ (Equivalence_Symmetric _ _ Hc) Hr).
Qed.

End AtElement.

(* 相关说明。 （已译） *)
Definition ew_WIdx : Type@{c} :=
  { N : PSubmodule ew_Cop & carrier (K (QuotientMod (psm_sub N))) }.

Definition RModop_esols : ElementSolutionSet K.
Proof using contK.
  refine (@Build_ElementSolutionSet ((RMod@{o x a p c} R)^op) K ew_WIdx
            (fun i => QuotientMod (psm_sub (projT1 i))) (fun i => projT2 i) _).
  intros M x.
  exists (existT (fun N : PSubmodule ew_Cop =>
                    carrier (K (QuotientMod (psm_sub N))))
            (ew_N M x) (ew_eQ M x)).
  exists (ew_t M x).
  exact (ew_t_covers M x).
Defined.

End Covering.

(* 相关说明。 （已译） *)

Definition RModop_continuous_representable@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (contK : ContinuousFunctor K) : Representable K :=
  representability_theorem K
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit contK) (RModop_esols K contK).

(* * ** 6. Watt's 定理, contravariant form, no 假设 （已译） *)

Definition watts_theorem_unconditional@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun ((RMod@{o x a p c} R)^op) Ab@{b c})
      (@CoHomAb _ (RMod_LocallyPropositional R) (RMod_AbEnriched R) A) T }.
Proof.
  pose (Rp := RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                (continuous_compose contT Ab_Forget_creates_continuous)).
  exists (wab_obj Rp).
  exact (@watt_ab_iso _ (LocallyPropositional_op (RMod_LocallyPropositional R))
           (AbEnriched_op (RMod_AbEnriched R)) T AF Rp).
Defined.

(* The 表示 module IS 对象 representability 定理
 produces [Ab_Forget ◯ T]. （已译） *)
Example watts_theorem_unconditional_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = wab_obj (RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                 (continuous_compose contT Ab_Forget_creates_continuous))
  := eq_refl.

(** ** 7. Non-vacuity *)

(* Every module A gives instance 定理, through
 Functor/Representable/Additive.v's [CoHomAb_continuous], the
 module 定理 returns isomorphic A. （已译） *)
Definition watts_unconditional_CoHomAb_obj@{a c p o x b +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, Set < b, c < b +}
  {R : RingObject@{a c p}} (A : RMod@{o x a p c} R) :
  projT1 (watts_theorem_unconditional
            (@CoHomAb _ (RMod_LocallyPropositional R) (RMod_AbEnriched R) A
             : _ ⟶ Ab@{b c})
            (@HomAb_additive _
               (LocallyPropositional_op (RMod_LocallyPropositional R))
               (AbEnriched_op (RMod_AbEnriched R)) A)
            (CoHomAb_continuous (RMod_AbEnriched R) A))
    ≅[(RMod@{o x a p c} R)^op] A :=
  repr_unique_iso
    (@HomAb_representable _
       (LocallyPropositional_op (RMod_LocallyPropositional R))
       (AbEnriched_op (RMod_AbEnriched R)) A)
    (RModop_continuous_representable _
       (continuous_compose (CoHomAb_continuous (RMod_AbEnriched R) A)
          Ab_Forget_creates_continuous)).

(* The set-valued form at plain hom-函子. （已译） *)
Definition RModop_hom_representable_obj@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (A : RMod@{o x a p c} R) :
  @repr_obj _ _ (RModop_continuous_representable
                   (@HomFrom_at ((RMod@{o x a p c} R)^op) A : _ ⟶ Sets@{c s})
                   (@hom_continuous_at ((RMod@{o x a p c} R)^op) A))
    ≅[(RMod@{o x a p c} R)^op] A :=
  repr_unique_iso (@Hom_Representable ((RMod@{o x a p c} R)^op) A)
    (RModop_continuous_representable _
       (@hom_continuous_at ((RMod@{o x a p c} R)^op) A)).

(* At a concrete ring: ℤ, with its three universes apart. *)
Definition watts_unconditional_at_Z@{a c p o x b +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, Set < b, c < b +}
  (A : RMod@{o x a p c} Int_Ring@{c p a}) :
  projT1 (watts_theorem_unconditional
            (@CoHomAb _ (RMod_LocallyPropositional _) (RMod_AbEnriched _) A
             : _ ⟶ Ab@{b c})
            (@HomAb_additive _
               (LocallyPropositional_op (RMod_LocallyPropositional _))
               (AbEnriched_op (RMod_AbEnriched _)) A)
            (CoHomAb_continuous (RMod_AbEnriched _) A))
    ≅[(RMod@{o x a p c} Int_Ring@{c p a})^op] A :=
  watts_unconditional_CoHomAb_obj A.
