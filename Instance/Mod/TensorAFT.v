Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Resize.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
 nLab:      https://ncatlab.org/nlab/show/representable+functor
 nLab:      https://ncatlab.org/nlab/show/solution+set+condition
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section SetsLimitElements.

Context {J : Category}.
Context {G : J ⟶ Sets}.
Context {N : Cone G}.
Context (HN : IsLimitCone N).

(* A compatible family of elements is a cone out of the singleton. *)
Definition slim_family_cone (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) : Cone G :=
  @Build_Cone J Sets G SetsOne
    (@Build_ACone J Sets SetsOne G (fun x => global_element (b x))
       (fun x y f _ => Hb x y f)).

Definition slim_elem (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) :
  carrier (vertex_obj[N]) :=
  unique_obj (HN (slim_family_cone b Hb)) ttt.

Lemma slim_elem_leg (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) (x : J) :
  cone_leg N x (slim_elem b Hb) ≈ b x.
Proof using All.
  exact (unique_property (HN (slim_family_cone b Hb)) x ttt).
Qed.

Lemma slim_ext (u v : carrier (vertex_obj[N]))
  (H : ∀ x : J, cone_leg N x u ≈ cone_leg N x v) : u ≈ v.
Proof using All. exact (absets_limit_ext (limitcone_isalimit HN) u v H). Qed.

End SetsLimitElements.

(* 相关说明。 （已译） *)

Section DirectSolutionSet.

Context {R : RingObject}.
Context (V V' : RModObject R).

(* 相关说明。 （已译） *)
Lemma rbl_corestrict_spanning {W : RModObject R} (β : RBilinear V V' W) :
  RBilinearSpanning (rbl_gen_corestrict β).
Proof using.
  intros [a D].
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|r a D IH].
  - refine (mgen_base (rbl_image (rbl_gen_corestrict β)) _ _).
    destruct Ha as [v [w Hvw]].
    exists v, w; exact Hvw.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _ IH).
    exact Hab.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_zero (rbl_image (rbl_gen_corestrict β)))).
    reflexivity.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_plus (rbl_image (rbl_gen_corestrict β)) _ _ IH1 IH2)).
    reflexivity.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_smul (rbl_image (rbl_gen_corestrict β)) r _ IH)).
    reflexivity.
Defined.

Definition tensor_esols_direct : ElementSolutionSet (Bilin V V').
Proof using.
  unshelve refine
    {| esol_index := SpanningArrowsOutOf (Bilin V V') SetsOne
     ; esol_obj := fun i => `1 i
     ; esol_elem := fun i => `1 (`2 i) ttt |}.
  intros c β.
  unshelve eexists.
  - refine (existT _ (SubmoduleMod (SubGenMod (rbl_image β))) _).
    refine (existT _ (global_element
                        (X := Bilin V V' (SubmoduleMod
                                (SubGenMod (rbl_image β))))
                        (rbl_gen_corestrict β)) _).
    exact (rbilinear_spanning_to_spanning (rbl_gen_corestrict β)
             (rbl_corestrict_spanning β)).
  - exists (smod_incl (SubGenMod (rbl_image β))).
    intros v w; reflexivity.
Defined.

Example tensor_esols_direct_index :
  esol_index tensor_esols_direct = SpanningArrowsOutOf (Bilin V V') SetsOne
  := eq_refl.

Example tensor_esols_direct_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj tensor_esols_direct i = `1 i := eq_refl.

Example tensor_esols_direct_elem
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem tensor_esols_direct i = `1 (`2 i) ttt := eq_refl.

(* 相关说明。 （已译） *)
Example tensor_esols_same_index
  (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP) = esol_index tensor_esols_direct
  := eq_refl.

End DirectSolutionSet.

(** ** 3. [Bilin V V'] is continuous *)

Section BilinContinuity.

Context {R : RingObject}.
Context (V V' : RModObject R).

Section AtALimitingCone.

Context {J : Category}.
Context {K : J ⟶ RMod R}.
Context {N : Cone K}.
Context (HN : IsLimitCone N).

(* 相关说明。 （已译） *)
Definition bilin_sets_limit : IsLimitCone (FCone (RMod_Forget R) N) :=
  RMod_Forget_creates_continuous R J K N HN.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma bilin_lim_ext (u v : carrier (cmon_setoid vertex_obj[N]))
  (H : ∀ x : J, cmon_map (rm_hom (cone_leg N x)) u
                  ≈ cmon_map (rm_hom (cone_leg N x)) v) : u ≈ v.
Proof using All. exact (slim_ext bilin_sets_limit u v H). Qed.

Section AtACone.

Context (Q : Cone (Bilin V V' ◯ K)).

Lemma bilin_family_compat (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V'))
  (x y : J) (f : x ~{J}~> y) :
  fmap[RMod_Forget R ◯ K] f (rbl_map (cone_leg Q x q) v w)
    ≈ rbl_map (cone_leg Q y q) v w.
Proof using All.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ Q) x y f q v w).
Qed.

Definition bilin_med_elem (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  carrier (cmon_setoid vertex_obj[N]) :=
  slim_elem bilin_sets_limit (fun x => rbl_map (cone_leg Q x q) v w)
    (fun x y f => bilin_family_compat q v w x y f).

Lemma bilin_med_elem_leg (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) (x : J) :
  cmon_map (rm_hom (cone_leg N x)) (bilin_med_elem q v w)
    ≈ rbl_map (cone_leg Q x q) v w.
Proof using All.
  exact (slim_elem_leg bilin_sets_limit
           (fun x => rbl_map (cone_leg Q x q) v w)
           (fun x y f => bilin_family_compat q v w x y f) x).
Qed.

Program Definition Bilin_med (q : carrier (vertex_obj[Q])) :
  RBilinear V V' vertex_obj[N] := {|
  rbl_map := bilin_med_elem q
|}.
Next Obligation.
  intros q v v' Hv w w' Hw.
  apply bilin_lim_ext; intro x.
  rewrite !bilin_med_elem_leg.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros q v v' w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (cmon_map_plus (rm_hom (cone_leg N x))).
  rewrite !bilin_med_elem_leg.
  apply rbl_add_l.
Qed.
Next Obligation.
  intros q v w w'.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (cmon_map_plus (rm_hom (cone_leg N x))).
  rewrite !bilin_med_elem_leg.
  apply rbl_add_r.
Qed.
Next Obligation.
  intros q r v w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (rm_map_smul (cone_leg N x)).
  rewrite !bilin_med_elem_leg.
  apply rbl_smul_l.
Qed.
Next Obligation.
  intros q r v w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (rm_map_smul (cone_leg N x)).
  rewrite !bilin_med_elem_leg.
  apply rbl_smul_r.
Qed.

Program Definition Bilin_cone_med :
  vertex_obj[Q] ~{Sets}~> vertex_obj[FCone (Bilin V V') N] :=
  {| morphism := Bilin_med |}.
Next Obligation.
  intros q q' Hq v w.
  change (bilin_med_elem q v w ≈ bilin_med_elem q' v w).
  apply bilin_lim_ext; intro x.
  rewrite !bilin_med_elem_leg.
  exact (proper_morphism (cone_leg Q x) q q' Hq v w).
Qed.

End AtACone.

Theorem Bilin_preserves_cone : IsLimitCone (FCone (Bilin V V') N).
Proof using All.
  intro Q.
  unshelve refine {| unique_obj := Bilin_cone_med Q |}.
  - intros x q v w.
    exact (bilin_med_elem_leg Q q v w x).
  - intros u Hu q v w.
    apply bilin_lim_ext; intro x.
    rewrite (bilin_med_elem_leg Q q v w x).
    symmetry; exact (Hu x q v w).
Qed.

End AtALimitingCone.

Definition Bilin_continuous : ContinuousFunctor (Bilin V V') :=
  fun J K N HN => Bilin_preserves_cone HN.

Definition Bilin_PreservesImageLimit :
  @PreservesImageLimit (RMod R) Sets (Bilin V V') :=
  Continuous_PreservesImageLimit Bilin_continuous.

End BilinContinuity.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CongruenceIndex.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record IsCongruence (Rq : MTerm V V' → MTerm V V' → Prop) : Prop := {
  cg_refl  : ∀ s, Rq s s;
  cg_sym   : ∀ s t, Rq s t → Rq t s;
  cg_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  cg_gen   : ∀ s t, mt_eq s t → Rq s t;
  cg_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (mt_plus s t) (mt_plus s' t');
  cg_neg   : ∀ s s', Rq s s' → Rq (mt_neg s) (mt_neg s');
  cg_smul  : ∀ (r : carrier (rig_setoid (ring_rig R))) s s',
               Rq s s' → Rq (mt_smul r s) (mt_smul r s')
}.

Definition CongIdx : Type :=
  { Rq : MTerm V V' → MTerm V V' → Prop & IsCongruence Rq }.

End CongruenceIndex.

Arguments IsCongruence {R} V V' Rq.
Arguments CongIdx {R} V V'.

Section QuotientModule.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

Lemma QMod_smul_respects (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) :
  Proper (equiv ==> Rq ==> Rq) (@mt_smul R V V').
Proof.
  intros r r' Hr s s' Hs.
  refine (cg_trans _ _ Rq HRq _ (@mt_smul R V V' r s') _ _ _).
  - exact (cg_smul _ _ Rq HRq r _ _ Hs).
  - exact (cg_gen _ _ Rq HRq _ _ (mte_smul Hr (mt_refl s'))).
Qed.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QMod_Setoid (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : Setoid (MTerm V V') :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := cg_refl  _ _ Rq HRq
        ; Equivalence_Symmetric  := cg_sym   _ _ Rq HRq
        ; Equivalence_Transitive := cg_trans _ _ Rq HRq |} |}.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QMod (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : obj[RMod R] :=
  {| rm_ab := {|
       ab_cmon := {|
         cmon_setoid :=
           {| carrier := MTerm V V'
            ; is_setoid := QMod_Setoid Rq HRq |};
         cmon_zero := @mt_zero R V V';
         cmon_plus := @mt_plus R V V';
         cmon_plus_respects := fun _ _ Hs _ _ Ht => cg_plus _ _ Rq HRq _ _ _ _ Hs Ht;
         cmon_plus_assoc := fun s t u => cg_gen _ _ Rq HRq _ _ (mte_assoc s t u);
         cmon_plus_comm  := fun s t => cg_gen _ _ Rq HRq _ _ (mte_comm s t);
         cmon_plus_zero_l := fun s => cg_gen _ _ Rq HRq _ _ (mte_zero_l s);
         cmon_prop := @PropEquiv_of_relation _ (QMod_Setoid Rq HRq) Rq
                        (fun _ _ h => h) (fun _ _ h => h)
       |};
       ab_neg := @mt_neg R V V';
       ab_neg_respects := fun _ _ Hs => cg_neg _ _ Rq HRq _ _ Hs;
       ab_neg_left := fun s => cg_gen _ _ Rq HRq _ _ (mte_neg_l s)
     |};
     rm_smul := @mt_smul R V V';
     rm_smul_respects := QMod_smul_respects Rq HRq;
     rm_smul_distr_l := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_distr_l r s t);
     rm_smul_distr_r := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_distr_r r s t);
     rm_smul_assoc := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_assoc r s t);
     rm_smul_one := fun s => cg_gen _ _ Rq HRq _ _ (mte_smul_one s)
  |}.

(* The canonical bilinear map 进入 quotient generator former. （已译） *)
Definition QMod_gen (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : RBilinear V V' (QMod Rq HRq) :=
  @Build_RBilinear R V V' (QMod Rq HRq) (@mt_gen R V V')
    (fun _ _ Hv _ _ Hw => cg_gen _ _ Rq HRq _ _ (mte_gen Hv Hw))
    (fun v v' w => cg_gen _ _ Rq HRq _ _ (mte_add_l v v' w))
    (fun v w w' => cg_gen _ _ Rq HRq _ _ (mte_add_r v w w'))
    (fun r v w => cg_gen _ _ Rq HRq _ _ (mte_sym (mte_act_l r v w)))
    (fun r v w => cg_gen _ _ Rq HRq _ _ (mte_sym (mte_act_r r v w))).

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem QMod_gen_spanning (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : RBilinearSpanning (QMod_gen Rq HRq).
Proof.
  intro t; induction t.
  - refine (mgen_base (rbl_image (QMod_gen Rq HRq)) _ _).
    exists c, c0; reflexivity.
  - exact (mgen_zero (rbl_image (QMod_gen Rq HRq))).
  - exact (mgen_plus (rbl_image (QMod_gen Rq HRq)) _ _ IHt1 IHt2).
  - exact (smod_neg (SubGenMod (rbl_image (QMod_gen Rq HRq))) _ IHt).
  - exact (mgen_smul (rbl_image (QMod_gen Rq HRq)) _ _ IHt).
Defined.

End QuotientModule.

Arguments QMod {R V V'} Rq HRq.
Arguments QMod_gen {R V V'} Rq HRq.
Arguments QMod_gen_spanning {R V V'} Rq HRq.

(*
   本节说明核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KernelCongruence.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).
Context {W : obj[RMod R]}.
Context (beta : RBilinear V V' W).

Definition ker_cong : MTerm V V' → MTerm V V' → Prop :=
  fun x y => @pequiv _ _ (cmon_prop W)
               (tensor_med_fun beta x) (tensor_med_fun beta y).

Lemma ker_cong_is_cong : IsCongruence V V' ker_cong.
Proof.
  unfold ker_cong.
  constructor.
  - intro s; apply (@pequiv_from _ _ (cmon_prop W)); reflexivity.
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop W)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop W) _ _ H).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop W)).
    transitivity (tensor_med_fun beta t);
      [ exact (@pequiv_to _ _ (cmon_prop W) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop W) _ _ H2) ].
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop W));
      exact (tensor_med_respects beta s t H).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (cmon_plus_respects W _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H2)).
  - intros s s' H; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (ab_neg_respects W _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H)).
  - intros r s s' H; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (rm_smul_respects W _ _ (reflexivity r) _ _
             (@pequiv_to _ _ (cmon_prop W) _ _ H)).
Qed.

Definition ker_idx : CongIdx V V' := existT _ ker_cong ker_cong_is_cong.

(* 相关说明。 （已译） *)
Program Definition ker_med : QMod ker_cong ker_cong_is_cong ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := tensor_med_fun beta |} |}
|}.
Solve All Obligations with
  (first [ (intros s t H; exact (@pequiv_to _ _ (cmon_prop W) _ _ H))
         | (intros; simpl; reflexivity) ]).

(* 相关说明。 （已译） *)
Example ker_factors (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom ker_med)
    (rbl_map (QMod_gen ker_cong ker_cong_is_cong) v w)
  = rbl_map beta v w
  := eq_refl.

(* 相关说明。 （已译） *)
Lemma ker_med_injective : RModInjective ker_med.
Proof.
  intros x y H; exact (@pequiv_from _ _ (cmon_prop W) _ _ H).
Qed.

(* 相关说明。 （已译） *)
Definition mgen_preimage (a : carrier (cmon_setoid W))
  (D : MGen (rbl_image beta) a)
  : { t : MTerm V V' & tensor_med_fun beta t ≈ a }.
Proof.
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|r a D IH].
  - exact (existT _ (@mt_gen R V V' (`1 Ha) (`1 (`2 Ha))) (`2 (`2 Ha))).
  - exact (existT _ (`1 IH) (transitivity (`2 IH) Hab)).
  - refine (existT _ (@mt_zero R V V') _); simpl; reflexivity.
  - exact (existT _ (@mt_plus R V V' (`1 IH1) (`1 IH2))
             (cmon_plus_respects W _ _ (`2 IH1) _ _ (`2 IH2))).
  - exact (existT _ (@mt_smul R V V' r (`1 IH))
             (rm_smul_respects W _ _ (reflexivity r) _ _ (`2 IH))).
Defined.

Lemma ker_med_surjective (Hsp : RBilinearSpanning beta) :
  RModSurjective ker_med.
Proof.
  intro b; exact (mgen_preimage b (Hsp b)).
Defined.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ker_iso (Hsp : RBilinearSpanning beta) :
  QMod ker_cong ker_cong_is_cong ≅ W.
Proof.
  unshelve refine {| to := ker_med
                   ; from := rmod_split ker_med ker_med_injective
                               (ker_med_surjective Hsp) |}.
  - exact (rmod_split_commutes ker_med ker_med_injective
             (ker_med_surjective Hsp)).
  - intro t; simpl.
    apply ker_med_injective.
    exact (`2 (ker_med_surjective Hsp (tensor_med_fun beta t))).
Defined.

End KernelCongruence.

Arguments ker_cong {R V V' W} beta.
Arguments ker_cong_is_cong {R V V' W} beta.
Arguments ker_idx {R V V' W} beta.
Arguments ker_med {R V V' W} beta.
Arguments ker_iso {R V V' W} beta Hsp.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QModOf {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : obj[RMod R] := QMod (`1 i) (`2 i).

Definition QModGenOf {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : RBilinear V V' (QModOf i) := QMod_gen (`1 i) (`2 i).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_esols_prop {R : RingObject} (V V' : obj[RMod R]) :
  ElementSolutionSet (Bilin V V').
Proof.
  unshelve refine (@Build_ElementSolutionSet (RMod R) (Bilin V V')
                     (CongIdx V V') QModOf QModGenOf _).
  intros c beta.
  exists (ker_idx beta), (ker_med beta).
  intros v w; simpl; reflexivity.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition tensor_via_AFT_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) : Representable (Bilin V V') :=
  representability_theorem (Bilin V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V') E.

(* THE HEADLINE, at ARBITRARY ring, no 假设 no [Set]. （已译） *)
Definition tensor_via_AFT {R : RingObject} (V V' : obj[RMod R]) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_prop V V').

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_esols_from_tensor {R : RingObject} (V V' : RModObject R) :
  ElementSolutionSet (Bilin V V').
Proof.
  unshelve refine (@Build_ElementSolutionSet (RMod R) (Bilin V V')
                     unit (fun _ => TensorMod V V')
                     (fun _ => @tensor_gen R V V') _).
  intros c β.
  refine (existT _ tt _).
  refine (existT _ (tensor_factor β) _).
  intros v w; exact (tensor_factor_commutes β v w).
Defined.

Definition tensor_via_AFT_from_tensor {R : RingObject} (V V' : RModObject R) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_from_tensor V V').

(* 相关说明。 （已译） *)

Definition tensor_repr_of_UE {R : RingObject} (V V' : RModObject R) :
  Representable (Bilin V V') :=
  Representable_of_UniversalElement (tensor_UniversalElement V V').

Example tensor_repr_of_UE_obj {R : RingObject} (V V' : RModObject R) :
  @repr_obj (RMod R) (Bilin V V') (tensor_repr_of_UE V V') = TensorMod V V'
  := eq_refl.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tensor_AFT_iso_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT_of_esols V V' E)
    ≅ TensorMod V V' :=
  repr_unique_iso (tensor_repr_of_UE V V')
    (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_iso {R : RingObject} (V V' : obj[RMod R]) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT V V')
    ≅ TensorMod V V' :=
  tensor_AFT_iso_of_esols V V' (tensor_esols_prop V V').

Definition tensor_AFT_iso_universal_of_esols {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :=
  repr_unique_iso_universal (tensor_repr_of_UE V V')
    (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_iso_universal {R : RingObject} (V V' : obj[RMod R]) :=
  tensor_AFT_iso_universal_of_esols V V' (tensor_esols_prop V V').

Definition tensor_AFT_ue_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) : UniversalElement (Bilin V V') :=
  UniversalElement_of_Representable (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_ue {R : RingObject} (V V' : obj[RMod R]) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue_of_esols V V' (tensor_esols_prop V V').

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition module_tensor_universal_of_esols {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue_of_esols V V' E.

Definition module_tensor_universal {R : RingObject} (V V' : obj[RMod R]) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue V V'.

Definition tensor_AFT_elem_iso {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  @ue_obj (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E) ≅ TensorMod V V' :=
  universal_element_iso
    (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
    (tensor_universal_element V V').

Theorem tensor_AFT_elem_commutes {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  fmap[Bilin V V'] (to (tensor_AFT_elem_iso V V' E))
    (@ue_elem (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E))
    ≈ @tensor_gen R V V'.
Proof.
  exact (ue_med_commutes
           (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
           (tensor_universal_element V V')).
Qed.

Definition tensor_AFT_elem_unique {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :=
  universal_element_unique
    (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
    (tensor_universal_element V V').

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem tensor_AFT_iso_carries_elem {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  fmap[Bilin V V'] (to (tensor_AFT_iso_of_esols V V' E))
    (@ue_elem (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E))
    ≈ @tensor_gen R V V'.
Proof.
  pose proof (repr_compatible_at
    (repr_induced_compatible (tensor_repr_of_UE V V')
       (tensor_via_AFT_of_esols V V' E) nat_id) (TensorMod V V') id) as HC.
  pose proof (@naturality _ _ _ _
      (to (@represented _ _ (tensor_via_AFT_of_esols V V' E)))
      (@repr_obj _ _ (tensor_via_AFT_of_esols V V' E)) (TensorMod V V')
      (to (tensor_AFT_iso_of_esols V V' E)) (@id (RMod R) _)) as HN.
  transitivity (transform[to (@represented _ _ (tensor_via_AFT_of_esols V V' E))]
                  (TensorMod V V')
                  (@compose (RMod R) _ _ _ (to (tensor_AFT_iso_of_esols V V' E))
                     (@id (RMod R) _))).
  - exact HN.
  - transitivity (transform[to (@represented _ _ (tensor_via_AFT_of_esols V V' E))]
                    (TensorMod V V')
                    (@compose (RMod R) _ _ _ (@id (RMod R) _)
                       (to (tensor_AFT_iso_of_esols V V' E)))).
    + apply proper_morphism.
      rewrite id_left, id_right; reflexivity.
    + rewrite HC.
      exact (@fmap_id _ _ (Bilin V V') (TensorMod V V') (@tensor_gen R V V')).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem tensor_AFT_isos_agree {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  tensor_AFT_elem_iso V V' E ≈ tensor_AFT_iso_of_esols V V' E.
Proof.
  exact (universal_element_iso_unique
           (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
           (tensor_universal_element V V')
           (tensor_AFT_iso_of_esols V V' E)
           (tensor_AFT_iso_carries_elem V V' E)).
Qed.

(* * ** 6. Exercise 3: balanced-biadditive 函子 [Ab ⟶ Sets] （已译） *)

Section BalBiaddFunctor.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Program Definition BalBiadditive_Setoid (A : AbObject) :
  Setoid (BalBiadditive N M A) := {|
  equiv := fun β γ => ∀ n m, bal_map β n m ≈ bal_map γ n m
|}.
Next Obligation.
  intros A.
  constructor.
  - intros β n m; reflexivity.
  - intros β γ Hβγ n m; symmetry; apply Hβγ.
  - intros β γ δ H1 H2 n m.
    transitivity (bal_map γ n m); [ apply H1 | apply H2 ].
Qed.

Definition BalBiadd_obj (A : AbObject) : SetoidObject := {|
  carrier   := BalBiadditive N M A;
  is_setoid := BalBiadditive_Setoid A
|}.

Program Definition BalBiadd_post {A B : AbObject} (f : A ~{Ab}~> B)
  (β : BalBiadditive N M A) : BalBiadditive N M B := {|
  bal_map := fun n m => cmon_map f (bal_map β n m)
|}.
Next Obligation.
  intros A B f β n n' Hn m m' Hm; simpl.
  exact (proper_morphism (cmon_map f) _ _ (bal_respects β _ _ Hn _ _ Hm)).
Qed.
Next Obligation.
  intros A B f β n n' m; simpl.
  rewrite (bal_add_l β n n' m).
  apply (cmon_map_plus f).
Qed.
Next Obligation.
  intros A B f β n m m'; simpl.
  rewrite (bal_add_r β n m m').
  apply (cmon_map_plus f).
Qed.
Next Obligation.
  intros A B f β x n m; simpl.
  now rewrite (bal_balance β x n m).
Qed.

Program Definition BalBiadd : Ab ⟶ Sets := {|
  fobj := BalBiadd_obj;
  fmap := fun A B f => {| morphism := BalBiadd_post f |}
|}.
Next Obligation.
  intros A B f β γ Hβγ n m; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hβγ n m)).
Qed.
Next Obligation.
  intros A B f g Hfg β n m; simpl.
  exact (Hfg (bal_map β n m)).
Qed.
Next Obligation. intros A β n m; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g β n m; simpl; reflexivity. Qed.

(* The universal element explicit construction already supplies, the
 form comparison below 所消耗. （已译） *)
Program Definition bal_universal_element :
  AUniversalElement BalBiadd (BalTensor N M) := {|
  aue_elem      := @bal_gen X N M;
  aue_universal := fun A β => {| unique_obj := bal_med β |}
|}.
Next Obligation. intros A β n m; simpl; reflexivity. Qed.
Next Obligation.
  intros A β k Hk.
  symmetry.
  exact (bal_med_unique β k Hk).
Qed.

Definition bal_UniversalElement : UniversalElement BalBiadd :=
  UniversalElement_of_AUniversalElement bal_universal_element.

Example bal_UniversalElement_obj :
  @ue_obj Ab BalBiadd bal_UniversalElement = BalTensor N M := eq_refl.

Example bal_UniversalElement_elem :
  @ue_elem Ab BalBiadd bal_UniversalElement = @bal_gen X N M := eq_refl.

End BalBiaddFunctor.

Arguments BalBiadditive_Setoid {X} N M A.
Arguments BalBiadd_obj {X} N M A.
Arguments BalBiadd_post {X} N M {A B} f β.
Arguments BalBiadd {X} N M.
Arguments bal_universal_element {X} N M.
Arguments bal_UniversalElement {X} N M.

(* 相关说明。 （已译） *)

Section BalContinuity.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Section AtALimitingCone.

Context {J : Category}.
Context {K : J ⟶ Ab}.
Context {L : Cone K}.
Context (HL : IsLimitCone L).

Definition bal_sets_limit : IsLimitCone (FCone Ab_Forget L) :=
  Ab_Forget_creates_continuous J K L HL.

Lemma bal_lim_ext (u v : carrier (cmon_setoid vertex_obj[L]))
  (H : ∀ x : J, cmon_map (cone_leg L x) u ≈ cmon_map (cone_leg L x) v) :
  u ≈ v.
Proof using All. exact (slim_ext bal_sets_limit u v H). Qed.

Section AtACone.

Context (Q : Cone (BalBiadd N M ◯ K)).

Lemma bal_family_compat (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N))) (m : carrier (cmon_setoid (rm_ab M)))
  (x y : J) (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f (bal_map (cone_leg Q x q) n m)
    ≈ bal_map (cone_leg Q y q) n m.
Proof using All.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ Q) x y f q n m).
Qed.

Definition bal_med_elem (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  carrier (cmon_setoid vertex_obj[L]) :=
  slim_elem bal_sets_limit (fun x => bal_map (cone_leg Q x q) n m)
    (fun x y f => bal_family_compat q n m x y f).

Lemma bal_med_elem_leg (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) (x : J) :
  cmon_map (cone_leg L x) (bal_med_elem q n m)
    ≈ bal_map (cone_leg Q x q) n m.
Proof using All.
  exact (slim_elem_leg bal_sets_limit
           (fun x => bal_map (cone_leg Q x q) n m)
           (fun x y f => bal_family_compat q n m x y f) x).
Qed.

Program Definition BalBiadd_med (q : carrier (vertex_obj[Q])) :
  BalBiadditive N M vertex_obj[L] := {|
  bal_map := bal_med_elem q
|}.
Next Obligation.
  intros q n n' Hn m m' Hm.
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  exact (bal_respects (cone_leg Q x q) _ _ Hn _ _ Hm).
Qed.
Next Obligation.
  intros q n n' m.
  apply bal_lim_ext; intro x.
  rewrite bal_med_elem_leg.
  rewrite (cmon_map_plus (cone_leg L x)).
  rewrite !bal_med_elem_leg.
  apply bal_add_l.
Qed.
Next Obligation.
  intros q n m m'.
  apply bal_lim_ext; intro x.
  rewrite bal_med_elem_leg.
  rewrite (cmon_map_plus (cone_leg L x)).
  rewrite !bal_med_elem_leg.
  apply bal_add_r.
Qed.
Next Obligation.
  intros q r n m.
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  apply bal_balance.
Qed.

Program Definition BalBiadd_cone_med :
  vertex_obj[Q] ~{Sets}~> vertex_obj[FCone (BalBiadd N M) L] :=
  {| morphism := BalBiadd_med |}.
Next Obligation.
  intros q q' Hq n m.
  change (bal_med_elem q n m ≈ bal_med_elem q' n m).
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  exact (proper_morphism (cone_leg Q x) q q' Hq n m).
Qed.

End AtACone.

Theorem BalBiadd_preserves_cone : IsLimitCone (FCone (BalBiadd N M) L).
Proof using All.
  intro Q.
  unshelve refine {| unique_obj := BalBiadd_cone_med Q |}.
  - intros x q n m.
    exact (bal_med_elem_leg Q q n m x).
  - intros u Hu q n m.
    apply bal_lim_ext; intro x.
    rewrite (bal_med_elem_leg Q q n m x).
    symmetry; exact (Hu x q n m).
Qed.

End AtALimitingCone.

Definition BalBiadd_continuous : ContinuousFunctor (BalBiadd N M) :=
  fun J K L HL => BalBiadd_preserves_cone HL.

Definition BalBiadd_PreservesImageLimit :
  @PreservesImageLimit Ab Sets (BalBiadd N M) :=
  Continuous_PreservesImageLimit BalBiadd_continuous.

End BalContinuity.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BalCongruenceIndex.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Record IsBalCongruence (Rq : bsum N M → bsum N M → Prop) : Prop := {
  bc_refl  : ∀ s, Rq s s;
  bc_sym   : ∀ s t, Rq s t → Rq t s;
  bc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  bc_gen   : ∀ s t, bs_eq s t → Rq s t;
  bc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (bs_plus s t) (bs_plus s' t');
  bc_neg   : ∀ s s', Rq s s' → Rq (bs_neg s) (bs_neg s')
}.

Definition BalCongIdx : Type :=
  { Rq : bsum N M → bsum N M → Prop & IsBalCongruence Rq }.

End BalCongruenceIndex.

Arguments IsBalCongruence {X} N M Rq.
Arguments BalCongIdx {X} N M.

Section BalQuotient.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

(* 相关说明。 （已译） *)
Definition QBal_Setoid (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : Setoid (bsum N M) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := bc_refl  _ _ Rq H
        ; Equivalence_Symmetric  := bc_sym   _ _ Rq H
        ; Equivalence_Transitive := bc_trans _ _ Rq H |} |}.

Definition QBal (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : obj[Ab] :=
  {| ab_cmon := {|
       cmon_setoid :=
         {| carrier := bsum N M ; is_setoid := QBal_Setoid Rq H |};
       cmon_zero := @bs_zero X N M;
       cmon_plus := @bs_plus X N M;
       cmon_plus_respects := fun _ _ Hs _ _ Ht => bc_plus _ _ Rq H _ _ _ _ Hs Ht;
       cmon_plus_assoc := fun s t u => bc_gen _ _ Rq H _ _ (be_assoc s t u);
       cmon_plus_comm  := fun s t => bc_gen _ _ Rq H _ _ (be_comm s t);
       cmon_plus_zero_l := fun s => bc_gen _ _ Rq H _ _ (be_zero_l s);
       cmon_prop := @PropEquiv_of_relation _ (QBal_Setoid Rq H) Rq
                      (fun _ _ h => h) (fun _ _ h => h)
     |};
     ab_neg := @bs_neg X N M;
     ab_neg_respects := fun _ _ Hs => bc_neg _ _ Rq H _ _ Hs;
     ab_neg_left := fun s => bc_gen _ _ Rq H _ _ (be_neg_l s)
  |}.

(* The canonical balanced map 进入 quotient generator former. （已译） *)
Definition QBal_gen (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : BalBiadditive N M (QBal Rq H) :=
  @Build_BalBiadditive X N M (QBal Rq H) (@bs_gen X N M)
    (fun _ _ Hn _ _ Hm => bc_gen _ _ Rq H _ _ (be_gen Hn Hm))
    (fun n n' m => bc_gen _ _ Rq H _ _ (be_add_l n n' m))
    (fun n m m' => bc_gen _ _ Rq H _ _ (be_add_r n m m'))
    (fun x n m => bc_gen _ _ Rq H _ _ (be_balance x n m)).

End BalQuotient.

Arguments QBal_Setoid {X N M} Rq H.
Arguments QBal {X N M} Rq H.
Arguments QBal_gen {X N M} Rq H.

Section BalKernelCongruence.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).
Context {A : AbObject}.
Context (beta : BalBiadditive N M A).

(* NO [PropEquiv] hypothesis: [cmon_prop] is a field of [CMonObject] and
   [AbObject] is a record over one. *)
Definition bal_ker_cong : bsum N M → bsum N M → Prop :=
  fun s t => @pequiv _ _ (cmon_prop A)
               (bal_med_fun beta s) (bal_med_fun beta t).

Lemma bal_ker_is_cong : IsBalCongruence N M bal_ker_cong.
Proof.
  unfold bal_ker_cong.
  constructor.
  - intro s; apply (@pequiv_from _ _ (cmon_prop A)); reflexivity.
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop A)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop A) _ _ H).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop A)).
    transitivity (bal_med_fun beta t);
      [ exact (@pequiv_to _ _ (cmon_prop A) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop A) _ _ H2) ].
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop A));
      exact (bal_med_respects N M beta s t H).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop A)); simpl.
    exact (cmon_plus_respects A _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H2)).
  - intros s s' H; apply (@pequiv_from _ _ (cmon_prop A)); simpl.
    exact (ab_neg_respects A _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H)).
Qed.

Definition bal_ker_idx : BalCongIdx N M :=
  existT _ bal_ker_cong bal_ker_is_cong.

(* The mediator out quotient. Respectfulness IS [pequiv_to]; the
 two 幺半群 laws [reflexivity], mediator being [bal_med_fun]. （已译） *)
Program Definition bal_ker_med :
  QBal bal_ker_cong bal_ker_is_cong ~{Ab}~> A := {|
  cmon_map := {| morphism := bal_med_fun beta |}
|}.
Solve All Obligations with
  (first [ (intros s t H; exact (@pequiv_to _ _ (cmon_prop A) _ _ H))
         | (intros; simpl; reflexivity) ]).

(* 相关说明。 （已译） *)
Example bal_ker_factors (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map bal_ker_med (bal_map (QBal_gen bal_ker_cong bal_ker_is_cong) n m)
  = bal_map beta n m
  := eq_refl.

End BalKernelCongruence.

Arguments bal_ker_cong {X N M A} beta.
Arguments bal_ker_is_cong {X N M A} beta.
Arguments bal_ker_idx {X N M A} beta.
Arguments bal_ker_med {X N M A} beta.

(* 相关说明。 （已译） *)
Definition QBalOf {X : RingObject} {N : RModObject (Ring_op X)}
  {M : RModObject X} (i : BalCongIdx N M) : obj[Ab] := QBal (`1 i) (`2 i).

Definition QBalGenOf {X : RingObject} {N : RModObject (Ring_op X)}
  {M : RModObject X} (i : BalCongIdx N M) : BalBiadditive N M (QBalOf i) :=
  QBal_gen (`1 i) (`2 i).

Definition bal_esols_prop {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     (BalCongIdx N M) QBalOf QBalGenOf _).
  intros A beta.
  exists (bal_ker_idx beta), (bal_ker_med beta).
  intros n m; simpl; reflexivity.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition bal_tensor_via_AFT_of_esols {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X)
  (E : ElementSolutionSet (BalBiadd N M)) :
  Representable (BalBiadd N M) :=
  representability_theorem (BalBiadd N M) Ab_Complete
    (BalBiadd_PreservesImageLimit N M) E.

Definition bal_tensor_via_AFT {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_prop N M).

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bal_esols_from_tensor {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     unit (fun _ => BalTensor N M)
                     (fun _ => @bal_gen X N M) _).
  intros A β.
  refine (existT _ tt _).
  refine (existT _ (bal_med β) _).
  intros n m; reflexivity.
Defined.

Definition bal_tensor_via_AFT_from_tensor {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_from_tensor N M).

Definition bal_repr_of_UE {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : Representable (BalBiadd N M) :=
  Representable_of_UniversalElement (bal_UniversalElement N M).

Example bal_repr_of_UE_obj {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  @repr_obj Ab (BalBiadd N M) (bal_repr_of_UE N M) = BalTensor N M := eq_refl.

Definition bal_AFT_iso_of_esols {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  @repr_obj Ab (BalBiadd N M) (bal_tensor_via_AFT_of_esols N M E)
    ≅ BalTensor N M :=
  repr_unique_iso (bal_repr_of_UE N M)
    (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_iso {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  @repr_obj Ab (BalBiadd N M) (bal_tensor_via_AFT N M) ≅ BalTensor N M :=
  bal_AFT_iso_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_iso_universal_of_esols {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X)
  (E : ElementSolutionSet (BalBiadd N M)) :=
  repr_unique_iso_universal (bal_repr_of_UE N M)
    (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_iso_universal {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :=
  bal_AFT_iso_universal_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_ue_of_esols {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  UniversalElement (BalBiadd N M) :=
  UniversalElement_of_Representable (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_ue {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : UniversalElement (BalBiadd N M) :=
  bal_AFT_ue_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_elem_iso {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  @ue_obj Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E) ≅ BalTensor N M :=
  universal_element_iso
    (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
    (bal_universal_element N M).

Theorem bal_AFT_elem_commutes {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  fmap[BalBiadd N M] (to (bal_AFT_elem_iso N M E))
    (@ue_elem Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E))
    ≈ @bal_gen X N M.
Proof.
  exact (ue_med_commutes
           (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
           (bal_universal_element N M)).
Qed.

Theorem bal_AFT_iso_carries_elem {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  fmap[BalBiadd N M] (to (bal_AFT_iso_of_esols N M E))
    (@ue_elem Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E))
    ≈ @bal_gen X N M.
Proof.
  pose proof (repr_compatible_at
    (repr_induced_compatible (bal_repr_of_UE N M)
       (bal_tensor_via_AFT_of_esols N M E) nat_id) (BalTensor N M) id) as HC.
  pose proof (@naturality _ _ _ _
      (to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E)))
      (@repr_obj _ _ (bal_tensor_via_AFT_of_esols N M E)) (BalTensor N M)
      (to (bal_AFT_iso_of_esols N M E)) (@id Ab _)) as HN.
  transitivity (transform[to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E))]
                  (BalTensor N M)
                  (@compose Ab _ _ _ (to (bal_AFT_iso_of_esols N M E)) (@id Ab _))).
  - exact HN.
  - transitivity (transform[to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E))]
                    (BalTensor N M)
                    (@compose Ab _ _ _ (@id Ab _) (to (bal_AFT_iso_of_esols N M E)))).
    + apply proper_morphism.
      rewrite id_left, id_right; reflexivity.
    + rewrite HC.
      exact (@fmap_id _ _ (BalBiadd N M) (BalTensor N M) (@bal_gen X N M)).
Qed.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem bal_AFT_isos_agree {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  bal_AFT_elem_iso N M E ≈ bal_AFT_iso_of_esols N M E.
Proof.
  exact (universal_element_iso_unique
           (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
           (bal_universal_element N M)
           (bal_AFT_iso_of_esols N M E)
           (bal_AFT_iso_carries_elem N M E)).
Qed.

Definition bal_AFT_elem_unique {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :=
  universal_element_unique
    (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
    (bal_universal_element N M).

(* 相关说明。 （已译） *)

Section AbGeneratedSub.

Context {A : AbObject}.
Context (P : carrier (cmon_setoid A) → Type).

(* Instance/Mod/Spanning.v's [ABGen] has exactly five fields of
 Instance/Ab/DirectedColimit.v's [AbSubgroup]; 这是 the
 repackaging, no 证明 obligation. （已译） *)
Definition ABGenSub : AbSubgroup A :=
  @Build_AbSubgroup A (ABGen P) (abgen_resp P) (abgen_zero P)
    (abgen_plus P) (abgen_neg P).

End AbGeneratedSub.

(* 相关说明。 （已译） *)
Program Definition AbImageSub {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSubgroup B := {|
  absub_mem := fun b => { a : carrier (cmon_setoid A) & cmon_map f a ≈ b }
|}.
Next Obligation.
  intros A B f a b Hab [x Hx].
  exists x; rewrite Hx; exact Hab.
Qed.
Next Obligation.
  intros A B f.
  exists (cmon_zero A); apply cmon_map_zero.
Qed.
Next Obligation.
  intros A B f a b [x Hx] [y Hy].
  exists (cmon_plus A x y).
  rewrite (cmon_map_plus f); now rewrite Hx, Hy.
Qed.
Next Obligation.
  intros A B f a [x Hx].
  exists (ab_neg A x).
  rewrite (ab_map_neg f); now rewrite Hx.
Qed.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ab_split {A B : AbObject} (f : A ~{Ab}~> B)
  (Hi : AbInjective f) (Hs : AbSurjective f) : B ~{Ab}~> A := {|
  cmon_map := {| morphism := fun b => `1 (Hs b) |}
|}.
Next Obligation.
  intros A B f Hi Hs a b Hab.
  apply Hi; rewrite (`2 (Hs a)), (`2 (Hs b)); exact Hab.
Qed.
Next Obligation.
  intros A B f Hi Hs; simpl.
  apply Hi; rewrite (`2 (Hs (cmon_zero B))).
  symmetry; exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A B f Hi Hs a b; simpl.
  apply Hi.
  rewrite (cmon_map_plus f).
  rewrite (`2 (Hs (cmon_plus B a b))), (`2 (Hs a)), (`2 (Hs b)).
  reflexivity.
Qed.

Lemma ab_split_commutes {A B : AbObject} (f : A ~{Ab}~> B)
  (Hi : AbInjective f) (Hs : AbSurjective f) :
  @compose Ab _ _ _ f (ab_split f Hi Hs) ≈ @id Ab B.
Proof. intro b; exact (`2 (Hs b)). Qed.

(* A subgroup subobject [Ab]: 含入 injective the
 nose, hence monic. （已译） *)
Definition abg_subobj {A : AbObject} (S : AbSubgroup A) : @SubObj Ab A :=
  @Build_SubObj Ab A (AbSubgroupAb S) (absub_incl S)
    (ab_injective_monic (absub_incl S) (fun _ _ H => H)).

Section BalSpanningBridge.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).
Context {A : AbObject}.
Context (β : BalBiadditive N M A).

Definition bal_restrict_image (m : @SubObj Ab A)
  (β' : BalBiadditive N M (sub_dom m))
  (Hβ : ∀ n mm, cmon_map (sub_mono m) (bal_map β' n mm) ≈ bal_map β n mm)
  (a : carrier (cmon_setoid A)) (Ha : bal_image N M β a) :
  absub_mem (AbImageSub (sub_mono m)) a.
Proof using All.
  destruct Ha as [n [mm Hnm]].
  exists (bal_map β' n mm).
  rewrite (Hβ n mm); exact Hnm.
Defined.

(*
   本节说明 TensorAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem bal_spanning_to_spanning (H : BalSpanning N M β) :
  Spanning (BalBiadd N M) (global_element (X := BalBiadd N M A) β).
Proof using All.
  intros m [k Hk].
  pose (β' := k ttt).
  assert (Hβ : ∀ n mm, cmon_map (sub_mono m) (bal_map β' n mm)
                         ≈ bal_map β n mm) by exact (Hk ttt).
  assert (Hs : AbSurjective (sub_mono m)).
  { intro x.
    exact (abgen_least (bal_image N M β)
             (absub_mem (AbImageSub (sub_mono m)))
             (absub_resp (AbImageSub (sub_mono m)))
             (absub_zero (AbImageSub (sub_mono m)))
             (absub_plus (AbImageSub (sub_mono m)))
             (absub_neg (AbImageSub (sub_mono m)))
             (bal_restrict_image m β' Hβ) x (H x)). }
  assert (Hi : AbInjective (sub_mono m)) by
    exact (ab_monic_injective (sub_mono m) (sub_is_monic m)).
  exists (ab_split (sub_mono m) Hi Hs).
  exact (ab_split_commutes (sub_mono m) Hi Hs).
Defined.

(* 相关说明。 （已译） *)
Program Definition bal_gen_corestrict :
  BalBiadditive N M (AbSubgroupAb (ABGenSub (bal_image N M β))) := {|
  bal_map := fun n mm =>
    existT _ (bal_map β n mm)
      (abgen_base (bal_image N M β) (bal_map β n mm)
         (existT _ n (existT _ mm (reflexivity _))))
|}.
Next Obligation.
  intros n n' Hn m m' Hm; simpl.
  exact (bal_respects β _ _ Hn _ _ Hm).
Qed.
Next Obligation. intros n n' m; simpl; apply bal_add_l. Qed.
Next Obligation. intros n m m'; simpl; apply bal_add_r. Qed.
Next Obligation. intros x n m; simpl; apply bal_balance. Qed.

Lemma bal_corestrict_spanning : BalSpanning N M bal_gen_corestrict.
Proof using All.
  intros [a D].
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|a D IH].
  - refine (abgen_base (bal_image N M bal_gen_corestrict) _ _).
    destruct Ha as [n [mm Hnm]].
    exists n, mm; exact Hnm.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _ IH).
    exact Hab.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_zero (bal_image N M bal_gen_corestrict))).
    reflexivity.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_plus (bal_image N M bal_gen_corestrict) _ _ IH1 IH2)).
    reflexivity.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_neg (bal_image N M bal_gen_corestrict) _ IH)).
    reflexivity.
Defined.

End BalSpanningBridge.

Definition bal_esols_direct {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     (SpanningArrowsOutOf (BalBiadd N M) SetsOne)
                     (fun i => `1 i) (fun i => `1 (`2 i) ttt) _).
  intros A β.
  unshelve eexists.
  - refine (existT _ (AbSubgroupAb (ABGenSub (bal_image N M β))) _).
    refine (existT _ (global_element
                        (X := BalBiadd N M
                                (AbSubgroupAb (ABGenSub (bal_image N M β))))
                        (bal_gen_corestrict N M β)) _).
    exact (bal_spanning_to_spanning N M (bal_gen_corestrict N M β)
             (bal_corestrict_spanning N M β)).
  - exists (absub_incl (ABGenSub (bal_image N M β))).
    intros n m; reflexivity.
Defined.

Example bal_esols_direct_index {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  esol_index (bal_esols_direct N M)
    = SpanningArrowsOutOf (BalBiadd N M) SetsOne := eq_refl.

Example bal_esols_direct_obj {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (i : SpanningArrowsOutOf (BalBiadd N M) SetsOne) :
  esol_obj (bal_esols_direct N M) i = `1 i := eq_refl.

Example bal_esols_direct_elem {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (i : SpanningArrowsOutOf (BalBiadd N M) SetsOne) :
  esol_elem (bal_esols_direct N M) i = `1 (`2 i) ttt := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cong_spanning_arrow {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : SpanningArrowsOutOf (Bilin V V') SetsOne :=
  existT _ (QModOf i)
    (existT _ (global_element (X := Bilin V V' (QModOf i)) (QModGenOf i))
       (rbilinear_spanning_to_spanning (QModGenOf i)
          (QMod_gen_spanning (`1 i) (`2 i)))).

Theorem tensor_spanning_SmallUpToIso {R : RingObject} (V V' : obj[RMod R]) :
  SmallUpToIso (sols_of_esols (Bilin V V') (tensor_esols_direct V V')).
Proof.
  unshelve refine (@Build_SmallUpToIso (RMod R) Sets (Bilin V V') SetsOne
                     (sols_of_esols (Bilin V V') (tensor_esols_direct V V'))
                     (CongIdx V V') cong_spanning_arrow _).
  intro i.
  destruct i as [W [g sp]].
  pose (beta := g ttt).
  assert (Hg : g ≈ global_element (X := Bilin V V' W) beta).
  { intro u; destruct u; intros v w; reflexivity. }
  assert (Hsp : RBilinearSpanning beta).
  { exact (spanning_to_rbilinear_spanning beta
             (spanning_respects (Bilin V V') g
                (global_element (X := Bilin V V' W) beta) Hg sp)). }
  exists (ker_idx beta).
  unshelve eexists.
  - exact (ker_iso beta Hsp).
  - intro u; destruct u; simpl; intros v w; reflexivity.
Defined.

(* Mac Lane's OWN family, resized by his own Lemma 2. *)
Definition tensor_esols_resized {R : RingObject} (V V' : obj[RMod R]) :
  ElementSolutionSet (Bilin V V') :=
  esols_of_sols (Bilin V V')
    (resize_up_to_iso (sols_of_esols (Bilin V V') (tensor_esols_direct V V'))
       (tensor_spanning_SmallUpToIso V V')).

(* ...and fed to the theorem.  Same signature as [tensor_via_AFT], reached
   by a different argument: p. 128's covering family plus Lemma 2, rather
   than the kernel congruence of an arbitrary bilinear map directly. *)
Definition tensor_via_AFT_maclane {R : RingObject} (V V' : obj[RMod R]) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_resized V V').
