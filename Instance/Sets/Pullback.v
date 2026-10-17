Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Regular.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(** * Pullbacks in [Sets] *)

(*
 nLab:      https://ncatlab.org/nlab/show/kernel+pair
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   本文件给出拉回实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ====================================================================== *)
(* 相关说明。 （已译） *)

Section SetsPullback.

Context {x y z : Sets}.
Context (f : x ~{Sets}~> z) (g : y ~{Sets}~> z).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_pb_carrier : Type :=
  { p : carrier x * carrier y & @equiv _ z (f (fst p)) (g (snd p)) }.

(* 相关说明。 （已译） *)
Definition sets_pb_equiv : crelation sets_pb_carrier :=
  fun u v => (@equiv _ x (fst `1 u) (fst `1 v) *
              @equiv _ y (snd `1 u) (snd `1 v))%type.

Lemma sets_pb_equivalence : Equivalence sets_pb_equiv.
Proof.
  constructor.
  - intros u; split; reflexivity.
  - intros u v [H1 H2]; split; symmetry; assumption.
  - intros u v w [H1 H2] [K1 K2]; split.
    + transitivity (fst `1 v); assumption.
    + transitivity (snd `1 v); assumption.
Qed.

Definition sets_pb_obj : Sets :=
  {| carrier   := sets_pb_carrier
   ; is_setoid := {| equiv        := sets_pb_equiv
                   ; setoid_equiv := sets_pb_equivalence |} |}.

Program Definition sets_pb_fst : sets_pb_obj ~{Sets}~> x :=
  {| morphism := fun u => fst `1 u |}.
Next Obligation. intros u v H; exact (fst H). Qed.

Program Definition sets_pb_snd : sets_pb_obj ~{Sets}~> y :=
  {| morphism := fun u => snd `1 u |}.
Next Obligation. intros u v H; exact (snd H). Qed.

Lemma sets_pb_commutes : f ∘ sets_pb_fst ≈ g ∘ sets_pb_snd.
Proof. intros u; exact (`2 u). Qed.

(* 相关说明。 （已译） *)
Program Definition sets_pb_med {Q : Sets}
        (q1 : Q ~{Sets}~> x) (q2 : Q ~{Sets}~> y)
        (Hq : f ∘ q1 ≈ g ∘ q2) : Q ~{Sets}~> sets_pb_obj :=
  {| morphism := fun e => ((q1 e, q2 e); Hq e) |}.
Next Obligation.
  intros e e' H.
  exact (proper_morphism q1 e e' H, proper_morphism q2 e e' H).
Qed.

Definition Sets_IsPullback :
  IsPullback f g sets_pb_obj sets_pb_fst sets_pb_snd.
Proof.
  constructor.
  - exact sets_pb_commutes.
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + exact (sets_pb_med q1 q2 Hq).
    + split; intros e; reflexivity.
    + intros v [Hv1 Hv2] e; split; symmetry; [exact (Hv1 e)|exact (Hv2 e)].
Defined.

Definition Sets_Pullback : Pullback f g :=
  is_pullback_pullback Sets_IsPullback.

(* 相关说明。 （已译） *)
Definition Sets_Pullback_obj : Pull f g Sets_Pullback = sets_pb_obj := eq_refl.
Definition Sets_Pullback_fst :
  pullback_fst f g Sets_Pullback = sets_pb_fst := eq_refl.
Definition Sets_Pullback_snd :
  pullback_snd f g Sets_Pullback = sets_pb_snd := eq_refl.

End SetsPullback.

#[export] Instance Sets_HasPullbacks : HasPullbacks Sets :=
  {| pullback := @Sets_Pullback |}.

(* ====================================================================== *)
(* 相关说明。 （已译） *)

Section KernelPair.

Context {a b : Sets}.
Context (f : a ~{Sets}~> b).

(* The 关系 setoid {(u, v) | f u ≈ f v}, agreement
 sub-setoid (A) taken at cospan (f, f). （已译） *)
Definition sets_ker : Sets := sets_pb_obj f f.

Definition sets_ker_fst : sets_ker ~{Sets}~> a := sets_pb_fst f f.
Definition sets_ker_snd : sets_ker ~{Sets}~> a := sets_pb_snd f f.

(* Structure/Regular.v's generic [kernel_pair] IS 关系 setoid,
 those two projections, nose. （已译） *)
Definition sets_kernel_pair_obj :
  Pull f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker := eq_refl.

Definition sets_kernel_pair_fst :
  pullback_fst f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker_fst
  := eq_refl.

Definition sets_kernel_pair_snd :
  pullback_snd f f (@kernel_pair Sets Sets_HasPullbacks a b f) = sets_ker_snd
  := eq_refl.

(* Membership, both ways. *)
Definition sets_ker_pair (u v : carrier a) (H : @equiv _ b (f u) (f v)) :
  carrier sets_ker := ((u, v); H).

Lemma sets_ker_related (w : carrier sets_ker) :
  @equiv _ b (f (sets_ker_fst w)) (f (sets_ker_snd w)).
Proof. exact (`2 w). Qed.

(* * ** The 等价-关系 laws, exhibited arrows （已译） *)

(* Reflexivity: the diagonal a ~> R, splitting both projections. *)
Program Definition sets_ker_refl : a ~{Sets}~> sets_ker :=
  {| morphism := fun u => ((u, u); reflexivity (f u)) |}.
Next Obligation. intros u v H; exact (H, H). Qed.

Lemma sets_ker_refl_fst : sets_ker_fst ∘ sets_ker_refl ≈ id[a].
Proof. intros u; reflexivity. Qed.

Lemma sets_ker_refl_snd : sets_ker_snd ∘ sets_ker_refl ≈ id[a].
Proof. intros u; reflexivity. Qed.

(* 相关说明。 （已译） *)
Program Definition sets_ker_sym : sets_ker ~{Sets}~> sets_ker :=
  {| morphism := fun w => ((snd `1 w, fst `1 w); symmetry (`2 w)) |}.
Next Obligation. intros w w' H; exact (snd H, fst H). Qed.

Lemma sets_ker_sym_fst : sets_ker_fst ∘ sets_ker_sym ≈ sets_ker_snd.
Proof. intros w; reflexivity. Qed.

Lemma sets_ker_sym_snd : sets_ker_snd ∘ sets_ker_sym ≈ sets_ker_fst.
Proof. intros w; reflexivity. Qed.

(* Transitivity needs 对象 composable pairs, itself a
 pullback: pullback [sets_ker_snd] along [sets_ker_fst]. （已译） *)
Definition sets_ker_comp : Sets := sets_pb_obj sets_ker_snd sets_ker_fst.

Definition sets_ker_comp_is_pullback :
  Pull sets_ker_snd sets_ker_fst
       (@pullback Sets Sets_HasPullbacks _ _ _ sets_ker_snd sets_ker_fst)
  = sets_ker_comp := eq_refl.

Definition sets_ker_comp_fst : sets_ker_comp ~{Sets}~> sets_ker :=
  sets_pb_fst sets_ker_snd sets_ker_fst.
Definition sets_ker_comp_snd : sets_ker_comp ~{Sets}~> sets_ker :=
  sets_pb_snd sets_ker_snd sets_ker_fst.

Lemma sets_ker_trans_related (w : carrier sets_ker_comp) :
  @equiv _ b (f (fst `1 (fst `1 w))) (f (snd `1 (snd `1 w))).
Proof.
  transitivity (f (snd `1 (fst `1 w))).
  - exact (`2 (fst `1 w)).
  - transitivity (f (fst `1 (snd `1 w))).
    + exact (proper_morphism f _ _ (`2 w)).
    + exact (`2 (snd `1 w)).
Qed.

Program Definition sets_ker_trans : sets_ker_comp ~{Sets}~> sets_ker :=
  {| morphism := fun w => ((fst `1 (fst `1 w), snd `1 (snd `1 w));
                           sets_ker_trans_related w) |}.
Next Obligation. intros w w' H; exact (fst (fst H), snd (snd H)). Qed.

Lemma sets_ker_trans_fst :
  sets_ker_fst ∘ sets_ker_trans ≈ sets_ker_fst ∘ sets_ker_comp_fst.
Proof. intros w; reflexivity. Qed.

Lemma sets_ker_trans_snd :
  sets_ker_snd ∘ sets_ker_trans ≈ sets_ker_snd ∘ sets_ker_comp_snd.
Proof. intros w; reflexivity. Qed.

End KernelPair.

(* ====================================================================== *)
(* 相关说明。 （已译） *)

Section PullbackAsEqualizer.

Context {x y z : Sets}.
Context (f : x ~{Sets}~> z) (g : y ~{Sets}~> z).

(* The equalizing map 进入 product: two projections paired. （已译） *)
Definition sets_pb_pair : sets_pb_obj f g ~{Sets}~> (x × y)%object :=
  (sets_pb_fst f g △ sets_pb_snd f g).

Definition sets_pullback_is_equalizer :
  IsEqualizer (f ∘ exl) (g ∘ exr) (sets_pb_obj f g) sets_pb_pair :=
  equalizer_of_pullback (Sets_IsPullback f g).

(* 相关说明。 （已译） *)
Definition sets_equalizer_is_pullback :
  IsPullback f g (sets_pb_obj f g) (exl ∘ sets_pb_pair) (exr ∘ sets_pb_pair) :=
  pullback_of_equalizer f g sets_pullback_is_equalizer.

Lemma sets_equalizer_round_fst : exl ∘ sets_pb_pair ≈ sets_pb_fst f g.
Proof. intros u; reflexivity. Qed.

Lemma sets_equalizer_round_snd : exr ∘ sets_pb_pair ≈ sets_pb_snd f g.
Proof. intros u; reflexivity. Qed.

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example sets_equalizer_round_fst_pointwise (u : carrier (sets_pb_obj f g)) :
  (exl ∘ sets_pb_pair) u = sets_pb_fst f g u := eq_refl.

Example sets_equalizer_round_snd_pointwise (u : carrier (sets_pb_obj f g)) :
  (exr ∘ sets_pb_pair) u = sets_pb_snd f g u := eq_refl.

(* 相关说明。 （已译） *)
Lemma sets_pb_pair_computes (u : carrier (sets_pb_obj f g)) :
  @equiv _ (x × y)%object (sets_pb_pair u) (`1 u).
Proof. split; reflexivity. Qed.

Lemma sets_pb_pair_equalizes (u : carrier (sets_pb_obj f g)) :
  @equiv _ z ((f ∘ exl) (sets_pb_pair u)) ((g ∘ exr) (sets_pb_pair u)).
Proof. exact (`2 u). Qed.

End PullbackAsEqualizer.

(* ====================================================================== *)
(* 相关说明。 （已译） *)

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SubsetOf (B : Sets) : Type := {
  sub_mem : carrier B -> Type;
  sub_mem_resp : ∀ p q : carrier B, @equiv _ B p q -> sub_mem p -> sub_mem q
}.

Arguments sub_mem {B} _ _.
Arguments sub_mem_resp {B} _ {p q} _ _.

Section Subset.

Context {B : Sets}.
Context (S : SubsetOf B).

Lemma sub_obj_equivalence :
  Equivalence (fun u v : { p : carrier B & sub_mem S p } =>
                 @equiv _ B `1 u `1 v).
Proof.
  constructor.
  - intros u; reflexivity.
  - intros u v H; symmetry; exact H.
  - intros u v w H K; transitivity (`1 v); assumption.
Qed.

(* The subset 对象 [Sets]: elements B together a
 membership witness, compared underlying elements. （已译） *)
Definition sub_obj : Sets :=
  {| carrier   := { p : carrier B & sub_mem S p }
   ; is_setoid := {| equiv        := fun u v => @equiv _ B `1 u `1 v
                   ; setoid_equiv := sub_obj_equivalence |} |}.

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sub_incl : sub_obj ~{Sets}~> B.
Proof.
  unshelve refine {| morphism := fun u => `1 u |}.
  intros u v H; exact H.
Defined.

Lemma sub_incl_Monic : Monic sub_incl.
Proof. constructor; intros Z u v H e; exact (H e). Qed.

End Subset.

Arguments sub_obj {B} _.
Arguments sub_incl {B} _.

(* 相关说明。 （已译） *)
Definition FactorsThrough {Z W V : Sets} (m : W ~{Sets}~> V)
           (h : Z ~{Sets}~> V) : Type :=
  { k : Z ~{Sets}~> W & m ∘ k ≈ h }.

Section Preimage.

Context {A B : Sets}.
Context (f : A ~{Sets}~> B) (S : SubsetOf B).

(* The preimage {p | f p ∈ S}. *)
Definition sets_preimage : SubsetOf A.
Proof using All.
  unshelve refine {| sub_mem := fun p => sub_mem S (f p) |}.
  intros u v Huv Hm.
  exact (sub_mem_resp S (proper_morphism f u v Huv) Hm).
Defined.

(* Membership in the preimage IS membership downstream, definitionally. *)
Definition sets_preimage_mem (p : carrier A) :
  sub_mem sets_preimage p = sub_mem S (f p) := eq_refl.

(* 相关说明。 （已译） *)
Program Definition sets_preimage_over :
  sub_obj sets_preimage ~{Sets}~> sub_obj S :=
  {| morphism := fun u => (f `1 u; `2 u) |}.
Next Obligation. intros u v H; exact (proper_morphism f _ _ H). Qed.

(* The preimage square is a pullback. *)
Definition sets_preimage_IsPullback :
  IsPullback f (sub_incl S) (sub_obj sets_preimage)
             (sub_incl sets_preimage) sets_preimage_over.
Proof.
  constructor.
  - intros u; reflexivity.
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + unshelve refine {| morphism := fun e => (q1 e; _) |}.
      * exact (sub_mem_resp S (symmetry (Hq e)) (`2 (q2 e))).
      * intros e e' H; exact (proper_morphism q1 e e' H).
    + split; intros e; [reflexivity|exact (Hq e)].
    + intros v [Hv1 Hv2] e; symmetry; exact (Hv1 e).
Defined.

(** ** The elementwise criterion *)

(* 相关说明。 （已译） *)
Lemma sets_preimage_criterion {Z : Sets} (t : Z ~{Sets}~> A) :
  FactorsThrough (sub_incl sets_preimage) t ↔
  FactorsThrough (sub_incl S) (f ∘ t).
Proof.
  split.
  - intros [k Hk].
    exists (sets_preimage_over ∘ k).
    intros e; exact (proper_morphism f _ _ (Hk e)).
  - intros [j Hj].
    unshelve refine (_; _).
    + unshelve refine {| morphism := fun e => (t e; _) |}.
      * exact (sub_mem_resp S (Hj e) (`2 (j e))).
      * intros e e' H; exact (proper_morphism t e e' H).
    + intros e; reflexivity.
Defined.

End Preimage.

(* ====================================================================== *)
(* 相关说明。 （已译） *)

(*
   本节说明 Pullback 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PbNatSet : Sets :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Definition PbBoolSet : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Definition evenM : PbNatSet ~{Sets}~> PbBoolSet.
Proof.
  unshelve refine {| morphism := Nat.even |};
  try (intros n m H; rewrite H; reflexivity).
Defined.

Definition idB : PbBoolSet ~{Sets}~> PbBoolSet.
Proof.
  unshelve refine {| morphism := fun c : bool => c |};
  try (intros c c' H; exact H).
Defined.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition graph_even : Sets := sets_pb_obj evenM idB.

Example graph_even_3 : carrier graph_even := ((3%nat, false); eq_refl).
Example graph_even_4 : carrier graph_even := ((4%nat, true); eq_refl).

Example graph_even_3_fst :
  sets_pb_fst evenM idB graph_even_3 = 3%nat := eq_refl.
Example graph_even_3_snd :
  sets_pb_snd evenM idB graph_even_3 = false := eq_refl.

(* (3, true) is NOT in the agreement subset: no witness can be supplied. *)
Lemma graph_even_excludes_3_true :
  @equiv _ PbBoolSet (evenM 3%nat) (idB true) → False.
Proof. discriminate. Qed.

(** ** The mediator computes *)

Lemma even_square : evenM ∘ id[PbNatSet] ≈ idB ∘ evenM.
Proof. intros n; reflexivity. Qed.

Definition even_med : PbNatSet ~{Sets}~> graph_even :=
  sets_pb_med evenM idB id[PbNatSet] evenM even_square.

(* The mediator produced 普遍性质 IS map. （已译） *)
Definition even_med_is_ump :
  unique_obj (ump_pullbacks evenM idB (Sets_Pullback evenM idB)
                            PbNatSet id[PbNatSet] evenM even_square)
  = even_med := eq_refl.

Example even_med_5_fst :
  sets_pb_fst evenM idB (even_med 5%nat) = 5%nat := eq_refl.
Example even_med_5_snd :
  sets_pb_snd evenM idB (even_med 5%nat) = false := eq_refl.
Example even_med_6_snd :
  sets_pb_snd evenM idB (even_med 6%nat) = true := eq_refl.

(* 相关说明。 （已译） *)

Example even_ker_02 : carrier (sets_ker evenM) := ((0%nat, 2%nat); eq_refl).

Example even_ker_02_fst : sets_ker_fst evenM even_ker_02 = 0%nat := eq_refl.
Example even_ker_02_snd : sets_ker_snd evenM even_ker_02 = 2%nat := eq_refl.

(* So the relation genuinely identifies two distinct elements. *)
Lemma even_ker_not_diagonal :
  @equiv _ PbNatSet (sets_ker_fst evenM even_ker_02)
                  (sets_ker_snd evenM even_ker_02) → False.
Proof. discriminate. Qed.

(* 相关说明。 （已译） *)
Example even_ker_sym_02_fst :
  sets_ker_fst evenM (sets_ker_sym evenM even_ker_02) = 2%nat := eq_refl.

Example even_ker_refl_0_snd :
  sets_ker_snd evenM (sets_ker_refl evenM 0%nat) = 0%nat := eq_refl.

(* 相关说明。 （已译） *)
Example even_ker_24 : carrier (sets_ker evenM) := ((2%nat, 4%nat); eq_refl).

Example even_ker_composable : carrier (sets_ker_comp evenM) :=
  ((even_ker_02, even_ker_24); eq_refl).

Example even_ker_trans_fst :
  sets_ker_fst evenM (sets_ker_trans evenM even_ker_composable) = 0%nat
  := eq_refl.

Example even_ker_trans_snd :
  sets_ker_snd evenM (sets_ker_trans evenM even_ker_composable) = 4%nat
  := eq_refl.

(** ** The preimage of a subset *)

Definition TrueSub : SubsetOf PbBoolSet.
Proof.
  refine (Build_SubsetOf PbBoolSet (fun c : bool => c = true) _).
  intros u v Huv Hm; rewrite <- Huv; exact Hm.
Defined.

(* 相关说明。 （已译） *)
Definition even_preimage : SubsetOf PbNatSet := sets_preimage evenM TrueSub.

Example even_preimage_4 : carrier (sub_obj even_preimage) := (4%nat; eq_refl).

Lemma even_preimage_excludes_3 : sub_mem even_preimage 3%nat → False.
Proof. discriminate. Qed.

(* A non-常值 map 进入 preimage, criterion carrying it
 downstairs. （已译） *)
Definition chooseM : PbBoolSet ~{Sets}~> PbNatSet.
Proof.
  unshelve refine {| morphism := fun c : bool => if c then 4%nat else 2%nat |};
  try (intros c c' H; rewrite H; reflexivity).
Defined.

Definition choose_factors :
  FactorsThrough (sub_incl even_preimage) chooseM.
Proof.
  unshelve refine (_; _).
  - unshelve refine {| morphism := fun c : bool => (chooseM c; _) |}.
    all: try (intros c c' H; rewrite H; reflexivity).
    all: try (destruct c; reflexivity).
  - intros c; reflexivity.
Defined.

Definition choose_factors_downstairs :
  FactorsThrough (sub_incl TrueSub) (evenM ∘ chooseM) :=
  fst (sets_preimage_criterion evenM TrueSub chooseM) choose_factors.

Example choose_downstairs_true :
  `1 (`1 choose_factors_downstairs true) = true := eq_refl.

Example choose_downstairs_false :
  `1 (`1 choose_factors_downstairs false) = true := eq_refl.

(* The criterion not vacuous negative direction either: the
 常值 3 does not factor through preimage. （已译） *)
Definition constThree : PbBoolSet ~{Sets}~> PbNatSet.
Proof.
  unshelve refine {| morphism := fun _ : bool => 3%nat |};
  try (intros c c' H; reflexivity).
Defined.

Lemma constThree_does_not_factor :
  FactorsThrough (sub_incl even_preimage) constThree → False.
Proof.
  intros [k Hk].
  pose proof (`2 (k true)) as Hm.
  pose proof (Hk true) as He.
  simpl in He, Hm.
  rewrite He in Hm.
  discriminate.
Qed.
