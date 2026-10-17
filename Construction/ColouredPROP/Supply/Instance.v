Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Tensor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Supply.
Require Import Category.Construction.ColouredPROP.Linear.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Eqdep_dec.
(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
From Coq Require Import Morphisms.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/PROP
   nLab:      https://ncatlab.org/nlab/show/comonoid
   nLab:      https://ncatlab.org/nlab/show/generators+and+relations
   Reference: Fong & Spivak, "Supplying bells and whistles in symmetric

   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SupplyInstance.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (copyable : Colour -> bool).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive SupplyGen : list Colour -> list Colour -> Type :=
  | SG_dup (c : Colour) : copyable c = true -> SupplyGen [c] [c; c]
  | SG_del (c : Colour) : copyable c = true -> SupplyGen [c] [].

(** The extended signature: base generators plus supply generators. *)
Definition SupplyExtSig : CSignature Colour := Sum_CSig S SupplyGen.

(** 本节：The generators terms. [[c] ++ [c] ≡ [c; c]] definitionally,
 so [sg_dup] inhabits tensor-shaped boundary the
 nose. （已译） *)
Definition sg_dup (c : Colour) (H : copyable c = true) :
  CTerm SupplyExtSig [c] [c; c] :=
  CT_gen (inr (SG_dup c H)).

Definition sg_del (c : Colour) (H : copyable c = true) :
  CTerm SupplyExtSig [c] [] :=
  CT_gen (inr (SG_del c H)).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive SupplyEqs : forall cs ds : list Colour,
    CTerm SupplyExtSig cs ds -> CTerm SupplyExtSig cs ds -> Prop :=

  (** 本节：Coassociativity. The right-hand side carries [from] the
 presented associator at [([c], [c], [c])]: single
 [app_assoc [c] [c] [c]] cast. （已译） *)
  | SE_coassoc (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c; c; c]
        (CT_comp (CT_tens (sg_dup c H) (CT_id [c])) (sg_dup c H))
        (CT_comp (CT_comp (CT_cast (app_assoc [c] [c] [c]))
                          (CT_tens (CT_id [c]) (sg_dup c H)))
                 (sg_dup c H))

  (** Left counit law. Cast-free: [[] ++ [c] ≡ [c]] definitionally,
 so deleting left copy 恒等 wire nose. （已译） *)
  | SE_counit_left (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c]
        (CT_comp (CT_tens (sg_del c H) (CT_id [c])) (sg_dup c H))
        (CT_id [c])

  (*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  | SE_counit_right (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c]
        (CT_comp (CT_tens (CT_id [c]) (sg_del c H)) (sg_dup c H))
        (CT_cast (eq_sym (app_nil_r [c])))

  (** 本节：Cocommutativity. Cast-free: [CT_braid [c] [c]] the
 presented braid nose. （已译） *)
  | SE_cocomm (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c; c]
        (CT_comp (CT_braid [c] [c]) (sg_dup c H))
        (sg_dup c H).

(* 相关说明。 （已译） *)

Definition SupplySMT : CSMT Colour :=
  Build_CSMT Colour SupplyExtSig SupplyEqs.

(** 本节：The THIRD [ColouredPROP] instance library. （已译） *)
Definition SupplyPROP : ColouredPROP Colour :=
  CPresentedColouredPROP SupplySMT Cdec.

(** The generators, as morphisms of [SupplyPROP]. *)
Definition SupplyPROP_dup (c : Colour) (H : copyable c = true) :
  ([c] : list Colour) ~{CPresentedCat SupplySMT}~> [c; c] :=
  cquot SupplySMT (sg_dup c H).

Definition SupplyPROP_del (c : Colour) (H : copyable c = true) :
  ([c] : list Colour) ~{CPresentedCat SupplySMT}~> [] :=
  cquot SupplySMT (sg_del c H).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Coassociativity, in the shape of [delta_coassoc] at
    [CPresented_Monoidal SupplySMT Cdec]. *)
Definition supply_wire_coassoc (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_tens (sg_dup c H) (CT_id [c])) (sg_dup c H))
    (CT_comp (CT_comp (CT_cast (app_assoc [c] [c] [c]))
                      (CT_tens (CT_id [c]) (sg_dup c H)))
             (sg_dup c H)) :=
  CTEW_ax SupplySMT _ _ (SE_coassoc c H).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma supply_wire_counit_left (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_tens (sg_del c H) (CT_id [c])) (sg_dup c H))
    (CT_cast (eq_sym (app_nil_l [c]))).
Proof using Cdec.
  rewrite (CT_cast_id Cdec (eq_sym (app_nil_l [c]))).
  exact (CTEW_ax SupplySMT _ _ (SE_counit_left c H)).
Qed.

(** 本节：Right counit, shape [delta_counit_right]: axiom is
 already stated field's right-hand side. （已译） *)
Definition supply_wire_counit_right (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_tens (CT_id [c]) (sg_del c H)) (sg_dup c H))
    (CT_cast (eq_sym (app_nil_r [c]))) :=
  CTEW_ax SupplySMT _ _ (SE_counit_right c H).

(** Cocommutativity, in the shape of
    [delta_cocommutative_of_ccomon]. *)
Definition supply_wire_cocomm (c : Colour) (H : copyable c = true) :
  CTermEqW SupplySMT
    (CT_comp (CT_braid [c] [c]) (sg_dup c H))
    (sg_dup c H) :=
  CTEW_ax SupplySMT _ _ (SE_cocomm c H).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition supply_wire_comonoid_raw (c : Colour) (H : copyable c = true) :
  @Comonoid (CPresentedCat SupplySMT)
    (@braided_is_monoidal (CPresentedCat SupplySMT)
       (@symmetric_is_braided (CPresentedCat SupplySMT)
          (CPresented_Symmetric SupplySMT Cdec)))
    ([c] : list Colour) :=
  @Build_Comonoid (CPresentedCat SupplySMT)
    (@braided_is_monoidal (CPresentedCat SupplySMT)
       (@symmetric_is_braided (CPresentedCat SupplySMT)
          (CPresented_Symmetric SupplySMT Cdec)))
    ([c] : list Colour)
    (SupplyPROP_dup c H)
    (SupplyPROP_del c H)
    (supply_wire_coassoc c H)
    (supply_wire_counit_left c H)
    (supply_wire_counit_right c H).

(** 本节：The commutative packaging, at instances [SelectiveSupply]
 class Supply.v asks ([wire c ≡ [c]] nose). （已译） *)
Definition supply_wire_comonoid (c : Colour) (H : copyable c = true) :
  @CommutativeComonoid (@cprop_cat Colour SupplyPROP)
    (@cprop_symmetric Colour SupplyPROP)
    (wire (P := SupplyPROP) c) :=
  @Build_CommutativeComonoid (CPresentedCat SupplySMT)
    (CPresented_Symmetric SupplySMT Cdec)
    ([c] : list Colour)
    (supply_wire_comonoid_raw c H)
    (supply_wire_cocomm c H).

(** ** The selective supply instance *)

Definition SupplyPROP_SelectiveSupply : SelectiveSupply SupplyPROP copyable :=
  @Build_SelectiveSupply Colour SupplyPROP copyable supply_wire_comonoid.

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example SupplyPROP_ctensor_app_b_refl (cs ds : list Colour) :
  ctensor_app_b SupplyPROP cs ds = eq_refl := eq_refl.

Example SupplyPROP_cunit_nil_b_refl :
  cunit_nil_b SupplyPROP = eq_refl := eq_refl.

Example SupplyPROP_coherence_is_refl :
  @cprop_monoidal_coherence Colour SupplyPROP = eq_refl := eq_refl.

Example SupplyPROP_wire (c : Colour) :
  wire (P := SupplyPROP) c = (c :: nil) := eq_refl.

(** 本节：The empty-boundary supply unit comonoid nose (the
 [cunit_nil_b] transport vanished). （已译） *)
Example SupplyPROP_supply_list_nil :
  supply_list (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply)
    [] (all_copyable_nil copyable)
  = @CommutativeComonoid_Unit (CPresentedCat SupplySMT)
      (CPresented_Symmetric SupplySMT Cdec) := eq_refl.

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma SupplyPROP_supply_list_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  supply_list (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  = @CommutativeComonoid_Tensor (CPresentedCat SupplySMT)
      (CPresented_Symmetric SupplySMT Cdec) _ _
      (supply_wire_comonoid c H)
      (@CommutativeComonoid_Unit (CPresentedCat SupplySMT)
         (CPresented_Symmetric SupplySMT Cdec)).
Proof using Type.
  cbn.
  rewrite (UIP_dec Bool.bool_dec (proj1 (andb_prop _ _ Hc)) H).
  reflexivity.
Qed.

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example SupplyPROP_supply_list_wire_delta (c : Colour)
  (H : copyable c = true) (Hc : all_copyable copyable [c]) :
  ccomon_delta
    (supply_list (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc)
  ≈[CPresentedCat SupplySMT]
  ccomon_delta
    (@CommutativeComonoid_Tensor (CPresentedCat SupplySMT)
       (CPresented_Symmetric SupplySMT Cdec) _ _
       (supply_wire_comonoid c H)
       (@CommutativeComonoid_Unit (CPresentedCat SupplySMT)
          (CPresented_Symmetric SupplySMT Cdec))).
Proof using Type.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  reflexivity.
Qed.

(** Every supply axiom holds in [SupplyPROP], by construction. *)
Example SupplyPROP_cocomm_holds (c : Colour) (H : copyable c = true) :
  cquot SupplySMT (CT_comp (CT_braid [c] [c]) (sg_dup c H))
    ≈[CPresentedCat SupplySMT] SupplyPROP_dup c H :=
  CTEW_ax SupplySMT _ _ (SE_cocomm c H).

(*
   本节说明 Instance 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Instance SupplyPROP_CTermEqW_Equivalence
  {cs ds : list Colour} :
  RelationClasses.Equivalence (@CTermEqW Colour SupplySMT cs ds).
Proof.
  split.
  - intro t; exact (CTermEqW_refl SupplySMT t).
  - intros s t Hst; exact (CTEW_sym _ s t Hst).
  - intros s t u H1 H2; exact (CTEW_trans _ s t u H1 H2).
Qed.

#[local] Instance SupplyPROP_CT_comp_Proper
  {cs ds es : list Colour} :
  Morphisms.Proper
    (Morphisms.respectful (@CTermEqW Colour SupplySMT ds es)
       (Morphisms.respectful (@CTermEqW Colour SupplySMT cs ds)
          (@CTermEqW Colour SupplySMT cs es)))
    (@CT_comp Colour SupplyExtSig cs ds es).
Proof.
  intros f f' Hf g g' Hg.
  exact (CTEW_comp _ f f' g g' Hf Hg).
Qed.

#[local] Instance SupplyPROP_CT_tens_Proper
  {cs1 ds1 cs2 ds2 : list Colour} :
  Morphisms.Proper
    (Morphisms.respectful (@CTermEqW Colour SupplySMT cs1 ds1)
       (Morphisms.respectful (@CTermEqW Colour SupplySMT cs2 ds2)
          (@CTermEqW Colour SupplySMT (cs1 ++ cs2) (ds1 ++ ds2))))
    (@CT_tens Colour SupplyExtSig cs1 ds1 cs2 ds2).
Proof.
  intros f f' Hf g g' Hg.
  exact (CTEW_tens _ f f' g g' Hf Hg).
Qed.

(** Embedded identity/tensor bookkeeping, as rewrite rules for
    [CTermEqW]. *)
Definition supply_eqw_id_left {cs ds : list Colour}
  (f : CTerm SupplyExtSig cs ds) :
  CTermEqW SupplySMT (CT_comp (CT_id ds) f) f :=
  CTEW_termeq SupplySMT _ _ (CTE_id_left f).

Definition supply_eqw_tens_id (a b : list Colour) :
  CTermEqW SupplySMT (CT_tens (CT_id a) (CT_id b)) (CT_id (a ++ b)) :=
  CTEW_termeq SupplySMT _ _ (CTE_tens_id a b).

(** 本节：The derived singleton copy IS duplicator. （已译） *)
Theorem SupplyPROP_scopy_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  scopy (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  ≈[CPresentedCat SupplySMT] SupplyPROP_dup c H.
Proof.
  unfold scopy.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  cbn.
  (* 相关说明。 （已译） *)
  pose proof (@CTE_braid_unit_right Colour SupplyExtSig [c]) as Hb.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Hb.
  cbn in Hb.
  (* 相关说明。 （已译） *)
  pose proof (@CTE_tens_id0_right Colour SupplyExtSig
                [c] [c; c] (sg_dup c H)) as Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c; c]) eq_refl) in Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Ht.
  cbn in Ht.
  (* 相关说明。 （已译） *)
  rewrite (CT_cast_id Cdec (app_assoc [c] [] [c])).
  rewrite (CT_cast_id Cdec (eq_sym (app_assoc [] [c] []))).
  rewrite (CT_cast_id Cdec (app_assoc [c] [] [])).
  rewrite (CT_cast_id Cdec (eq_sym (app_assoc [c] [c] []))).
  rewrite (CT_cast_id Cdec (eq_sym (app_nil_l []))).
  (* Braid id, fuse 恒等 tensors, peel identities. （已译） *)
  rewrite (CTEW_termeq SupplySMT _ _ Hb).
  rewrite !supply_eqw_tens_id.
  rewrite (CTEW_termeq SupplySMT _ _ Ht).
  rewrite !supply_eqw_id_left.
  reflexivity.
Qed.

(** 本节：The derived singleton discard IS deleter. （已译） *)
Theorem SupplyPROP_sdiscard_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  sdiscard (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  ≈[CPresentedCat SupplySMT] SupplyPROP_del c H.
Proof.
  unfold sdiscard.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  cbn.
  (* 相关说明。 （已译） *)
  pose proof (@CTE_tens_id0_right Colour SupplyExtSig
                [c] [] (sg_del c H)) as Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r ([] : list Colour)) eq_refl)
    in Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Ht.
  cbn in Ht.
  (* The unit-comonoid counit is an endo-cast; kill it, then peel. *)
  rewrite (CT_cast_id Cdec (app_nil_l [])).
  rewrite (CTEW_termeq SupplySMT _ _ Ht).
  rewrite !supply_eqw_id_left.
  reflexivity.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The supply generators mention only copyable colours, so a
    non-copyable colour occurs equally often (namely zero times) on
    both boundaries of every supply generator. *)
Definition supplygen_conservative (c : Colour) (Hc : copyable c = false) :
  c_conservative Cdec SupplyGen c.
Proof using Type.
  intros cs ds g.
  destruct g as [d Hd | d Hd]; simpl.
  - (* SG_dup d : [d] -> [d; d] *)
    destruct (Cdec d c) as [e | n].
    + exfalso; subst d; rewrite Hd in Hc; discriminate.
    + reflexivity.
  - (* SG_del d : [d] -> [] *)
    destruct (Cdec d c) as [e | n].
    + exfalso; subst d; rewrite Hd in Hc; discriminate.
    + reflexivity.
Qed.

(** The extended signature conservative at [c] whenever base
 signature (the supply half always is, previous
 引理). （已译） *)
Definition supplyextsig_conservative (c : Colour) (Hc : copyable c = false)
  (HS : c_conservative Cdec S c) :
  c_conservative Cdec SupplyExtSig c :=
  fun cs ds g =>
    match g with
    | inl gS => HS cs ds gS
    | inr gG => supplygen_conservative c Hc cs ds gG
    end.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem SupplyPROP_no_fanout (c : Colour) (Hc : copyable c = false)
  (HS : c_conservative Cdec S c) :
  (([c] : list Colour) ~{SupplyPROP}~> [c; c]) -> False.
Proof using Type.
  exact (no_linear_fanout_presented Cdec SupplySMT c
           (supplyextsig_conservative c Hc HS)).
Qed.

(** No discard either, by the same counting argument. *)
Theorem SupplyPROP_no_discard (c : Colour) (Hc : copyable c = false)
  (HS : c_conservative Cdec S c) :
  (([c] : list Colour) ~{SupplyPROP}~> []) -> False.
Proof using Type.
  exact (no_linear_discard_presented Cdec SupplySMT c
           (supplyextsig_conservative c Hc HS)).
Qed.

(** Fan-out at copyable colours: the duplicator itself.  Note
    [[c] ++ [c] ≡ [c; c]] definitionally, so no cast intervenes. *)
Definition SupplyPROP_fanout (c : Colour) (H : copyable c = true) :
  ([c] : list Colour) ~{SupplyPROP}~> [c; c] :=
  cquot SupplySMT (CT_gen (inr (SG_dup c H))).

End SupplyInstance.

Arguments SupplyGen {Colour} copyable _ _ : assert.
Arguments SupplyExtSig {Colour} S copyable _ _ : assert.
Arguments SupplySMT {Colour} S copyable : assert.
Arguments SupplyPROP {Colour} Cdec S copyable : assert.
Arguments SupplyPROP_dup {Colour} S copyable c H : assert.
Arguments SupplyPROP_del {Colour} S copyable c H : assert.
Arguments supply_wire_comonoid {Colour} Cdec S copyable c H : assert.
Arguments SupplyPROP_SelectiveSupply {Colour} Cdec S copyable : assert.
Arguments supplygen_conservative {Colour} Cdec copyable c Hc cs ds g : assert.
Arguments supplyextsig_conservative {Colour} Cdec S copyable c Hc HS cs ds g
  : assert.
Arguments SupplyPROP_no_fanout {Colour} Cdec S copyable c Hc HS _ : assert.
Arguments SupplyPROP_no_discard {Colour} Cdec S copyable c Hc HS _ : assert.
Arguments SupplyPROP_fanout {Colour} Cdec S copyable c H : assert.
Arguments SupplyPROP_scopy_wire {Colour} Cdec S copyable c H Hc : assert.
Arguments SupplyPROP_sdiscard_wire {Colour} Cdec S copyable c H Hc : assert.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PureSupply.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (copyable : Colour -> bool).

(** 本节：The empty signature conservative at every colour —
 [Empty_CSig_conservative] [Construction/ColouredPROP/Linear.v],
 at section's [Cdec]. （已译） *)
Definition pure_base_conservative (c : Colour) :
  c_conservative Cdec Empty_CSig c :=
  Empty_CSig_conservative Cdec c.

(** A wire of the pure supply PROP supports a fan-out iff its colour is
    copyable. *)
Theorem fanout_iff (c : Colour) :
  inhabited
    (([c] : list Colour) ~{SupplyPROP Cdec Empty_CSig copyable}~> [c; c])
  <-> copyable c = true.
Proof using Type.
  split.
  - intros [t].
    destruct (copyable c) eqn:Hc.
    + reflexivity.
    + exfalso.
      exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hc
               (pure_base_conservative c) t).
  - intro H.
    exact (inhabits (SupplyPROP_fanout Cdec Empty_CSig copyable c H)).
Qed.

(** The discard-side 镜像, symmetry. （已译） *)
Theorem discard_iff (c : Colour) :
  inhabited
    (([c] : list Colour) ~{SupplyPROP Cdec Empty_CSig copyable}~> [])
  <-> copyable c = true.
Proof using Type.
  split.
  - intros [t].
    destruct (copyable c) eqn:Hc.
    + reflexivity.
    + exfalso.
      exact (SupplyPROP_no_discard Cdec Empty_CSig copyable c Hc
               (pure_base_conservative c) t).
  - intro H.
    exact (inhabits
             (cquot (SupplySMT Empty_CSig copyable)
                (CT_gen (inr (SG_del copyable c H))))).
Qed.

End PureSupply.

Arguments pure_base_conservative {Colour} Cdec c cs ds g : assert.
Arguments fanout_iff {Colour} Cdec copyable c : assert.
Arguments discard_iff {Colour} Cdec copyable c : assert.
