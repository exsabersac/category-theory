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

(** * The free selective supply: a presented coloured PROP with
      per-wire duplicators and deleters *)

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

(** The generators as terms.  [[c] ++ [c] ≡ [c; c]] definitionally,
    so [sg_dup] also inhabits the tensor-shaped boundary on the
    nose. *)
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

  (** Coassociativity.  The right-hand side carries the [from] of the
      presented associator at [([c], [c], [c])]: the single
      [app_assoc [c] [c] [c]] cast. *)
  | SE_coassoc (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c; c; c]
        (CT_comp (CT_tens (sg_dup c H) (CT_id [c])) (sg_dup c H))
        (CT_comp (CT_comp (CT_cast (app_assoc [c] [c] [c]))
                          (CT_tens (CT_id [c]) (sg_dup c H)))
                 (sg_dup c H))

  (** Left counit law.  Cast-free: [[] ++ [c] ≡ [c]] definitionally,
      so deleting the left copy is the identity wire on the nose. *)
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

  (** Cocommutativity.  Cast-free: [CT_braid [c] [c]] is the
      presented braid on the nose. *)
  | SE_cocomm (c : Colour) (H : copyable c = true) :
      SupplyEqs [c] [c; c]
        (CT_comp (CT_braid [c] [c]) (sg_dup c H))
        (sg_dup c H).

(** ** The theory and its presented coloured PROP *)

Definition SupplySMT : CSMT Colour :=
  Build_CSMT Colour SupplyExtSig SupplyEqs.

(** The THIRD [ColouredPROP] instance of the library. *)
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

(** Right counit, in the shape of [delta_counit_right]: the axiom is
    already stated with the field's right-hand side. *)
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

(** The commutative packaging, at the instances the [SelectiveSupply]
    class of Supply.v asks for ([wire c ≡ [c]] on the nose). *)
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

(** The empty-boundary supply is the unit comonoid on the nose (the
    [cunit_nil_b] transport vanished). *)
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

(** The derived singleton copy IS the duplicator. *)
Theorem SupplyPROP_scopy_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  scopy (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  ≈[CPresentedCat SupplySMT] SupplyPROP_dup c H.
Proof.
  unfold scopy.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  cbn.
  (* The unit braid collapses (its [eq_rect] transport is over an
     endo-equality at the concrete word [[c]]). *)
  pose proof (@CTE_braid_unit_right Colour SupplyExtSig [c]) as Hb.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Hb.
  cbn in Hb.
  (* The strict right-unit law at the duplicator. *)
  pose proof (@CTE_tens_id0_right Colour SupplyExtSig
                [c] [c; c] (sg_dup c H)) as Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c; c]) eq_refl) in Ht.
  rewrite (UIP_dec (list_eq_dec Cdec) (app_nil_r [c]) eq_refl) in Ht.
  cbn in Ht.
  (* Kill the five endo-casts (all boundary words are concrete). *)
  rewrite (CT_cast_id Cdec (app_assoc [c] [] [c])).
  rewrite (CT_cast_id Cdec (eq_sym (app_assoc [] [c] []))).
  rewrite (CT_cast_id Cdec (app_assoc [c] [] [])).
  rewrite (CT_cast_id Cdec (eq_sym (app_assoc [c] [c] []))).
  rewrite (CT_cast_id Cdec (eq_sym (app_nil_l []))).
  (* Braid to id, fuse the identity tensors, peel the identities. *)
  rewrite (CTEW_termeq SupplySMT _ _ Hb).
  rewrite !supply_eqw_tens_id.
  rewrite (CTEW_termeq SupplySMT _ _ Ht).
  rewrite !supply_eqw_id_left.
  reflexivity.
Qed.

(** The derived singleton discard IS the deleter. *)
Theorem SupplyPROP_sdiscard_wire (c : Colour) (H : copyable c = true)
  (Hc : all_copyable copyable [c]) :
  sdiscard (P := SupplyPROP) (SS := SupplyPROP_SelectiveSupply) [c] Hc
  ≈[CPresentedCat SupplySMT] SupplyPROP_del c H.
Proof.
  unfold sdiscard.
  rewrite (SupplyPROP_supply_list_wire c H Hc).
  cbn.
  (* The strict right-unit law at the deleter. *)
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

(** The extended signature is conservative at [c] whenever the base
    signature is (the supply half always is, by the previous
    lemma). *)
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

(** The empty signature is conservative at every colour —
    [Empty_CSig_conservative] of [Construction/ColouredPROP/Linear.v],
    at the section's [Cdec]. *)
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

(** The discard-side mirror, for symmetry. *)
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
