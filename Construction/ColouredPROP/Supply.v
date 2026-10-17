Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Tensor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Presentation.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Bool.Bool.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/copy-discard+category
   Reference: Fong & Spivak, "Supplying bells and whistles in symmetric
   Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Supply.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(** The coloured-PROP-对象 [⟦cs⟧c], in
 [Construction/ColouredPROP.v] (whose notation section-local
 there must re-declared per file). （已译） *)
Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(** ** MP/MB mediation *)

(** Tensor-on-对象 concatenation, transported the
 braided/symmetric monoidal path where comonoids live. （已译） *)
Definition ctensor_app_b (cs ds : list Colour) :
  ((⟦cs⟧c ⨂[MBc P] ⟦ds⟧c)%object = ⟦cs ++ ds⟧c) :=
  match cprop_monoidal_coherence P in _ = M
        return ((⟦cs⟧c ⨂[M] ⟦ds⟧c)%object = ⟦cs ++ ds⟧c)
  with eq_refl => cprop_tensor_app cs ds end.

(** The unit 对象 empty word, braided/symmetric
 monoidal path. （已译） *)
Definition cunit_nil_b : @I P (MBc P) = ⟦[]⟧c :=
  match cprop_monoidal_coherence P in _ = M
        return (@I P M = ⟦[]⟧c)
  with eq_refl => cprop_unit_nil end.

(** Transparent congruence of [⨂[MBc P]] on object equalities (the
    [MBc]-side sibling of Interp.v's [ctensor_obj_eq]; kept as nested
    [match]es so that it computes to [eq_refl] on [eq_refl]s). *)
Definition ctensor2_b {x x' y y' : P} (e : x = x') (e' : y = y') :
  ((x ⨂[MBc P] y)%object = (x' ⨂[MBc P] y')%object) :=
  match e in _ = u return ((x ⨂[MBc P] y)%object = (u ⨂[MBc P] y')%object) with
  | eq_refl =>
      match e' in _ = v
            return ((x ⨂[MBc P] y)%object = (x ⨂[MBc P] v)%object) with
      | eq_refl => eq_refl
      end
  end.

(** ** Copyability evidence *)

Context (copyable : Colour -> bool).

(** Every colour word copyable. A boolean equation, so the
 evidence 证明-irrelevant without any axioms. （已译） *)
Definition all_copyable (cs : list Colour) : Prop :=
  forallb copyable cs = true.

Definition all_copyable_nil : all_copyable [] := eq_refl.

Lemma all_copyable_single (c : Colour) (H : copyable c = true) :
  all_copyable [c].
Proof.
  unfold all_copyable; simpl.
  rewrite H; reflexivity.
Qed.

Lemma all_copyable_app (cs ds : list Colour) :
  all_copyable cs -> all_copyable ds -> all_copyable (cs ++ ds).
Proof.
  unfold all_copyable; intros Hcs Hds.
  rewrite forallb_app, Hcs, Hds; reflexivity.
Qed.

Lemma all_copyable_app_l (cs ds : list Colour) :
  all_copyable (cs ++ ds) -> all_copyable cs.
Proof.
  unfold all_copyable; intros H.
  rewrite forallb_app in H.
  exact (proj1 (andb_prop _ _ H)).
Qed.

Lemma all_copyable_app_r (cs ds : list Colour) :
  all_copyable (cs ++ ds) -> all_copyable ds.
Proof.
  unfold all_copyable; intros H.
  rewrite forallb_app in H.
  exact (proj2 (andb_prop _ _ H)).
Qed.

(** Unconditional 证明 irrelevance copyability evidence — the
 payoff [bool]-valued copyability (no colour decidability
 needed). （已译） *)
Lemma all_copyable_irrelevant (cs : list Colour)
  (H1 H2 : all_copyable cs) : H1 = H2.
Proof. exact (UIP_dec Bool.bool_dec H1 H2). Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class SelectiveSupply : Type := {
  supply_wire (c : Colour) :
    copyable c = true ->
    @CommutativeComonoid (@cprop_cat Colour P) (@cprop_symmetric Colour P)
      (wire c)
}.

(** ** The derived boundary supply *)

(** Leibniz transport commutative-comonoid structure along an
 对象 equality. Transparent, so at instances where the
 equality computes [eq_refl] transport vanishes. （已译） *)
Definition ccomonoid_transport {X Y : P} (e : X = Y) :
  @CommutativeComonoid P (@cprop_symmetric Colour P) X ->
  @CommutativeComonoid P (@cprop_symmetric Colour P) Y :=
  match e in _ = Z
        return @CommutativeComonoid P (@cprop_symmetric Colour P) X ->
               @CommutativeComonoid P (@cprop_symmetric Colour P) Z
  with eq_refl => fun M => M end.

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint supply_list `{SS : SelectiveSupply} (cs : list Colour) :
  all_copyable cs ->
  @CommutativeComonoid P (@cprop_symmetric Colour P) ⟦cs⟧c :=
  match cs return all_copyable cs ->
                  @CommutativeComonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
  with
  | [] => fun _ =>
      ccomonoid_transport cunit_nil_b
        (@CommutativeComonoid_Unit P (@cprop_symmetric Colour P))
  | c :: cs' => fun H =>
      ccomonoid_transport (ctensor_app_b [c] cs')
        (@CommutativeComonoid_Tensor P (@cprop_symmetric Colour P) _ _
           (supply_wire c (proj1 (andb_prop _ _ H)))
           (supply_list cs' (proj2 (andb_prop _ _ H))))
  end.

(** Copy and discard on a fully copyable boundary. *)
Definition scopy `{SS : SelectiveSupply} (cs : list Colour)
  (H : all_copyable cs) :
  ⟦cs⟧c ~{P}~> (⟦cs⟧c ⨂[MBc P] ⟦cs⟧c)%object :=
  ccomon_delta (supply_list cs H).

Definition sdiscard `{SS : SelectiveSupply} (cs : list Colour)
  (H : all_copyable cs) :
  ⟦cs⟧c ~{P}~> @I P (MBc P) :=
  ccomon_epsilon (supply_list cs H).

(** 本节：The derived supply does not depend copyability evidence —
 Leibniz equality, not merely [≈]. （已译） *)
Lemma supply_list_irr `{SS : SelectiveSupply} (cs : list Colour)
  (H1 H2 : all_copyable cs) :
  supply_list cs H1 = supply_list cs H2.
Proof.
  rewrite (all_copyable_irrelevant cs H1 H2); reflexivity.
Qed.

Lemma scopy_irr `{SS : SelectiveSupply} (cs : list Colour)
  (H1 H2 : all_copyable cs) :
  scopy cs H1 = scopy cs H2.
Proof.
  unfold scopy; rewrite (supply_list_irr cs H1 H2); reflexivity.
Qed.

Lemma sdiscard_irr `{SS : SelectiveSupply} (cs : list Colour)
  (H1 H2 : all_copyable cs) :
  sdiscard cs H1 = sdiscard cs H2.
Proof.
  unfold sdiscard; rewrite (supply_list_irr cs H1 H2); reflexivity.
Qed.

End Supply.

Arguments ctensor_app_b {Colour} P cs ds : assert.
Arguments cunit_nil_b {Colour} P : assert.
Arguments ctensor2_b {Colour} P {x x' y y'} e e' : assert.
Arguments all_copyable {Colour} copyable cs : assert.
Arguments all_copyable_nil {Colour} copyable : assert.
Arguments all_copyable_single {Colour} copyable c H : assert.
Arguments all_copyable_app {Colour} copyable cs ds _ _ : assert.
Arguments all_copyable_app_l {Colour} copyable cs ds _ : assert.
Arguments all_copyable_app_r {Colour} copyable cs ds _ : assert.
Arguments all_copyable_irrelevant {Colour} copyable cs H1 H2 : assert.
Arguments SelectiveSupply {Colour} P copyable : assert.
Arguments supply_wire {Colour P copyable SelectiveSupply} c _ : assert.
Arguments ccomonoid_transport {Colour} P {X Y} e _ : assert.
Arguments supply_list {Colour P copyable SS} cs H : assert.
Arguments scopy {Colour P copyable SS} cs H : assert.
Arguments sdiscard {Colour P copyable SS} cs H : assert.
Arguments supply_list_irr {Colour P copyable SS} cs H1 H2 : assert.
Arguments scopy_irr {Colour P copyable SS} cs H1 H2 : assert.
Arguments sdiscard_irr {Colour P copyable SS} cs H1 H2 : assert.

(* ------------------------------------------------------------------ *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example ctensor_app_b_free_is_refl {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (cs ds : list Colour) :
  ctensor_app_b (FreeColouredPROP S Cdec) cs ds = eq_refl := eq_refl.

Example cunit_nil_b_free_is_refl {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) :
  cunit_nil_b (FreeColouredPROP S Cdec) = eq_refl := eq_refl.

Example ctensor_app_b_presented_is_refl {Colour : Type} (E : CSMT Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) (cs ds : list Colour) :
  ctensor_app_b (CPresentedColouredPROP E Cdec) cs ds = eq_refl := eq_refl.

Example cunit_nil_b_presented_is_refl {Colour : Type} (E : CSMT Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d}) :
  cunit_nil_b (CPresentedColouredPROP E Cdec) = eq_refl := eq_refl.

(* ------------------------------------------------------------------ *)

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Transport a left-unitor-shaped object equality along an equality
    of [Monoidal] records. *)
Definition tmon_unitl_obj {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x : C)
  (e : ((@I C M1) ⨂[M1] x)%object = x) :
  ((@I C M2) ⨂[M2] x)%object = x :=
  match E in _ = m return (((@I C m) ⨂[m] x)%object = x) with
  | eq_refl => e
  end.

Lemma tmon_unitl_cast {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x : C)
  (e : ((@I C M1) ⨂[M1] x)%object = x) :
  to (@unit_left C M1 x) ≈ id_cast e →
  to (@unit_left C M2 x) ≈ id_cast (tmon_unitl_obj E x e).
Proof.
  destruct E.
  intro He.
  exact He.
Qed.

(** Transport an associator-shaped object equality. *)
Definition tmon_assoc_obj {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x y z : C)
  (e : ((x ⨂[M1] y) ⨂[M1] z)%object = (x ⨂[M1] (y ⨂[M1] z))%object) :
  ((x ⨂[M2] y) ⨂[M2] z)%object = (x ⨂[M2] (y ⨂[M2] z))%object :=
  match E in _ = m
        return (((x ⨂[m] y) ⨂[m] z)%object = (x ⨂[m] (y ⨂[m] z))%object)
  with
  | eq_refl => e
  end.

Lemma tmon_assoc_cast {C : Category} {M1 M2 : @Monoidal C}
  (E : M1 = M2) (x y z : C)
  (e : ((x ⨂[M1] y) ⨂[M1] z)%object = (x ⨂[M1] (y ⨂[M1] z))%object) :
  to (@tensor_assoc C M1 x y z) ≈ id_cast e →
  to (@tensor_assoc C M2 x y z) ≈ id_cast (tmon_assoc_obj E x y z e).
Proof.
  destruct E.
  intro He.
  exact He.
Qed.

(** If [to] direction 同构 cast, [from]
 direction cast along symmetric equality. （已译） *)
Lemma iso_from_id_cast {C : Category} {x y : C} (i : x ≅ y) (e : x = y) :
  to i ≈ id_cast e → from i ≈ id_cast (eq_sym e).
Proof.
  intro H.
  rewrite <- (id_right (from i)).
  rewrite <- (id_cast_inv_r e).
  rewrite comp_assoc.
  rewrite <- H.
  rewrite iso_from_to.
  apply id_left.
Qed.

(* ------------------------------------------------------------------ *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TensorComonoidCoherence.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Lemma tensor_delta_unit_l_raw {y : C} (dy : y ~> (y ⨂ y)%object) :
  (to (@unit_left C _ y) ⨂ to (@unit_left C _ y))
    ∘ (mid_swap_inv I y ∘ ((@unit_left C _ I)⁻¹ ⨂ dy))
    ≈ dy ∘ to (@unit_left C _ y).
Proof.
  rewrite mid_swap_inv_swap_inner.
  assert (E : ((@unit_left C _ I)⁻¹ ⨂ dy)
                ≈ ((@unit_left C _ I)⁻¹ ⨂ id[(y ⨂ y)%object])
                    ∘ (id[I] ⨂ dy)).
  { rewrite <- bimap_comp.
    now rewrite id_right, id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite swap_inner_unit_left.
  symmetry.
  apply to_unit_left_natural.
Qed.

Lemma tensor_delta_assoc_raw {x y z : C}
  (dx : x ~> (x ⨂ x)%object) (dy : y ~> (y ⨂ y)%object)
  (dz : z ~> (z ⨂ z)%object) :
  (to (@tensor_assoc C _ x y z) ⨂ to (@tensor_assoc C _ x y z))
    ∘ (mid_swap_inv ((x ⨂ y)%object) z
         ∘ ((mid_swap_inv x y ∘ (dx ⨂ dy)) ⨂ dz))
    ≈ (mid_swap_inv x ((y ⨂ z)%object)
         ∘ (dx ⨂ (mid_swap_inv y z ∘ (dy ⨂ dz))))
        ∘ to (@tensor_assoc C _ x y z).
Proof.
  rewrite !mid_swap_inv_swap_inner.
  assert (EL : ((swap_inner x x y y ∘ (dx ⨂ dy)) ⨂ dz)
                 ≈ (swap_inner x x y y ⨂ id[(z ⨂ z)%object])
                     ∘ ((dx ⨂ dy) ⨂ dz)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  assert (ER : (dx ⨂ (swap_inner y y z z ∘ (dy ⨂ dz)))
                 ≈ (id[(x ⨂ x)%object] ⨂ swap_inner y y z z)
                     ∘ (dx ⨂ (dy ⨂ dz))).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite EL, ER; clear EL ER.
  rewrite <- !comp_assoc.
  rewrite to_tensor_assoc_natural.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  symmetry.
  apply swap_inner_assoc.
Qed.

Lemma tensor_epsilon_assoc_raw {x y z : C}
  (ex : x ~> I) (ey : y ~> I) (ez : z ~> I) :
  to (@unit_left C _ I) ∘ ((to (@unit_left C _ I) ∘ (ex ⨂ ey)) ⨂ ez)
    ≈ (to (@unit_left C _ I)
         ∘ (ex ⨂ (to (@unit_left C _ I) ∘ (ey ⨂ ez))))
        ∘ to (@tensor_assoc C _ x y z).
Proof.
  assert (EL : ((to (@unit_left C _ I) ∘ (ex ⨂ ey)) ⨂ ez)
                 ≈ (to (@unit_left C _ I) ⨂ id[I]) ∘ ((ex ⨂ ey) ⨂ ez)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  assert (ER : (ex ⨂ (to (@unit_left C _ I) ∘ (ey ⨂ ez)))
                 ≈ (id[I] ⨂ to (@unit_left C _ I)) ∘ (ex ⨂ (ey ⨂ ez))).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite EL, ER; clear EL ER.
  rewrite <- !comp_assoc.
  rewrite to_tensor_assoc_natural.
  rewrite !comp_assoc.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite <- triangle_identity.
  rewrite unit_identity.
  reflexivity.
Qed.

End TensorComonoidCoherence.

(* ------------------------------------------------------------------ *)

(** ** The cast kit at [MBc P] *)

Section SupplyCastKit.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(** 本节：A tensor casts at [MBc P] cast along paired
 equality [ctensor2_b]. （已译） *)
Lemma cbimap_cast_b {x x' y y' : P} (e : x = x') (e' : y = y') :
  (id_cast e ⨂[MBc P] id_cast e') ≈ id_cast (ctensor2_b P e e').
Proof.
  destruct e, e'.
  exact (@bimap_id_id P P P (@tensor P (MBc P)) x y).
Qed.

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cunitl_obj_b (x : P) :
  ((@I P (MBc P)) ⨂[MBc P] x)%object = x :=
  tmon_unitl_obj (@cprop_monoidal_coherence Colour P) x
    (@strict_unit_left_obj P (@cprop_strict Colour P) x).

Lemma cunitl_cast_b (x : P) :
  to (@unit_left P (MBc P) x) ≈ id_cast (cunitl_obj_b x).
Proof.
  apply (tmon_unitl_cast (@cprop_monoidal_coherence Colour P) x
           (@strict_unit_left_obj P (@cprop_strict Colour P) x)).
  symmetry.
  apply (cstrict_unitl_cast P x).
Qed.

Lemma cunitl_cast_from_b (x : P) :
  from (@unit_left P (MBc P) x) ≈ id_cast (eq_sym (cunitl_obj_b x)).
Proof.
  apply iso_from_id_cast.
  apply cunitl_cast_b.
Qed.

Definition cassoc_obj_b (x y z : P) :
  ((x ⨂[MBc P] y) ⨂[MBc P] z)%object
  = (x ⨂[MBc P] (y ⨂[MBc P] z))%object :=
  tmon_assoc_obj (@cprop_monoidal_coherence Colour P) x y z
    (@strict_assoc_obj P (@cprop_strict Colour P) x y z).

Lemma cassoc_cast_b (x y z : P) :
  to (@tensor_assoc P (MBc P) x y z) ≈ id_cast (cassoc_obj_b x y z).
Proof.
  apply (tmon_assoc_cast (@cprop_monoidal_coherence Colour P) x y z
           (@strict_assoc_obj P (@cprop_strict Colour P) x y z)).
  symmetry.
  apply (cstrict_assoc_cast P x y z).
Qed.

Lemma cassoc_cast_from_b (x y z : P) :
  from (@tensor_assoc P (MBc P) x y z)
    ≈ id_cast (eq_sym (cassoc_obj_b x y z)).
Proof.
  apply iso_from_id_cast.
  apply cassoc_cast_b.
Qed.

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma ccomonoid_transport_delta {X Y : P} (e : X = Y)
  (M : @CommutativeComonoid P (@cprop_symmetric Colour P) X) :
  ccomon_delta (ccomonoid_transport P e M)
  = hom_cast e (ctensor2_b P e e) (ccomon_delta M).
Proof.
  destruct e.
  reflexivity.
Qed.

Lemma ccomonoid_transport_epsilon {X Y : P} (e : X = Y)
  (M : @CommutativeComonoid P (@cprop_symmetric Colour P) X) :
  ccomon_epsilon (ccomonoid_transport P e M)
  = hom_cast e eq_refl (ccomon_epsilon M).
Proof.
  destruct e.
  reflexivity.
Qed.

(* * *** The canonical 态射, respelled through [ccomon_*]

 Definitional unfoldings [canonical_tensor_delta]/[epsilon]
 (Hypergraph.v) 进入 raw shapes supply theorems chase. （已译） *)

Lemma canonical_tensor_delta_ccomon {X Y : P}
  (MX : @CommutativeComonoid P (@cprop_symmetric Colour P) X)
  (MY : @CommutativeComonoid P (@cprop_symmetric Colour P) Y) :
  @canonical_tensor_delta P (@cprop_symmetric Colour P) X Y MX MY
  = @mid_swap_inv P (@cprop_symmetric Colour P) X Y
      ∘ (ccomon_delta MX ⨂[MBc P] ccomon_delta MY).
Proof.
  reflexivity.
Qed.

Lemma canonical_tensor_epsilon_ccomon {X Y : P}
  (MX : @CommutativeComonoid P (@cprop_symmetric Colour P) X)
  (MY : @CommutativeComonoid P (@cprop_symmetric Colour P) Y) :
  @canonical_tensor_epsilon P (@cprop_symmetric Colour P) X Y MX MY
  = to (@unit_left P (MBc P) (@I P (MBc P)))
      ∘ (ccomon_epsilon MX ⨂[MBc P] ccomon_epsilon MY).
Proof.
  reflexivity.
Qed.

End SupplyCastKit.

Arguments cbimap_cast_b {Colour} P {x x' y y'} e e' : assert.
Arguments cunitl_obj_b {Colour} P x : assert.
Arguments cunitl_cast_b {Colour} P x : assert.
Arguments cunitl_cast_from_b {Colour} P x : assert.
Arguments cassoc_obj_b {Colour} P x y z : assert.
Arguments cassoc_cast_b {Colour} P x y z : assert.
Arguments cassoc_cast_from_b {Colour} P x y z : assert.
Arguments ccomonoid_transport_delta {Colour} P {X Y} e M : assert.
Arguments ccomonoid_transport_epsilon {Colour} P {X Y} e M : assert.
Arguments canonical_tensor_delta_ccomon {Colour} P {X Y} MX MY : assert.
Arguments canonical_tensor_epsilon_ccomon {Colour} P {X Y} MX MY : assert.

(* ------------------------------------------------------------------ *)

(* 相关说明。 （已译） *)

Section SupplyCoherence.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).
Context {OD : @ObjDecEq P}.

Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：Unit absorption canonical delta: casting canonical
 tensor delta (the transported unit comonoid's delta) [dy]
 along unitor-shaped equality [dy] itself. （已译） *)
Lemma supply_delta_unit_general {n y : P}
  (u : @I P (MBc P) = n)
  (U2 : ((@I P (MBc P)) ⨂[MBc P] (@I P (MBc P)))%object
        = (n ⨂[MBc P] n)%object)
  (dy : y ~{P}~> (y ⨂[MBc P] y)%object)
  (e : (n ⨂[MBc P] y)%object = y)
  (E2 : ((n ⨂[MBc P] y) ⨂[MBc P] (n ⨂[MBc P] y))%object
        = (y ⨂[MBc P] y)%object) :
  hom_cast e E2
    (@mid_swap_inv P (@cprop_symmetric Colour P) n y
       ∘ (hom_cast u U2 (from (@unit_left P (MBc P) (@I P (MBc P))))
          ⨂[MBc P] dy))
    ≈ dy.
Proof using OD P.
  destruct u.
  rewrite (obj_uip U2 eq_refl).
  rewrite hom_cast_refl.
  rewrite (obj_uip e (cunitl_obj_b P y)).
  rewrite (obj_uip E2 (ctensor2_b P (cunitl_obj_b P y) (cunitl_obj_b P y))).
  rewrite hom_cast_decompose.
  rewrite <- (cbimap_cast_b P).
  rewrite <- !(cunitl_cast_b P).
  rewrite <- (cunitl_cast_from_b P).
  rewrite (tensor_delta_unit_l_raw (S := @cprop_symmetric Colour P) dy).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(** 本节：Unit absorption canonical epsilon. （已译） *)
Lemma supply_epsilon_unit_general {n y : P}
  (u : @I P (MBc P) = n)
  (ey : y ~{P}~> @I P (MBc P))
  (e : (n ⨂[MBc P] y)%object = y) :
  hom_cast e eq_refl
    (to (@unit_left P (MBc P) (@I P (MBc P)))
       ∘ (hom_cast u eq_refl id[@I P (MBc P)] ⨂[MBc P] ey))
    ≈ ey.
Proof using OD P.
  destruct u.
  rewrite hom_cast_refl.
  rewrite (obj_uip e (cunitl_obj_b P y)).
  rewrite hom_cast_decompose.
  rewrite id_cast_refl, id_left.
  rewrite <- (cunitl_cast_from_b P).
  rewrite <- to_unit_left_natural.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Qed.

(** 本节：Associativity canonical delta: two cast-mediated
 iterations canonical tensor delta agree. （已译） *)
Lemma supply_delta_assoc_general {x y z v w s : P}
  (dx : x ~{P}~> (x ⨂[MBc P] x)%object)
  (dy : y ~{P}~> (y ⨂[MBc P] y)%object)
  (dz : z ~{P}~> (z ⨂[MBc P] z)%object)
  (eyz : (y ⨂[MBc P] z)%object = v)
  (Eyz : ((y ⨂[MBc P] z) ⨂[MBc P] (y ⨂[MBc P] z))%object
         = (v ⨂[MBc P] v)%object)
  (exv : (x ⨂[MBc P] v)%object = s)
  (Exv : ((x ⨂[MBc P] v) ⨂[MBc P] (x ⨂[MBc P] v))%object
         = (s ⨂[MBc P] s)%object)
  (exy : (x ⨂[MBc P] y)%object = w)
  (Exy : ((x ⨂[MBc P] y) ⨂[MBc P] (x ⨂[MBc P] y))%object
         = (w ⨂[MBc P] w)%object)
  (ewz : (w ⨂[MBc P] z)%object = s)
  (Ewz : ((w ⨂[MBc P] z) ⨂[MBc P] (w ⨂[MBc P] z))%object
         = (s ⨂[MBc P] s)%object) :
  hom_cast exv Exv
    (@mid_swap_inv P (@cprop_symmetric Colour P) x v
       ∘ (dx ⨂[MBc P]
          hom_cast eyz Eyz
            (@mid_swap_inv P (@cprop_symmetric Colour P) y z
               ∘ (dy ⨂[MBc P] dz))))
    ≈ hom_cast ewz Ewz
        (@mid_swap_inv P (@cprop_symmetric Colour P) w z
           ∘ (hom_cast exy Exy
                (@mid_swap_inv P (@cprop_symmetric Colour P) x y
                   ∘ (dx ⨂[MBc P] dy))
              ⨂[MBc P] dz)).
Proof using OD P.
  destruct eyz.
  rewrite (obj_uip Eyz eq_refl).
  rewrite hom_cast_refl.
  destruct exy.
  rewrite (obj_uip Exy eq_refl).
  rewrite hom_cast_refl.
  destruct ewz.
  rewrite (obj_uip Ewz eq_refl).
  rewrite hom_cast_refl.
  rewrite (obj_uip exv (eq_sym (cassoc_obj_b P x y z))).
  rewrite (obj_uip Exv (ctensor2_b P (eq_sym (cassoc_obj_b P x y z))
                                     (eq_sym (cassoc_obj_b P x y z)))).
  rewrite hom_cast_decompose.
  rewrite <- (cbimap_cast_b P).
  rewrite <- !(cassoc_cast_from_b P).
  rewrite (id_cast_irr (eq_sym (eq_sym (cassoc_obj_b P x y z)))
                       (cassoc_obj_b P x y z)).
  rewrite <- (cassoc_cast_b P).
  rewrite <- comp_assoc.
  rewrite <- (tensor_delta_assoc_raw (S := @cprop_symmetric Colour P)
                dx dy dz).
  rewrite (comp_assoc
             (from (@tensor_assoc P (MBc P) x y z)
                ⨂[MBc P] from (@tensor_assoc P (MBc P) x y z))
             (to (@tensor_assoc P (MBc P) x y z)
                ⨂[MBc P] to (@tensor_assoc P (MBc P) x y z))).
  rewrite <- bimap_comp.
  rewrite !iso_from_to.
  rewrite bimap_id_id.
  apply id_left.
Qed.

(** 本节：Associativity canonical epsilon. （已译） *)
Lemma supply_epsilon_assoc_general {x y z v w s : P}
  (ex : x ~{P}~> @I P (MBc P))
  (ey : y ~{P}~> @I P (MBc P))
  (ez : z ~{P}~> @I P (MBc P))
  (eyz : (y ⨂[MBc P] z)%object = v)
  (exv : (x ⨂[MBc P] v)%object = s)
  (exy : (x ⨂[MBc P] y)%object = w)
  (ewz : (w ⨂[MBc P] z)%object = s) :
  hom_cast exv eq_refl
    (to (@unit_left P (MBc P) (@I P (MBc P)))
       ∘ (ex ⨂[MBc P]
          hom_cast eyz eq_refl
            (to (@unit_left P (MBc P) (@I P (MBc P)))
               ∘ (ey ⨂[MBc P] ez))))
    ≈ hom_cast ewz eq_refl
        (to (@unit_left P (MBc P) (@I P (MBc P)))
           ∘ (hom_cast exy eq_refl
                (to (@unit_left P (MBc P) (@I P (MBc P)))
                   ∘ (ex ⨂[MBc P] ey))
              ⨂[MBc P] ez)).
Proof using OD P.
  destruct eyz.
  rewrite hom_cast_refl.
  destruct exy.
  rewrite hom_cast_refl.
  destruct ewz.
  rewrite hom_cast_refl.
  rewrite (obj_uip exv (eq_sym (cassoc_obj_b P x y z))).
  rewrite hom_cast_decompose.
  rewrite id_cast_refl, id_left.
  rewrite (id_cast_irr (eq_sym (eq_sym (cassoc_obj_b P x y z)))
                       (cassoc_obj_b P x y z)).
  rewrite <- (cassoc_cast_b P).
  symmetry.
  apply (tensor_epsilon_assoc_raw (S := @cprop_symmetric Colour P)
           ex ey ez).
Qed.

(* 相关说明。 （已译） *)

Context (copyable : Colour -> bool).
Context {SS : SelectiveSupply P copyable}.

(** Per-colour copyability evidence is unique, like [all_copyable]'s. *)
Lemma copyable_irrelevant (c : Colour) (p q : copyable c = true) : p = q.
Proof.
  apply (UIP_dec Bool.bool_dec).
Qed.

(** 本节：Each equation unfolds one [supply_list] constructor case and
 computes transported projection through
 [ccomonoid_transport_delta]/[epsilon]; residue is
 definitional. （已译） *)

Lemma supply_list_delta_nil (H : all_copyable copyable []) :
  ccomon_delta (supply_list [] H)
  = hom_cast (cunit_nil_b P)
      (ctensor2_b P (cunit_nil_b P) (cunit_nil_b P))
      (from (@unit_left P (MBc P) (@I P (MBc P)))).
Proof.
  exact (ccomonoid_transport_delta P (cunit_nil_b P)
           (@CommutativeComonoid_Unit P (@cprop_symmetric Colour P))).
Qed.

Lemma supply_list_epsilon_nil (H : all_copyable copyable []) :
  ccomon_epsilon (supply_list [] H)
  = hom_cast (cunit_nil_b P) eq_refl id[@I P (MBc P)].
Proof.
  exact (ccomonoid_transport_epsilon P (cunit_nil_b P)
           (@CommutativeComonoid_Unit P (@cprop_symmetric Colour P))).
Qed.

Lemma supply_list_delta_cons (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l)) :
  ccomon_delta (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l)
      (ctensor2_b P (ctensor_app_b P [c] l) (ctensor_app_b P [c] l))
      (@mid_swap_inv P (@cprop_symmetric Colour P) (@wire Colour P c) ⟦l⟧c
         ∘ (ccomon_delta (supply_wire c (proj1 (andb_prop _ _ H)))
            ⨂[MBc P]
            ccomon_delta (supply_list l (proj2 (andb_prop _ _ H))))).
Proof.
  exact (ccomonoid_transport_delta P (ctensor_app_b P [c] l)
           (@CommutativeComonoid_Tensor P (@cprop_symmetric Colour P) _ _
              (supply_wire c (proj1 (andb_prop _ _ H)))
              (supply_list l (proj2 (andb_prop _ _ H))))).
Qed.

Lemma supply_list_epsilon_cons (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l)) :
  ccomon_epsilon (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l) eq_refl
      (to (@unit_left P (MBc P) (@I P (MBc P)))
         ∘ (ccomon_epsilon (supply_wire c (proj1 (andb_prop _ _ H)))
            ⨂[MBc P]
            ccomon_epsilon (supply_list l (proj2 (andb_prop _ _ H))))).
Proof.
  exact (ccomonoid_transport_epsilon P (ctensor_app_b P [c] l)
           (@CommutativeComonoid_Tensor P (@cprop_symmetric Colour P) _ _
              (supply_wire c (proj1 (andb_prop _ _ H)))
              (supply_list l (proj2 (andb_prop _ _ H))))).
Qed.

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma supply_list_delta_cons_any (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l))
  (p : copyable c = true) (q : all_copyable copyable l) :
  ccomon_delta (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l)
      (ctensor2_b P (ctensor_app_b P [c] l) (ctensor_app_b P [c] l))
      (@mid_swap_inv P (@cprop_symmetric Colour P) (@wire Colour P c) ⟦l⟧c
         ∘ (ccomon_delta (supply_wire c p)
            ⨂[MBc P] ccomon_delta (supply_list l q))).
Proof.
  rewrite (copyable_irrelevant c p (proj1 (andb_prop _ _ H))).
  rewrite (all_copyable_irrelevant copyable l q (proj2 (andb_prop _ _ H))).
  exact (supply_list_delta_cons c l H).
Qed.

Lemma supply_list_epsilon_cons_any (c : Colour) (l : list Colour)
  (H : all_copyable copyable (c :: l))
  (p : copyable c = true) (q : all_copyable copyable l) :
  ccomon_epsilon (supply_list (c :: l) H)
  = hom_cast (ctensor_app_b P [c] l) eq_refl
      (to (@unit_left P (MBc P) (@I P (MBc P)))
         ∘ (ccomon_epsilon (supply_wire c p)
            ⨂[MBc P] ccomon_epsilon (supply_list l q))).
Proof.
  rewrite (copyable_irrelevant c p (proj1 (andb_prop _ _ H))).
  rewrite (all_copyable_irrelevant copyable l q (proj2 (andb_prop _ _ H))).
  exact (supply_list_epsilon_cons c l H).
Qed.

(*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem supply_app_delta (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (Hcd : all_copyable copyable (cs ++ ds)) :
  ccomon_delta (supply_list (cs ++ ds) Hcd)
    ≈ hom_cast (ctensor_app_b P cs ds)
        (ctensor2_b P (ctensor_app_b P cs ds) (ctensor_app_b P cs ds))
        (canonical_tensor_delta (supply_list cs Hc) (supply_list ds Hd)).
Proof using OD P SS copyable.
  revert Hc Hcd.
  induction cs as [| c cs' IH]; intros Hc Hcd.
  - (* 相关说明。 （已译） *)
    rewrite (all_copyable_irrelevant copyable _ Hcd Hd).
    rewrite (canonical_tensor_delta_ccomon P).
    rewrite supply_list_delta_nil.
    symmetry.
    apply supply_delta_unit_general.
  - (*
   本节说明 Supply 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    change ((c :: cs') ++ ds) with (c :: cs' ++ ds).
    rewrite (supply_list_delta_cons_any c (cs' ++ ds) Hcd
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite (IH (proj2 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite !(canonical_tensor_delta_ccomon P).
    rewrite (supply_list_delta_cons_any c cs' Hc
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hc))).
    apply supply_delta_assoc_general.
Qed.

Theorem supply_app_epsilon (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (Hcd : all_copyable copyable (cs ++ ds)) :
  ccomon_epsilon (supply_list (cs ++ ds) Hcd)
    ≈ hom_cast (ctensor_app_b P cs ds) eq_refl
        (canonical_tensor_epsilon (supply_list cs Hc) (supply_list ds Hd)).
Proof using OD P SS copyable.
  revert Hc Hcd.
  induction cs as [| c cs' IH]; intros Hc Hcd.
  - rewrite (all_copyable_irrelevant copyable _ Hcd Hd).
    rewrite (canonical_tensor_epsilon_ccomon P).
    rewrite supply_list_epsilon_nil.
    symmetry.
    apply supply_epsilon_unit_general.
  - change ((c :: cs') ++ ds) with (c :: cs' ++ ds).
    rewrite (supply_list_epsilon_cons_any c (cs' ++ ds) Hcd
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite (IH (proj2 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hcd))).
    rewrite !(canonical_tensor_epsilon_ccomon P).
    rewrite (supply_list_epsilon_cons_any c cs' Hc
               (proj1 (andb_prop _ _ Hc)) (proj2 (andb_prop _ _ Hc))).
    apply supply_epsilon_assoc_general.
Qed.

End SupplyCoherence.

Arguments copyable_irrelevant {Colour} copyable c p q : assert.
Arguments supply_list_delta_nil {Colour P copyable SS} H : assert.
Arguments supply_list_epsilon_nil {Colour P copyable SS} H : assert.
Arguments supply_list_delta_cons {Colour P copyable SS} c l H : assert.
Arguments supply_list_epsilon_cons {Colour P copyable SS} c l H : assert.
Arguments supply_list_delta_cons_any {Colour P copyable SS} c l H p q
  : assert.
Arguments supply_list_epsilon_cons_any {Colour P copyable SS} c l H p q
  : assert.
Arguments supply_app_delta {Colour P OD copyable SS} cs ds Hc Hd Hcd : assert.
Arguments supply_app_epsilon {Colour P OD copyable SS} cs ds Hc Hd Hcd
  : assert.
