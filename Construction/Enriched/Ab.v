(* 相关说明。 （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/Ab-enriched+category
   Wikipedia: https://en.wikipedia.org/wiki/Preadditive_category

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Coq.ZArith.BinInt.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Monoidal.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** From AbEnriched 范畴 tensor data （已译） *)

Section FromAbEnriched.

Context {C : Category} {A : AbEnriched C}.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context {LP : LocallyPropositional C}.

(* The hom-group of a hom-set: Structure/AbCategory.v's fields, packaged
   as an object of Ab. *)
Definition ehom_ab (x y : C) : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := x ~> y; is_setoid := @homset C x y |};
    cmon_zero := @pzero C _ x y;
    cmon_plus := @padd C _ x y;
    cmon_plus_respects := @padd_respects C _ x y;
    cmon_plus_assoc := @padd_assoc C _ x y;
    cmon_plus_comm := @padd_comm C _ x y;
    cmon_plus_zero_l := @padd_zero_left C _ x y;
    cmon_prop := locally_prop x y
  |};
  ab_neg := @abneg C A x y;
  ab_neg_respects := @abneg_respects C A x y;
  ab_neg_left := fun f =>
    transitivity (@padd_comm C _ x y (abneg f) f) (padd_abneg f)
|}.

(* Precomposition with f, as a homomorphism of hom-groups: additivity is
   [compose_padd_right], zero-preservation [compose_pzero_left]. *)
Program Definition precomp_hom {x y z : C} (f : x ~> y) :
  AbHom (ehom_ab y z) (ehom_ab x z) := {|
  cmon_map := {| morphism := fun g : y ~> z => g ∘ f |}
|}.
Next Obligation.
  intros x y z f g g' Hg.
  exact (compose_respects _ _ Hg _ _ (reflexivity f)).
Qed.
Next Obligation.
  intros x y z f; simpl.
  exact (@compose_pzero_left C _ x y z f).
Qed.
Next Obligation.
  intros x y z f g g'; simpl.
  exact (@compose_padd_right C _ x y z g g' f).
Qed.

(* 相关说明。 （已译） *)
Program Definition postcomp_hom {x y z : C} (g : y ~> z) :
  AbHom (ehom_ab x y) (ehom_ab x z) := {|
  cmon_map := {| morphism := fun f : x ~> y => g ∘ f |}
|}.
Next Obligation.
  intros x y z g f f' Hf.
  exact (compose_respects _ _ (reflexivity g) _ _ Hf).
Qed.
Next Obligation.
  intros x y z g; simpl.
  exact (@compose_pzero_right C _ x y z g).
Qed.
Next Obligation.
  intros x y z g f f'; simpl.
  exact (@compose_padd_left C _ x y z g f f').
Qed.

(* The ℤ-action commutes 复合 either side — instances of
 [zsmul_hom] at two homomorphisms above (design note 2). （已译） *)
Lemma zsmul_precomp {x y z : C} (n : Z) (g : y ~> z) (f : x ~> y) :
  zsmul (ehom_ab y z) n g ∘ f ≈ zsmul (ehom_ab x z) n (g ∘ f).
Proof.
  exact (zsmul_hom (precomp_hom f) n g).
Qed.

Lemma zsmul_postcomp {x y z : C} (n : Z) (g : y ~> z) (f : x ~> y) :
  g ∘ zsmul (ehom_ab x y) n f ≈ zsmul (ehom_ab x z) n (g ∘ f).
Proof.
  exact (zsmul_hom (postcomp_hom g) n f).
Qed.

(* The unit ℤ → A(x,x): n ↦ n·id.  Additivity in n is [zsmul_add]. *)
Program Definition ab_eid (x : C) : AbHom ZAb (ehom_ab x x) := {|
  cmon_map := {| morphism := fun n : Z => zsmul (ehom_ab x x) n (@id C x) |}
|}.
Next Obligation.
  intros x n m Hnm.
  rewrite (ZAb_eq n m Hnm).
  reflexivity.
Qed.
Next Obligation.
  intros x; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x n m; simpl.
  exact (zsmul_add (ehom_ab x x) n m (@id C x)).
Qed.

(* Composition A(y,z) ⊗ A(x,y) → A(x,z): ⊗-factorization ∘, its
 bilinearity two 复合-bilinearity fields Preadditive. （已译） *)
Program Definition ab_ecompose (x y z : C) :
  AbHom (AbTensor (ehom_ab y z) (ehom_ab x y)) (ehom_ab x z) :=
  tensor_ump (@Build_Bilinear (ehom_ab y z) (ehom_ab x y) (ehom_ab x z)
    (fun g f => g ∘ f) _ _ _).
Next Obligation.
  intros x y z g g' f; simpl.
  exact (@compose_padd_right C _ x y z g g' f).
Qed.
Next Obligation.
  intros x y z g f f'; simpl.
  exact (@compose_padd_left C _ x y z g f f').
Qed.

(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Enriched_of_AbEnriched : @Enriched Ab Ab_Monoidal.
Proof using A C LP.
  unshelve refine
    (@Build_Enriched Ab Ab_Monoidal obj[C] ehom_ab ab_eid ab_ecompose
       _ _ _).
  - (* eid_left : ecompose ∘ eid ⨂ id ≈ unit_left *)
    intros x y s; revert s.
    apply tensor_hom_ext.
    intros n f; simpl.
    refine (transitivity (zsmul_precomp n (@id C y) f) _).
    exact (zsmul_respects (ehom_ab x y) n _ _ (id_left f)).
  - (* eid_right : ecompose ∘ id ⨂ eid ≈ unit_right *)
    intros x y s; revert s.
    apply tensor_hom_ext.
    intros f n; simpl.
    refine (transitivity (zsmul_postcomp n f (@id C x)) _).
    exact (zsmul_respects (ehom_ab x y) n _ _ (id_right f)).
  - (* ecompose_assoc *)
    intros x y z w s; revert s.
    apply tensor_hom_ext2.
    intros h g f; simpl.
    exact (symmetry (comp_assoc h g f)).
Defined.

End FromAbEnriched.

(* * ** From tensor data AbEnriched 范畴 （已译） *)

Section ToAbEnriched.

Context (E : @Enriched Ab Ab_Monoidal).

(* The 范畴: 复合 [ecompose] at generator, 恒等 is
 [eid] at 1. The laws E's equations consumed at generators, where
 both sides compute. （已译） *)
Program Definition Category_of_Enriched_Ab : Category := {|
  obj := @eobj Ab Ab_Monoidal E;
  hom := fun x y => carrier (@ehom Ab Ab_Monoidal E x y);
  homset := fun x y =>
    is_setoid (cmon_setoid (ab_cmon (@ehom Ab Ab_Monoidal E x y)));
  id := fun x => cmon_map (@eid Ab Ab_Monoidal E x) 1%Z;
  compose := fun x y z g f =>
    cmon_map (@ecompose Ab Ab_Monoidal E x y z) (ts_gen g f)
|}.
Next Obligation.
  (* compose_respects *)
  intros x y z g g' Hg f f' Hf.
  exact (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
           _ _ (te_gen Hg Hf)).
Qed.
Next Obligation.
  (* id_left: eid_left at the generator ts_gen 1 f *)
  intros x y f.
  pose proof (@eid_left Ab Ab_Monoidal E x y
                (@ts_gen ZAb (@ehom Ab Ab_Monoidal E x y) 1%Z f)) as Hl.
  simpl in Hl.
  refine (transitivity Hl _).
  exact (zsmul_one (@ehom Ab Ab_Monoidal E x y) f).
Qed.
Next Obligation.
  (* id_right: eid_right at the generator ts_gen f 1 *)
  intros x y f.
  pose proof (@eid_right Ab Ab_Monoidal E x y
                (@ts_gen (@ehom Ab Ab_Monoidal E x y) ZAb f 1%Z)) as Hr.
  simpl in Hr.
  refine (transitivity Hr _).
  exact (zsmul_one (@ehom Ab Ab_Monoidal E x y) f).
Qed.
Next Obligation.
  (* comp_assoc: ecompose_assoc at ts_gen (ts_gen f g) h *)
  intros x y z w f g h.
  pose proof (@ecompose_assoc Ab Ab_Monoidal E x y z w
                (@ts_gen (AbTensor (@ehom Ab Ab_Monoidal E z w)
                                   (@ehom Ab Ab_Monoidal E y z))
                         (@ehom Ab Ab_Monoidal E x y)
                   (@ts_gen (@ehom Ab Ab_Monoidal E z w)
                            (@ehom Ab Ab_Monoidal E y z) f g) h)) as Ha.
  simpl in Ha.
  exact (symmetry Ha).
Qed.
Next Obligation.
  (* comp_assoc_sym *)
  intros x y z w f g h.
  pose proof (@ecompose_assoc Ab Ab_Monoidal E x y z w
                (@ts_gen (AbTensor (@ehom Ab Ab_Monoidal E z w)
                                   (@ehom Ab Ab_Monoidal E y z))
                         (@ehom Ab Ab_Monoidal E x y)
                   (@ts_gen (@ehom Ab Ab_Monoidal E z w)
                            (@ehom Ab Ab_Monoidal E y z) f g) h)) as Ha.
  simpl in Ha.
  exact Ha.
Qed.

(* The AbEnriched structure: hom-group operations hom-对象;
 bilinearity 复合 generator relations tensor
 pushed through [ecompose]'s homomorphism property. （已译） *)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition LocallyPropositional_of_Enriched_Ab :
  LocallyPropositional Category_of_Enriched_Ab.
Proof.
  constructor.
  intros x y.
  exact (cmon_prop (ab_cmon (@ehom Ab Ab_Monoidal E x y))).
Defined.

Program Definition AbEnriched_of_Enriched_Ab :
  AbEnriched Category_of_Enriched_Ab := {|
  abenriched_preadditive := {|
    padd := fun x y f g =>
      cmon_plus (ab_cmon (@ehom Ab Ab_Monoidal E x y)) f g;
    pzero := fun x y =>
      cmon_zero (ab_cmon (@ehom Ab Ab_Monoidal E x y))
  |};
  abneg := fun x y f => ab_neg (@ehom Ab Ab_Monoidal E x y) f
|}.
Next Obligation.
  intros x y f g h.
  exact (cmon_plus_assoc _ f g h).
Qed.
Next Obligation.
  intros x y f g.
  exact (cmon_plus_comm _ f g).
Qed.
Next Obligation.
  intros x y f.
  exact (cmon_plus_zero_l _ f).
Qed.
Next Obligation.
  (* compose_padd_left: h ∘ (f + g) ≈ h ∘ f + h ∘ g *)
  intros x y z h f g; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (te_bilin_r h f g)) _).
  exact (cmon_map_plus (@ecompose Ab Ab_Monoidal E x y z)
           (ts_gen h f) (ts_gen h g)).
Qed.
Next Obligation.
  (* compose_padd_right: (f + g) ∘ h ≈ f ∘ h + g ∘ h *)
  intros x y z f g h; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (te_bilin_l f g h)) _).
  exact (cmon_map_plus (@ecompose Ab Ab_Monoidal E x y z)
           (ts_gen f h) (ts_gen g h)).
Qed.
Next Obligation.
  (* compose_pzero_left: 0 ∘ f ≈ 0 *)
  intros x y z f; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (ts_gen_zero_l f)) _).
  exact (cmon_map_zero (@ecompose Ab Ab_Monoidal E x y z)).
Qed.
Next Obligation.
  (* compose_pzero_right: f ∘ 0 ≈ 0 *)
  intros x y z f; simpl.
  refine (transitivity
            (proper_morphism (cmon_map (@ecompose Ab Ab_Monoidal E x y z))
               _ _ (ts_gen_zero_r f)) _).
  exact (cmon_map_zero (@ecompose Ab Ab_Monoidal E x y z)).
Qed.
Next Obligation.
  (* padd_abneg: f + (− f) ≈ 0 *)
  intros x y f.
  exact (ab_neg_right (@ehom Ab Ab_Monoidal E x y) f).
Qed.

End ToAbEnriched.

(** ** The correspondence *)

(* Mac Lane's "can be described completely in these terms", as a
   Type-valued equivalence of the two presentations — the same shape as
   [Category_is_Enriched_over_Set] and [Enriched_Two_preorder]. *)
(* The forward direction, exercised at concrete witness: Ab an
 Ab-范畴, so it enriched over itself. （已译） *)
Definition Enriched_Ab_itself : @Enriched Ab Ab_Monoidal :=
  @Enriched_of_AbEnriched Ab Ab_AbEnriched Ab_LocallyPropositional.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Enriched_Ab_iff_AbEnriched :
  @Enriched Ab Ab_Monoidal ↔
  { C : Category & (LocallyPropositional C * AbEnriched C)%type }.
Proof.
  split.
  - intro E.
    exact (Category_of_Enriched_Ab E;
           (LocallyPropositional_of_Enriched_Ab E,
            AbEnriched_of_Enriched_Ab E)).
  - intros [C [LP A]].
    exact (@Enriched_of_AbEnriched C A LP).
Defined.
