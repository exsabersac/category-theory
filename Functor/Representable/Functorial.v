Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Iso.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(*
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    nLab: https://ncatlab.org/nlab/show/representable+functor

   本文件给出可表性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section YonedaTranspose.

Context (C : Category).
Context {K K' : C ⟶ Sets}.
Context (R : Representable K) (R' : Representable K').

(*
   本节说明Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition repr_induced_is_yoneda_transpose (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

End YonedaTranspose.

(* 相关说明。 （已译） *)

Section Bridge.

Universes o h.
Context (C : Category@{o h h}).

(* 相关说明。 （已译） *)
Definition repr_of_representation {F : C ⟶ Sets} (c : C)
  (b : [Hom c,─] ≅[Fun] F) : Representable F := {|
  repr_obj := c;
  represented := b
|}.

Context (P : C → Type) (eqP : ∀ c, Setoid (P c)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Representable_of_UnivProperty (H : IsUniversalProperty C P eqP)
  (c : C) (t : P c) : Representable (@repr_functor C P eqP H) := {|
  repr_obj := c;
  represented := to (repr_equivalence c) t
|}.

End Bridge.

Arguments repr_of_representation {C F} c b.
Arguments Representable_of_UnivProperty {C P eqP} H c t.

Section BridgeBack.

Universes o h.
Context (C : Category@{o h h}).
Context (F : C ⟶ Sets).

(*
   本节说明函子、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition UnivProperty_of_Representable
  : IsUniversalProperty C (fun c => @Isomorphism ([C, Sets]) [Hom c,─] F)
      (fun c => iso_setoid) := {|
  repr_functor := F;
  repr_equivalence := fun c => iso_id
|}.

End BridgeBack.

Arguments UnivProperty_of_Representable {C} F.

(** ** The τ = id case, cross-linked *)

Section CrossLink.

Context (C : Category).
Context {F : C ⟶ Sets}.
Context {c v : C}.
Context (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F).

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma repr_pair_iso_from_is_induced :
  from (repr_pair_iso b1 b2)
    ≈ repr_induced (repr_of_representation c b1)
                   (repr_of_representation v b2) nat_id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  apply proper_morphism.
  symmetry; srewrite (@fmap_id _ _ F c); reflexivity.
Qed.

Lemma repr_pair_iso_to_is_induced :
  to (repr_pair_iso b1 b2)
    ≈ repr_induced (repr_of_representation v b2)
                   (repr_of_representation c b1) nat_id.
Proof.
  unfold repr_induced, repr_transport; simpl.
  apply proper_morphism.
  symmetry; srewrite (@fmap_id _ _ F v); reflexivity.
Qed.

End CrossLink.

Section UnivPropertyCrossLink.

Context (C : Category).
Context (P : C → Type) (eqP : ∀ c, Setoid (P c)).
Context (H : IsUniversalProperty C P eqP).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition up_unique_obj_is_repr_pair_iso (c d : C) (t : P c) (s : P d) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H c d t s)
  = repr_pair_iso (to (repr_equivalence c) t) (to (repr_equivalence d) s)
  := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary univ_property_iso_from_is_induced (c d : C) (t : P c) (s : P d) :
  from (unique_obj (univ_property_unique_up_to_unique_iso C P eqP H c d t s))
    ≈ repr_induced (Representable_of_UnivProperty H c t)
                   (Representable_of_UnivProperty H d s) nat_id.
Proof. apply repr_pair_iso_from_is_induced. Qed.

End UnivPropertyCrossLink.

(* * ** The 范畴 已表示的 函子, 表示-对象
 函子 （已译） *)

Section ReprFunctor.

Universes o h.
Context (C : Category@{o h h}).

(* The full subcategory [C, Sets] 函子 carrying chosen
 representation. [shom := True] full-subcategory idiom of
 Theory/Skeleton.v Construction/Localization.v. （已译） *)
Program Definition ReprSubcat : Subcategory ([C, Sets]) := {|
  sobj := fun K => Representable K;
  shom := fun _ _ _ _ _ => True
|}.

Definition ReprCat : Category := @Sub ([C, Sets]) ReprSubcat.

(* ...and assignment ⟨K, R⟩ ↦ repr_obj R, τ ↦ arrow τ names. It
 lands C^op because [repr_induced_comp] reverses 复合. （已译） *)
Program Definition ReprObjFunctor : ReprCat ⟶ C^op := {|
  fobj := fun X => @repr_obj _ _ (`2 X);
  fmap := fun X Y f => repr_induced (`2 X) (`2 Y) (`1 f)
|}.
Next Obligation. intros f g Hfg; now apply repr_induced_respects. Qed.
Next Obligation. now apply repr_induced_id. Qed.
Next Obligation. now apply repr_induced_comp. Qed.

(* Fullness: Mac Lane's correspondence run backwards. An arrow h between the
 表示 对象 is carried ψ' ∘ Hom(h, −) ∘ ψ⁻¹, that
 transformation names h again — 唯一性, once ψ⁻¹ ∘ ψ has been
 cancelled.（已译） *)
Program Definition ReprObj_Full : Functor.Full ReprObjFunctor := {|
  prefmap := fun X Y h =>
    (to (@represented _ _ (`2 Y))
       ∘[Fun] (fmap[Curried_Hom C] (op h) ∘[Fun] from (@represented _ _ (`2 X)))
     ; I)
|}.
Next Obligation.
  symmetry; apply (repr_induced_unique X0 X _ g).
  apply repr_compatible_of_at; intros d k; simpl.
  apply proper_morphism.
  pose proof (iso_from_to (@represented _ _ X0) d k) as HH; simpl in HH.
  rewrite HH.
  now rewrite id_left.
Qed.

(* 相关说明。 （已译） *)
Definition ReprObj_Faithful : Functor.Faithful ReprObjFunctor.
Proof.
  constructor; simpl; intros X Y f g E d z.
  assert (Hz : transform[to (@represented _ _ (`2 X))] d
                 (transform[from (@represented _ _ (`2 X))] d z) ≈ z).
  { pose proof (iso_to_from (@represented _ _ (`2 X)) d z) as HT; simpl in HT.
    rewrite HT.
    srewrite (@fmap_id _ _ (`1 X) d); reflexivity. }
  pose proof (repr_compatible_at
                (repr_induced_compatible (`2 X) (`2 Y) (`1 f)) d
                (transform[from (@represented _ _ (`2 X))] d z)) as Ef.
  pose proof (repr_compatible_at
                (repr_induced_compatible (`2 X) (`2 Y) (`1 g)) d
                (transform[from (@represented _ _ (`2 X))] d z)) as Eg.
  simpl in Ef, Eg.
  rewrite <- Hz, <- Ef, <- Eg.
  now rewrite E.
Qed.

End ReprFunctor.

Arguments ReprSubcat C.
Arguments ReprCat C.
Arguments ReprObjFunctor C.

(*
   本节说明自然变换、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Witness.

Notation BNat := (Deloop Nat_Plus).

(* 相关说明。 （已译） *)
Definition wit_tau (n : nat) := @fmap _ _ (Curried_Hom BNat) ttt ttt n.

(* 相关说明。 （已译） *)
Definition wit_induced_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

Lemma wit_tau_not_id : wit_tau 3%nat ≈ nat_id → False.
Proof. intro Hx; pose proof (Hx ttt 0%nat) as H0; simpl in H0; discriminate. Qed.

Lemma wit_induced_not_id :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau 3%nat)
    ≈ id{BNat} → False.
Proof. intro Hx; simpl in Hx; discriminate. Qed.

(* The same at in-tree [Representable] 实例 rather than the
 tautological one: [YoEvalAt_Representable] (Functor/Hom/Yoneda/Natural.v)
 represents evaluation at 对象 可表 copresheaf. Acting
 each 函子 [fmap] at n is transformation evaluations.（已译） *)
Program Definition wit_ev_tau (n : nat)
  : @YoEvalAt BNat ttt ⟹ @YoEvalAt BNat ttt := {|
  transform := fun F => fmap[F] n
|}.
Next Obligation. exact (@naturality_sym _ _ _ _ f ttt ttt n x0). Qed.
Next Obligation. exact (@naturality _ _ _ _ f ttt ttt n x0). Qed.

(*
   本节说明Yoneda、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wit_ev_induced (n : nat) :
  repr_induced (YoEvalAt_Representable BNat ttt)
               (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)
    ≈ wit_tau n.
Proof. simpl; intros; unfold op; now rewrite <- plus_n_O. Qed.

Lemma wit_ev_tau_not_id : wit_ev_tau 3%nat ≈ nat_id → False.
Proof.
  intro Hx.
  pose proof (Hx (fobj[Curried_Hom BNat] ttt) 0%nat) as H0; simpl in H0.
  discriminate.
Qed.

Lemma wit_ev_induced_not_id :
  repr_induced (YoEvalAt_Representable BNat ttt)
               (YoEvalAt_Representable BNat ttt) (wit_ev_tau 3%nat)
    ≈ id → False.
Proof. intro Hx; pose proof (Hx ttt 0%nat) as H0; simpl in H0; discriminate. Qed.

End Witness.
