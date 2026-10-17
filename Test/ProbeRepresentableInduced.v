(*
   本文件为测试：ProbeRepresentableInduced。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

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
Require Import Category.Functor.Representable.Functorial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(*
   本节说明Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(* Control 1: 柯里化的 hom-函子 itself formable here — so what the
 negatives reject fullness/faithfulness packaging, not [Curried_Hom]
 not [[C, Sets]] target. （已译） *)
Check (Curried_Hom C).

(* 相关说明。 （已译） *)
Check (fun F : C ⟶ Sets => Representable F).

(* Controls 3-6: so whole Functor/Representable.v's
 development — induced arrow, uniqueness packaging, the
 同构 upgrade, tautological representation. （已译） *)
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (tau : K ⟹ K') => repr_induced R R' tau).
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (tau : K ⟹ K') => repr_induced_universal R R' tau).
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (i : K ≅[Fun] K') => repr_induced_iso R R' i).
Check (fun c : C => Hom_Representable c).

(* Negative 1: faithfulness of the Yoneda embedding is not formable here. *)
Fail Check (Yoneda_Faithful C).

(* Negative 2: neither is fullness... *)
Fail Check (Yoneda_Full C).

(* 相关说明。 （已译） *)
Fail Check (fun c d : C => Yoneda_Embedding' C c d).

(* Negative 4: pin propagates [repr_pair_iso], 所消耗
 [Yoneda_Embedding'] — so it DONORS' restriction not something
 Functor/Hom/Yoneda/Iso.v introduces. （已译） *)
Fail Check (fun (F : C ⟶ Sets) (c v : C)
                (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F) =>
              repr_pair_iso b1 b2).

(* 相关说明。 （已译） *)
Fail Check (repr_pair_iso_from_is_induced C).

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@fmap_inj _ _ (Curried_Hom C) (Yoneda_Faithful C)).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition probe_faithful_rederived : Functor.Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same.
  simpl in same.
  specialize same with c id. now rewrite 2 id_left in same.
Qed.

Definition probe_full_rederived : Functor.Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

End ObjectsBelowHoms.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section FunctorBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

Check (ReprObjFunctor C).

End FunctorBelowHoms.

(** ** (2) The conversion boundaries *)

Section Conversion.

Context (C : Category).
Context {F : C ⟶ Sets}.
Context {c v : C}.
Context (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F).

(* 相关说明。 （已译） *)
Definition probe_yoneda_transpose (K K' : C ⟶ Sets)
  (R : Representable K) (R' : Representable K') (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

(* Control 11: 同构 [univ_property_unique_up_to_unique_iso]
 produces IS [repr_pair_iso], nose. （已译） *)
Definition probe_up_unique_obj (P : C → Type) (eqP : ∀ x, Setoid (P x))
  (H : IsUniversalProperty C P eqP) (x y : C) (t : P x) (s : P y) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H x y t s)
  = repr_pair_iso (to (repr_equivalence x) t) (to (repr_equivalence y) s)
  := eq_refl.

(*
   本节说明 ProbeRepresentableInduced 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_pair_iso_strict :
  from (repr_pair_iso b1 b2)
  = repr_induced (repr_of_representation c b1)
                 (repr_of_representation v b2) nat_id := eq_refl.

End Conversion.

Section ConversionWitness.

Notation BNat := (Deloop Nat_Plus).

(* 相关说明。 （已译） *)
Definition probe_wit_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

(* Negative 8: against [YoEvalAt_Representable] it does not, even
 componentwise — Yoneda 同构's backward leg leaves [∘ id],
 which over (ℕ, +) is [n + 0]. The agreement is [≈]
 ([wit_ev_induced]).（已译） *)
Fail Definition probe_wit_ev_strict (n : nat) (d : BNat) (g : ttt ~{BNat}~> d) :
  transform[repr_induced (YoEvalAt_Representable BNat ttt)
                         (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)] d g
  = transform[wit_tau n] d g := eq_refl.

End ConversionWitness.
