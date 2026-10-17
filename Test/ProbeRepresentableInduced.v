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

(** ** (1) The donors' universe restriction, and the escape from it

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The Yoneda donors do not reach it; the induced-arrow
    development does. *)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(* Control 1: the curried hom-functor itself is formable here — so what the
   negatives reject is the fullness/faithfulness packaging, not [Curried_Hom]
   and not the [[C, Sets]] target. *)
Check (Curried_Hom C).

(* Control 2: so is the [Representable] class, which is what makes the
   restriction worth escaping — the class is more general than its donors. *)
Check (fun F : C ⟶ Sets => Representable F).

(* Controls 3-6: and so is the whole of Functor/Representable.v's
   development — the induced arrow, its uniqueness packaging, the
   isomorphism upgrade, and the tautological representation. *)
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

(* ...and negative 3, therefore neither is the packaged hom-bijection the
   issue suggested routing through. *)
Fail Check (fun c d : C => Yoneda_Embedding' C c d).

(* Negative 4: the pin propagates to [repr_pair_iso], which consumes
   [Yoneda_Embedding'] — so it is the DONORS' restriction and not something
   Functor/Hom/Yoneda/Iso.v introduces. *)
Fail Check (fun (F : C ⟶ Sets) (c v : C)
                (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F) =>
              repr_pair_iso b1 b2).

(* Negative 5: ...and thence to Functor/Representable/Functorial.v's
   cross-link, whose printed binder does NOT show the identification. *)
Fail Check (repr_pair_iso_from_is_induced C).

(* Negative 6 is negative 1 one application further in: the projection out of
   the instance is rejected too, for the same reason.  It earns its place by
   pairing with control 7, which inhabits the very same class at this very
   category — so what is rejected is the CONSTANT [Yoneda_Faithful], not the
   claim that [Curried_Hom C] is faithful here. *)
Fail Check (@fmap_inj _ _ (Curried_Hom C) (Yoneda_Faithful C)).

(* Controls 7 and 8: the same two proof scripts, copied verbatim from
   Functor/Hom.v and run here, succeed.  This is what makes negatives
   1-3 a statement about minimization rather than about mathematics. *)
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

(* Control 9, outside the section: the representing-object functor is formable
   over a category with the same strict separation.  It is stated separately
   because it needs the section's constraint discharged into its own binder. *)
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

(* Control 10: the issue's suggested route and the route taken produce the SAME
   TERM — [repr_induced] IS the Yoneda transpose, by [eq_refl]. *)
Definition probe_yoneda_transpose (K K' : C ⟶ Sets)
  (R : Representable K) (R' : Representable K') (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

(* Control 11: the isomorphism [univ_property_unique_up_to_unique_iso]
   produces IS [repr_pair_iso], on the nose. *)
Definition probe_up_unique_obj (P : C → Type) (eqP : ∀ x, Setoid (P x))
  (H : IsUniversalProperty C P eqP) (x y : C) (t : P x) (s : P y) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H x y t s)
  = repr_pair_iso (to (repr_equivalence x) t) (to (repr_equivalence y) s)
  := eq_refl.

(* Negative 7: but [repr_pair_iso]'s leg is NOT the induced arrow on the nose.
   [nat_id]'s component is [fmap[F] id] rather than [id]
   (Theory/Natural/Transformation.v), so the induced arrow carries one
   [fmap] application the leg does not, and the agreement is only [≈]
   ([repr_pair_iso_from_is_induced]). *)
Fail Definition probe_pair_iso_strict :
  from (repr_pair_iso b1 b2)
  = repr_induced (repr_of_representation c b1)
                 (repr_of_representation v b2) nat_id := eq_refl.

End Conversion.

Section ConversionWitness.

Notation BNat := (Deloop Nat_Plus).

(* Control 12: against the tautological representations the induced arrow
   computes on the nose. *)
Definition probe_wit_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

(* Negative 8: against [YoEvalAt_Representable] it does not, even
   componentwise — the Yoneda isomorphism's backward leg leaves an [∘ id],
   which over (ℕ, +) is an [n + 0].  The agreement is [≈]
   ([wit_ev_induced]). *)
Fail Definition probe_wit_ev_strict (n : nat) (d : BNat) (g : ttt ~{BNat}~> d) :
  transform[repr_induced (YoEvalAt_Representable BNat ttt)
                         (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)] d g
  = transform[wit_tau n] d g := eq_refl.

End ConversionWitness.
