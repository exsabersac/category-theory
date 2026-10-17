Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Limit.Power.Hom.
Require Import Category.Structure.Limit.Power.Adjunction.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Parameter.

Generalizable All Variables.

(*
   本文件为测试：ProbeCopower366。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* Instrument check: the harness reports a genuine failure, and a [Fail]
   that succeeds prints nothing, so this must be here. *)
Fail Check probe_366_no_such_constant.

(** ** Controls: everything the negatives name, named outside a [Fail] *)

Check @Power_Functor.
Check @Copower_Functor.
Check @Copower_Power_Adjunction.
Check @cp_adj_iso.
Check @cp_middle.
Check @power_fmap.
Check @power_ev.
Check @copower_inj.
Check @copower_desc.
Check @copower_ump.
Check @power_WeightedLimit.
Check @power_of_weighted.
Check @copower_WeightedColimit.
Check @power_weight.
Check @power_diagram.
Check @copower_diagram.
Check @index_setoid.
Check @wrt_ev.
Check @wrt_inj.
Check @Copower_Bifunctor.
Check @cp_pa_iso.
Check @cp_pa_adj.
Check @Copower_ParametrizedAdjunction.
Check @Power_Bifunctor.
Check @Copower_Bifunctor_Iso.
Check @MacLane_Ex1_hom_bifunctor.
Check @HomAllStrict.
Check @One_HasIndexedCoproducts.
Check @Sets_HasIndexedCoproducts.
Check @Opposite.
Check @Opposite_Functor.
Check @WeightedLimit.
Check @Partial_l.
Check @_1.
Check @cp_pa_adj.
Check @ex1_pa_adj.
Check @Ex1_Bifunctor.
Check @HomCoq.
Check @counit.
Check @unique_property.
Check Coq.

(** ** A. §A: the direct copower functor agrees on DATA, not as a record *)

Section DirectCopower.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

Definition cfd (b b' : C) (g : b ~> b') : copower J b ~> copower J b' :=
  unique_obj (copower_desc (copower_ump J b)
                (fun j : J => copower_inj J b' j ∘ g)).

Lemma cfd_inj {b b' : C} (g : b ~> b') (j : J) :
  cfd b b' g ∘ copower_inj J b j ≈ copower_inj J b' j ∘ g.
Proof. exact (unique_property (copower_desc (copower_ump J b) _) j). Qed.

Program Definition Copower_Functor_direct : C ⟶ C := {|
  fobj := fun b => copower J b;
  fmap := fun b b' g => cfd b b' g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply (uniqueness (copower_desc (copower_ump J b) _)).
  intros j; rewrite cfd_inj; now rewrite Hg.
Qed.
Next Obligation.
  intros b.
  apply (uniqueness (copower_desc (copower_ump J b) _)).
  intros j; now rewrite id_left, id_right.
Qed.
Next Obligation.
  intros x y z f g.
  apply (uniqueness (copower_desc (copower_ump J x) _)).
  intros j.
  rewrite <- comp_assoc, cfd_inj, comp_assoc, cfd_inj.
  now rewrite <- comp_assoc.
Qed.

(* POSITIVE CONTROLS: both DATA fields agree on the nose. *)
Example direct_obj (b : C) :
  fobj[Copower_Functor_direct] b = fobj[Copower_Functor J] b := eq_refl.

Example direct_fmap {b b' : C} (g : b ~> b') :
  fmap[Copower_Functor_direct] g = fmap[Copower_Functor J] g := eq_refl.

(* NEGATIVE 1, CONVERSION.  The WHOLE RECORD is refused: the three
   [Program]-rebuilt law fields differ.  Verbatim:
     ... (cannot unify "Copower_Functor_direct" and "Copower_Functor J"). *)
Fail Example direct_is_op_record :
  Copower_Functor_direct = Copower_Functor J := eq_refl.

End DirectCopower.

(** ** B. §A: the copower functor is [Opposite_Functor] OF the op-power
    functor, and is NOT that functor *)

Section CopowerNotPower.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example copower_is_op_power :
  @Copower_Functor C HC J = @Power_Functor (C^op) HC J := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example copower_is_power :
  Copower_Functor J = Power_Functor J := eq_refl.

(* POSITIVE CONTROL: what DOES hold on the nose is the double opposite. *)
Example double_op :
  Opposite_Functor (Copower_Functor J) = @Power_Functor (C^op) HC J
  := eq_refl.

(* POSITIVE CONTROLS for negative 3: each donor lands at [cp_middle J b c]. *)
Example copower_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle J b c) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

Example power_at_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C b (power J c)
     ; is_setoid := @homset C b (power J c) |} (cp_middle J b c) :=
  power_hom_iso_at (@power_ump C HP J c) b.

(*
   本节说明 ProbeCopower366 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example copower_at_swapped_middle (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (copower J b) c
     ; is_setoid := @homset C (copower J b) c |} (cp_middle J c b) :=
  copower_hom_iso_at (@copower_ump C HC J b) c.

End CopowerNotPower.

(*
   本节说明 ProbeCopower366 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section QedClone.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(* An OPAQUE clone: the same adjunction, closed with [Qed]. *)
Definition cp_adj_qed : Copower_Functor J ⊣ Power_Functor J.
Proof. exact (Copower_Power_Adjunction J). Qed.

(* POSITIVE CONTROL: the target's [Defined] version DOES read back. *)
Example defined_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J)
    (Copower_Power_Adjunction J) b c = cp_adj_iso J b c := eq_refl.

(* NEGATIVE 5, CONVERSION: the [Qed] clone does not. *)
Fail Example qed_readback (b c : C) :
  @adj C C (Copower_Functor J) (Power_Functor J) cp_adj_qed b c
  = cp_adj_iso J b c := eq_refl.

(* The §E adjunction, same treatment.  The readback at stake is the
   target's own [pa_adj_iso_is_cp_adj_iso], which is what makes §E's
   bijection §B's rather than a second one. *)
Definition cp_pa_adj_qed : Partial_l Copower_Bifunctor J ⊣ Power_Functor J.
Proof. exact (cp_pa_adj J). Qed.

(* POSITIVE CONTROL. *)
Example pa_defined_readback (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    (cp_pa_adj J) b c = cp_adj_iso J b c := eq_refl.

(* NEGATIVE 12, CONVERSION.  Verbatim tail:
     (cannot unify "adj[cp_pa_adj_qed]" and "cp_adj_iso J b c"). *)
Fail Example pa_qed_readback (b c : C) :
  @adj C C (Partial_l Copower_Bifunctor J) (Power_Functor J)
    cp_pa_adj_qed b c = cp_adj_iso J b c := eq_refl.

End QedClone.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section QedCloneEx1.

Context {C : Category}.
Context {HC : @HasIndexedCoproducts C}.
Context (HS : HomAllStrict C).

Definition ex1_pa_adj_qed (a : C) :
  Partial_l Ex1_Bifunctor a ⊣ HomCoq HS a.
Proof. exact (ex1_pa_adj HS a). Qed.

(* POSITIVE CONTROL: with the transparent original the counit reduces, so
   the mediator's [unique_property] closes it with no tactic at all. *)
Example ex1_counit_defined (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq HS a)
    (ex1_pa_adj HS a) c ∘ copower_inj (a ~> c) a g ≈ g :=
  unique_property
    (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g.

(* NEGATIVE 13, CONVERSION. *)
Fail Example ex1_counit_qed (a c : C) (g : a ~> c) :
  @counit C Coq (Partial_l Ex1_Bifunctor a) (HomCoq HS a)
    (ex1_pa_adj_qed a) c ∘ copower_inj (a ~> c) a g ≈ g :=
  unique_property
    (copower_desc (copower_ump (a ~> c) a) (fun i : a ~> c => i)) g.

End QedCloneEx1.

(** ** D. §C: why the copower half is built directly over [1^op] *)

Section WeightedShapes.

Context {C : Category}.
Context (b : C).

(* NEGATIVE 6, CONVERSION: the colimit shape is NOT the limit shape. *)
Fail Example one_op_is_one : Opposite _1 = _1 := eq_refl.

(*
   本节说明 ProbeCopower366 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example op_diagram_is_diagram :
  Opposite_Functor (copower_diagram b) = @power_diagram (C^op) b := eq_refl.

(* POSITIVE CONTROL: the two weights agree on the single object's value. *)
Example weight_values_agree (J : Type) :
  fobj[copower_weight J] ttt = fobj[power_weight J] ttt := eq_refl.

End WeightedShapes.

(** ** E. §C: the weighted round trip leaves ONE identity residue *)

Section WeightedRoundTripPin.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).
Context (b : C).

(* POSITIVE CONTROLS: the residues, exhibited. *)
Example ev_residue (j : J) : wrt_ev J b j = power_ev J b j ∘[C] id := eq_refl.
Example inj_residue (j : J) :
  wrt_inj J b j = id ∘[C] copower_inj J b j := eq_refl.

(* NEGATIVES 8 and 9, CONVERSION: strict is refuted on both sides. *)
Fail Example ev_strict (j : J) : wrt_ev J b j = power_ev J b j := eq_refl.
Fail Example inj_strict (j : J) :
  wrt_inj J b j = copower_inj J b j := eq_refl.

End WeightedRoundTripPin.

(** ** F. §E: the §B ISO ascribes at the partial functor; the §B
    ADJUNCTION does not, because [Adjunction] is indexed by the functor
    RECORD and not by its two actions *)

Section PartialAscription.

Context {C : Category}.
Context {HP : @HasIndexedProducts C}.
Context {HC : @HasIndexedCoproducts C}.
Context (J : Type).

(* POSITIVE CONTROLS: both actions agree, and so the ISO ascribes. *)
Example partial_obj (b : C) :
  fobj[Partial_l Copower_Bifunctor J] b = fobj[Copower_Functor J] b
  := eq_refl.

Example iso_ascribes (b c : C) :
  @Isomorphism Sets
    {| carrier := @hom C (fobj[Partial_l Copower_Bifunctor J] b) c
     ; is_setoid := @homset C (fobj[Partial_l Copower_Bifunctor J] b) c |}
    {| carrier := @hom C b (fobj[Power_Functor J] c)
     ; is_setoid := @homset C b (fobj[Power_Functor J] c) |} :=
  cp_adj_iso J b c.

(* NEGATIVE 10, CONVERSION.  The error names the offending field:
     (cannot unify "λ (x y : obj[C^op^op]) (f g : x ~{ C^op^op }~> y),
                    fmap_respects y x f g"
      and "Partial.Partial_l_obligation_1 C Coq C Copower_Bifunctor J"). *)
Fail Definition adjunction_ascribes :
  Partial_l Copower_Bifunctor J ⊣ Power_Functor J :=
  Copower_Power_Adjunction J.

End PartialAscription.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IndexPin.

Universes co ch ji.
Constraint ch < ji.
Context (Cu : Category@{co ch ch}) (HPu : @HasIndexedProducts Cu)
        (Ju : Type@{ji}) (bu cu : obj[Cu]).

Check (@power Cu HPu Ju bu).
Check (@power_ev Cu HPu Ju bu).
Check (@Power_Functor Cu HPu Ju).
Check (index_setoid Ju).
Check (power_weight Ju).
Check (@power_diagram Cu bu).
Check (HomDiagram cu (@power_diagram Cu bu)).

(*
   本节说明 ProbeCopower366 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (WeightedLimit (power_weight Ju) (@power_diagram Cu bu)).

End IndexPin.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IndexAboveHom.

Universes co ch ji.
Constraint ch < ji.
Context (Cu : Category@{co ch ch}) (HPu : @HasIndexedProducts Cu)
        (HCu : @HasIndexedCoproducts Cu) (Ju : Type@{ji}).

Check (@Power_Functor Cu HPu Ju).
Check (@Copower_Functor Cu HCu Ju).
Check (@power_fmap Cu HPu Ju).

(* NEGATIVE 14, FORMABILITY.  Verbatim tail:
     The term "Ju" has type "Type@{ji}" while it is expected to have type
     "Type@{...}" (universe inconsistency: Cannot enforce ji <= ...
     because ... < ji).
   [cp_adj_iso] is refused at the same levels, carrying the same four
   equations. *)
Fail Check (@Copower_Power_Adjunction Cu HPu HCu Ju).

End IndexAboveHom.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition blur_equivalence : Equivalence (fun _ _ : bool => True) :=
  {| Equivalence_Reflexive := fun _ => I
   ; Equivalence_Symmetric := fun _ _ _ => I
   ; Equivalence_Transitive := fun _ _ _ _ _ => I |}.

Definition BoolBlur : obj[Sets] :=
  {| carrier := bool
   ; is_setoid := Build_Setoid bool (fun _ _ => True) blur_equivalence |}.

Definition ProbePt : obj[Sets] := Sets_discrete Datatypes.unit.

Definition blur_id : Sets_discrete bool ~{Sets}~> BoolBlur.
Proof.
  unshelve econstructor.
  - exact (fun b : bool => b).
  - intros x y H; exact I.
Defined.

Definition blur_neg : Sets_discrete bool ~{Sets}~> BoolBlur.
Proof.
  unshelve econstructor.
  - exact negb.
  - intros x y H; exact I.
Defined.

Lemma blur_equal : blur_id ≈ blur_neg.
Proof. intro b; exact I. Qed.

(* The [fmap_respects] obligation, written out at the shape it takes. *)
Definition SetsIndexRespects : Type :=
  ∀ (S S' a : Sets) (f f' : S ~{Sets}~> S'), f ≈ f' → ∀ j : S,
    @copower_inj Sets Sets_HasIndexedCoproducts (carrier S') a (f j)
      ≈ @copower_inj Sets Sets_HasIndexedCoproducts (carrier S') a (f' j).

Theorem sets_index_respects_absurd : SetsIndexRespects → False.
Proof.
  intro H.
  destruct (H (Sets_discrete bool) BoolBlur ProbePt
              blur_id blur_neg blur_equal true tt) as [e _].
  simpl in e; discriminate e.
Qed.

(** ** I. The two parametrizations are BOTH inhabited *)

Check (@Copower_ParametrizedAdjunction).
Check (@Copower_Object_ParametrizedAdjunction).
Check One_Ex1_ParametrizedAdjunction.
Check (@Copower_Bifunctor_Iso).
