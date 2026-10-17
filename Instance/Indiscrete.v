(* * * The indiscrete 函子 right half Smythe's adjoint string （已译） *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Cat.Objects.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/indiscrete+category
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/adjoint+triple
 nLab:      https://ncatlab.org/nlab/show/strict+category
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出非离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition indisc_lift {C : Category} {A : Type} (f : obj[C] -> A)
  : C ⟶ Indiscrete A.
Proof.
  unshelve refine (@Build_Functor C (Indiscrete A) f
                     (fun _ _ _ => tt) _ _ _).
  - intros x y f1 g1 H. apply indiscrete_hom_eq.
  - intros x. apply indiscrete_hom_eq.
  - intros x y z g1 h1. apply indiscrete_hom_eq.
Defined.

(** ** §2. The indiscrete functor *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition StrictCat_Indisc : Coq ⟶ StrictCat := {|
  fobj := Indiscrete;
  fmap := fun A B (f : A ~{Coq}~> B) => indisc_lift (C := Indiscrete A) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §3. The adjunction *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition indisc_adj_iso@{u u0 u1 co ch +}
  (C : obj[StrictCat@{u u0 u1 co ch}]) (A : obj[Coq]) :
  @Isomorphism Sets
    {| carrier := @hom Coq (StrictCat_Objects C) A
     ; is_setoid := @homset Coq (StrictCat_Objects C) A |}
    {| carrier := @hom StrictCat C (StrictCat_Indisc A)
     ; is_setoid := @homset StrictCat C (StrictCat_Indisc A) |} := {|
  to   := {| morphism := fun (f : obj[C] -> A) => indisc_lift f |};
  from := {| morphism := fun (F : C ⟶ Indiscrete A) => fobj[F] |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. apply indiscrete_hom_eq.
Defined.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Objects_Indisc_Adjunction :
  StrictCat_Objects ⊣ StrictCat_Indisc.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact indisc_adj_iso.
  - intros C D A f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
  - intros C A B f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §4. Strengths, strict first *)

Example indisc_obj (A : obj[Coq]) :
  fobj[StrictCat_Indisc] A = Indiscrete A := eq_refl.

Example indisc_obj_carrier (A : obj[Coq]) :
  obj[Indiscrete A] = A := eq_refl.

Example indisc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Indisc] f] x = f x := eq_refl.

Example adj_to_lifts (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  to (indisc_adj_iso C A) f = indisc_lift f := eq_refl.

Example adj_from_forgets (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  from (indisc_adj_iso C A) F = fobj[F] := eq_refl.

Example adj_from_to_ind (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  from (indisc_adj_iso C A) (to (indisc_adj_iso C A) f) = f := eq_refl.

Example indisc_counit_is_id (A : obj[Coq]) (a : A) :
  @counit _ _ _ _ Objects_Indisc_Adjunction A a = a := eq_refl.

Example unit_obj (C : obj[StrictCat]) (x : C) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction C] x = x := eq_refl.

Example unit_is_lift (C : obj[StrictCat]) :
  @unit _ _ _ _ Objects_Indisc_Adjunction C
    = indisc_lift (fun x : obj[C] => x) := eq_refl.

Fail Example adj_to_from_ind (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) = F := eq_refl.

Example rt_obj (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x : C) :
  fobj[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] x
    = fobj[F] x := eq_refl.

Fail Example rt_map_strict (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h := eq_refl.

Example rt_map_leibniz (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h.
Proof. apply indiscrete_hom_eq. Qed.

Example adj_to_from_equiv (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) ≈ F.
Proof. exact (iso_to_from (indisc_adj_iso C A) F). Qed.

Fail Example unit_has_no_eta (u : Datatypes.unit) : u = tt := eq_refl.

Example unit_eta_by_destruct (u : Datatypes.unit) : u = tt.
Proof. now destruct u. Qed.

(* * ** §5. The indiscrete 函子 fully faithful （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Indisc_Faithful : Faithful StrictCat_Indisc.

#[export] Program Instance Indisc_Full : Full StrictCat_Indisc := {|
  prefmap := fun A B (G : StrictCat_Indisc A ~{StrictCat}~> StrictCat_Indisc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_to_from (indisc_adj_iso (StrictCat_Indisc x) y) g).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition adjoint_string :
  (StrictCat_Disc ⊣ StrictCat_Objects)
    * (StrictCat_Objects ⊣ StrictCat_Indisc) :=
  (Disc_Objects_Adjunction, Objects_Indisc_Adjunction).

(* * ** §7. The two adjoints 对象 函子 genuinely differ （已译） *)

(* The engine, one line: 态射 DISCRETE 范畴 an
 equality 证明, indiscrete 范畴 supplies 态射
 between any two 对象, so image [tt] IS equation. （已译） *)
Lemma ind_to_disc_constant {A B : Type}
  (F : Indiscrete A ⟶ DiscreteCat B) (x y : A) : fobj[F] x = fobj[F] y.
Proof. exact (fmap[F] (tt : x ~{Indiscrete A}~> y)). Qed.

Theorem disc_indisc_not_iso :
  @Isomorphism StrictCat (DiscreteCat bool) (Indiscrete bool) -> False.
Proof.
  intro I.
  destruct (iso_to_from I) as [eo _]. simpl in eo.
  pose proof (f_equal (fobj[to I]) (ind_to_disc_constant (from I) true false))
    as H.
  rewrite (eo true), (eo false) in H.
  discriminate.
Qed.

Theorem disc_indisc_not_eq :
  StrictCat_Disc bool = StrictCat_Indisc bool -> False.
Proof.
  intro H.
  refine (Indiscrete_bool_Discrete_absurd _).
  exact (eq_rect _ Discrete (DiscreteCat_Discrete bool) _ H).
Qed.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section IndiscreteSetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (C : Category@{uo uh uh}) (A : Type@{uo}).

  (* 相关说明。 （已译） *)
  Check (C : obj[StrictCat]).
  Check (fmap[StrictCat_Objects] (Id[C])).
  Check (@disc_ext@{uo uh uh uo}).
  Check (DiscreteCat@{uo uh uh} A).
  Check (@indisc_lift (DiscreteCat@{uo Set Set} A) A).

  (* 1: the donor reaches these levels. *)
  Check (Indiscrete@{uo uh uh} : Type@{uo} -> Category@{uo uh uh}).

  (* 2: so does the lift built over it ... *)
  Check (@indisc_lift C A).

  (* 3: ... so, therefore, does 伴随. （已译） *)
  Check (@indisc_adj_iso C A).
End IndiscreteSetPin.

(*
   本节说明伴随、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section IndiscreteObjectsFree.
  Universes wo.
  Constraint Set < wo.
  Context (C : Category@{wo Set Set}) (A : Type@{wo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsFree.

Section IndiscreteObjectsAboveHoms.
  Universes vo vh.
  Constraint Set < vh.
  Constraint vh < vo.
  Context (C : Category@{vo vh vh}) (A : Type@{vo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsAboveHoms.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_identity_functor_ind_to_disc
  (F : Indiscrete bool ⟶ DiscreteCat bool)
  (H : forall b : bool, fobj[F] b = b) : False.
Proof.
  pose proof (ind_to_disc_constant F true false) as K.
  rewrite (H true), (H false) in K. discriminate.
Qed.

(** ** §10. Non-vacuity *)

(*
   本节说明 Indiscrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example comp_obj (A : obj[Coq]) :
  fobj[StrictCat_Objects ◯ StrictCat_Indisc] A = A := eq_refl.

Example comp_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fmap[StrictCat_Objects ◯ StrictCat_Indisc] f x = f x := eq_refl.

Fail Example comp_is_id :
  StrictCat_Objects ◯ StrictCat_Indisc = Id[Coq] := eq_refl.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ind_bool_objs_distinct : (true : Indiscrete bool) = false -> False.
Proof. discriminate. Qed.

(*
   本节说明 Indiscrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SharedMiddle.
Universes a b c d.
Constraint Set < b.
Constraint b < a.
Check adjoint_string@{c a b d a b}.
End SharedMiddle.

Definition ind_bool_connected : Connected (Indiscrete bool) :=
  @arrow_connected (Indiscrete bool) (fun _ _ => tt).

Program Definition ind_bool_iso :
  @Isomorphism (Indiscrete bool) true false := {| to := tt; from := tt |}.

(* The transposition computes. By [adj_to_lifts] forward leg IS
 [indisc_lift], so these evaluate 伴随's own [to] at a
 non-恒等 function. （已译） *)
Example neg_lift_true :
  fobj[indisc_lift (C := DiscreteCat bool) negb] true = false := eq_refl.

Example neg_lift_false :
  fobj[indisc_lift (C := DiscreteCat bool) negb] false = true := eq_refl.

Example counit_bool (b : bool) :
  @counit _ _ _ _ Objects_Indisc_Adjunction bool b = b := eq_refl.

Example unit_disc_bool (b : bool) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction (DiscreteCat bool)] b = b
  := eq_refl.
