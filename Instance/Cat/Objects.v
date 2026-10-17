(** * The objects functor on the category of categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/indiscrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/Cat
 nLab:      https://ncatlab.org/nlab/show/strict+category
 nLab:      https://ncatlab.org/nlab/show/connected+component
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** §1. The discrete extension, with its universes written out *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition disc_ext@{o h p q} {A : Type@{o}} {C : Category@{q h p}}
  (f : A → obj[C]) : DiscreteCat@{o h p} A ⟶ C.
Proof.
  unshelve refine (@Build_Functor (DiscreteCat@{o h p} A) C f
                    (fun x y (e : x = y) =>
                       match e in _ = z return f x ~{C}~> f z with
                       | eq_refl => id end) _ _ _).
  - intros x y e1 e2 He. destruct He. reflexivity.
  - intros x. reflexivity.
  - intros x y z g e. destruct g, e. simpl. symmetry; apply id_left.
Defined.

(** ** §2. The objects functor *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition StrictCat_Objects : StrictCat ⟶ Coq := {|
  fobj := fun C => obj[C];
  fmap := fun _ _ F => fobj[F]
|}.

(** ** §3. The discrete functor *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition StrictCat_Disc : Coq ⟶ StrictCat := {|
  fobj := fun A => DiscreteCat A;
  fmap := fun A B (f : A ~{Coq}~> B) => disc_ext (C := DiscreteCat B) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.

(** ** §4. The adjunction *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition disc_adj_iso (A : obj[Coq]) (C : obj[StrictCat]) :
  @Isomorphism Sets
    {| carrier := @hom StrictCat (StrictCat_Disc A) C
     ; is_setoid := @homset StrictCat (StrictCat_Disc A) C |}
    {| carrier := @hom Coq A (StrictCat_Objects C)
     ; is_setoid := @homset Coq A (StrictCat_Objects C) |} := {|
  to   := {| morphism := fun (F : DiscreteCat A ⟶ C) => fobj[F] |};
  from := {| morphism := fun (f : A → obj[C]) => disc_ext f |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. destruct e.
  unfold Logic.transport, Logic.transport_r, Logic.transport; simpl.
  symmetry; exact (@fmap_id _ _ x a).
Defined.

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Disc_Objects_Adjunction : StrictCat_Disc ⊣ StrictCat_Objects.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact disc_adj_iso.
  - intros A B C f g. reflexivity.
  - intros A B C f g. reflexivity.
Defined.

(** ** §5. Strengths, strict first *)

Example objects_obj (C : obj[StrictCat]) :
  fobj[StrictCat_Objects] C = obj[C] := eq_refl.

Example objects_map (C D : obj[StrictCat]) (F : C ~{StrictCat}~> D)
  (x : C) : fmap[StrictCat_Objects] F x = F x := eq_refl.

Example disc_on_obj (A : obj[Coq]) :
  fobj[StrictCat_Disc] A = DiscreteCat A := eq_refl.

Example disc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Disc] f] x = f x := eq_refl.

Example adj_to_forgets (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  to (disc_adj_iso A C) F = fobj[F] := eq_refl.

Example adj_from_extends (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) (x : A) :
  fobj[from (disc_adj_iso A C) f] x = f x := eq_refl.

Example adj_to_from (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) :
  to (disc_adj_iso A C) (from (disc_adj_iso A C) f) = f := eq_refl.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example unit_is_id (A : obj[Coq]) (a : A) :
  @unit _ _ _ _ Disc_Objects_Adjunction A a = a := eq_refl.

Example counit_obj (C : obj[StrictCat])
  (x : StrictCat_Disc (StrictCat_Objects C)) :
  fobj[@counit _ _ _ _ Disc_Objects_Adjunction C] x = x := eq_refl.

(*
   本节说明 Objects 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example adj_from_to_strict (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) = F := eq_refl.

Example adj_from_to_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) ≈ F.
Proof. exact (iso_from_to (disc_adj_iso A C) F). Qed.

Example roundtrip_obj (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fobj[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] x = fobj[F] x
  := eq_refl.

Fail Example roundtrip_map (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    = fmap[F] (eq_refl : x = x) := eq_refl.

Example roundtrip_map_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    ≈ fmap[F] (eq_refl : x = x).
Proof. symmetry; exact (@fmap_id _ _ F x). Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Disc_Faithful : Faithful StrictCat_Disc.

#[export] Program Instance Disc_Full : Full StrictCat_Disc := {|
  prefmap := fun A B (G : StrictCat_Disc A ~{StrictCat}~> StrictCat_Disc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_from_to (disc_adj_iso x (StrictCat_Disc y)) g).
Defined.

(** ** §6. Why the source is [StrictCat] and not [Cat] *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ObjRespectsCat : Type :=
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset Cat C D) F G → ∀ x : C, F x = G x.

(* Over [StrictCat] it is the FIRST PROJECTION of the hom-setoid: a [:=]
   with no tactic. *)
Definition objects_respects_StrictCat :
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset StrictCat C D) F G → ∀ x : C, F x = G x :=
  fun C D F G H => `1 H.

Lemma indiscrete_hom_eq (a b : Datatypes.unit) : a = b.
Proof. now destruct a, b. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition SwapI : Indiscrete bool ⟶ Indiscrete bool := {|
  fobj := negb;
  fmap := fun _ _ _ => tt
|}.

Lemma swap_iso_in_Cat :
  @equiv _ (@homset Cat (Indiscrete bool) (Indiscrete bool))
         (Id[Indiscrete bool]) SwapI.
Proof.
  unshelve eexists.
  - intro x. unshelve eexists; simpl; try exact tt; apply indiscrete_hom_eq.
  - intros x y f; simpl; apply indiscrete_hom_eq.
Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem objects_not_functorial_over_Cat : ObjRespectsCat → False.
Proof.
  intro K.
  exact (eq_ind true (fun b : bool => if b then True else False) I false
           (K _ _ (Id[Indiscrete bool]) SwapI swap_iso_in_Cat true)).
Qed.

(** ** §7. Why the target is [Coq] and not [Sets] *)

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PointedObjectMap
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A]) : Type :=
  (∀ (A : obj[Sets]) (x y : carrier A), Kpt A x = Kpt A y → x = y)
    * (∀ (A B : obj[Sets]) (f : A ~{Sets}~> B) (x : carrier A),
         fobj[Kmap A B f] (Kpt A x) = Kpt B (f x)).

(*
   本节说明 Objects 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition BlurBool : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition kTrue : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => true |}.

Program Definition kFalse : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => false |}.

Lemma k_equiv : kTrue ≈ kFalse.
Proof. intro x; exact I. Qed.

Theorem no_carrier_functor_Sets_StrictCat
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A])
  (HK : PointedObjectMap K Kmap Kpt)
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat (K A) (K B)) (Kmap A B f) (Kmap A B g))
  : False.
Proof.
  destruct HK as [Kinj Kobj].
  pose proof (`1 (Kresp _ _ kTrue kFalse k_equiv) (Kpt BlurBool true)) as H.
  rewrite (Kobj BlurBool BlurBool kTrue true) in H.
  rewrite (Kobj BlurBool BlurBool kFalse true) in H.
  apply Kinj in H.
  discriminate.
Qed.

(* Instantiation 1: the DISCRETE object map on carriers, i.e. §3's
   [StrictCat_Disc] re-aimed at [Sets].  It is refuted. *)
Definition disc_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  DiscreteCat (carrier A) ~{StrictCat}~> DiscreteCat (carrier B) :=
  disc_ext (C := DiscreteCat (carrier B)) f.

Definition disc_carrier_pointed :
  PointedObjectMap (fun A => DiscreteCat (carrier A)) disc_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem disc_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (disc_carrier_Kmap A B f) (disc_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ disc_carrier_pointed Kresp).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ind_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  Indiscrete (carrier A) ~{StrictCat}~> Indiscrete (carrier B) := {|
  fobj := f;
  fmap := fun _ _ _ => tt
|}.

Definition ind_carrier_pointed :
  PointedObjectMap (fun A => Indiscrete (carrier A)) ind_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem ind_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (ind_carrier_Kmap A B f) (ind_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ ind_carrier_pointed Kresp).
Qed.

(** ** §8. The universe boundary *)

(*
   本节说明 Objects 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明 Objects 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section SetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (A : Type@{uo}) (C : Category@{uo uh uh}) (f : A → obj[C]).

  (* controls: the shape and the functor type ARE formable here, and both
     donors ARE nameable. *)
  Check (DiscreteCat@{uo uh uh} A).
  Check (DiscreteCat@{uo uh uh} A ⟶ C).
  Check (DiscreteCat_Functor f).
  Check (Indiscrete A).

  (* and, since the annotation, both donors also REACH these levels *)
  Check (DiscreteCat_Functor f : DiscreteCat@{uo uh uh} A ⟶ C).
  Check (Indiscrete@{uo uh uh} : Type@{uo} → Category@{uo uh uh}).

  (* as does the hand-written extension *)
  Check (disc_ext@{uo uh uh uo} f : DiscreteCat@{uo uh uh} A ⟶ C).
End SetPin.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section StrictCatObjects.
  Universes co ch cp.
  Constraint ch < cp.
  Context (C : Category@{co ch cp}).
  Fail Check (C : obj[StrictCat]).
End StrictCatObjects.

Section StrictCatHomsBelow.
  Universes co ch.
  Constraint ch < co.
  Context (C : Category@{co ch ch}).
  Check (C : obj[StrictCat]).
End StrictCatHomsBelow.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section AdjunctionUniversesSeparated.
  Universes a b c e f.
  Constraint b < f.
  Check (StrictCat_Disc@{a b c f e f} ⊣ StrictCat_Objects@{a c f e f b}).
End AdjunctionUniversesSeparated.

(** ** §9. The objects functor genuinely forgets *)

(*
   本节说明函子、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Ltac bool_cases :=
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  reflexivity.

Program Definition BoolMon : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := @eq bool |};
  id      := fun _ => false;
  compose := fun _ _ _ f g => xorb f g
|}.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.

Program Definition ZeroF : BoolMon ⟶ BoolMon := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => false
|}.

(* [poly_unit] has decidable equality, so Hedberg applies and the
   transport in [Functor_StrictEq_Setoid]'s coherence field can be
   eliminated; the argument is axiom-free. *)
Lemma poly_unit_uip (p : @eq poly_unit ttt ttt) : p = eq_refl.
Proof.
  apply (Eqdep_dec.UIP_dec (fun x y : poly_unit => left
    (match x, y with ttt, ttt => eq_refl end))).
Qed.

Lemma Id_neq_ZeroF :
  @equiv _ (@homset StrictCat BoolMon BoolMon) (Id[BoolMon]) ZeroF → False.
Proof.
  intros [eo co].
  pose proof (co ttt ttt true) as H.
  rewrite (poly_unit_uip (eo ttt)) in H.
  simpl in H. discriminate.
Qed.

Example objects_merges :
  fmap[StrictCat_Objects] (Id[BoolMon]) ≈ fmap[StrictCat_Objects] ZeroF.
Proof. intro x; reflexivity. Qed.

Theorem Objects_not_Faithful : Faithful StrictCat_Objects → False.
Proof.
  intro F. exact (Id_neq_ZeroF (fmap_inj _ _ objects_merges)).
Qed.
