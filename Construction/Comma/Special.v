Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** * The comma of two constant functors is the discrete category on a hom-set *)

(*
   nLab:      https://ncatlab.org/nlab/show/comma+category
   nLab:      https://ncatlab.org/nlab/show/discrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Block A: the discrete category on a setoid *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DiscreteSetoidCat {A : Type} (S : Setoid A) : Category := {|
  obj     := A;                                (* objects are the carrier *)
  hom     := fun x y => @equiv A S x y;        (* a morphism IS a proof of ≈ *)
  homset  := fun _ _ => {| equiv := fun _ _ => True |};   (* thin *)
  id      := fun x => @Equivalence_Reflexive A (@equiv A S) (@setoid_equiv A S) x;
  compose := fun x y z g f =>
    @Equivalence_Transitive A (@equiv A S) (@setoid_equiv A S) x y z f g
|}.

(* Thinness, in the form used below: any two parallel arrows agree. *)
Lemma DiscreteSetoidCat_thin {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(* The discrete category on the hom-set C(b, a) — Mac Lane's "discrete
   category on the hom-set", read at the hom-SETOID as the header explains. *)
Definition HomDiscrete {C : Category} (b a : C) : Category :=
  DiscreteSetoidCat (@homset C b a).

(** ** Block B: the comma of two constant functors *)

Section CommaConstant.

Context {C : Category}.
Context {b a : C}.

(* The canonical comma object attached to an arrow h : b ~> a, padded with the
   unique object of 1 on both sides. *)
Definition comma_const_obj (h : b ~{C}~> a) : (=(b) ↓ =(a)) := ((ttt, ttt); h).

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma comma_const_thin (X Y : (=(b) ↓ =(a))) (m n : X ~> Y) : m ≈ n.
Proof.
  destruct m as [[u1 u2] Hm], n as [[v1 v2] Hn]; simpl.
  now split; destruct u1, u2, v1, v2.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma comma_const_equiv {X Y : (=(b) ↓ =(a))} (m : X ~> Y) : `2 X ≈ `2 Y.
Proof.
  destruct m as [uv Hm]; simpl in *.
  rewrite id_left, id_right in Hm.
  now symmetry.
Qed.

(*
   本节说明 Special 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

Program Definition comma_const_mor {X Y : (=(b) ↓ =(a))} (e : `2 X ≈ `2 Y) :
  X ~> Y := ((ttt, ttt); _).
Next Obligation.
  intros X Y e; simpl.
  (* the square is `2 Y ∘ id ≈ id ∘ `2 X, both constant functors sending every
     arrow of 1 to an identity *)
  rewrite id_left, id_right; now symmetry.
Qed.

#[local] Obligation Tactic := cat_simpl.

(*
   本节说明 Special 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition comma_const_obj_iso {X Y : (=(b) ↓ =(a))} (e : `2 X ≈ `2 Y) :
  X ≅ Y := {|
  to   := comma_const_mor e;
  from := comma_const_mor (symmetry e)
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(* Every comma object is canonically isomorphic to the canonical one on its own
   arrow; only the unit padding changes. *)
Program Definition comma_const_iso (X : (=(b) ↓ =(a))) :
  comma_const_obj (`2 X) ≅ X := {|
  to   := comma_const_mor (Y:=X) (reflexivity _);
  from := comma_const_mor (X:=X) (reflexivity _)
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(* Read off the arrow: the comma of two constant functors ⟶ the hom-set. *)
Program Definition Comma_Hom : (=(b) ↓ =(a)) ⟶ HomDiscrete b a := {|
  fobj := fun X => `2 X;
  fmap := fun _ _ m => comma_const_equiv m
|}.

(* ... and back, padding an arrow into a comma object. *)
Program Definition Hom_Comma : HomDiscrete b a ⟶ (=(b) ↓ =(a)) := {|
  fobj := comma_const_obj;
  fmap := fun x y e => comma_const_mor (X:=comma_const_obj x)
                                       (Y:=comma_const_obj y) e
|}.
Solve All Obligations with (intros; apply comma_const_thin).

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* [idtac] so that BOTH clauses are written out rather than left to the default
   obligation tactic; restored immediately afterwards. *)
#[local] Obligation Tactic := idtac.

Program Definition Comma_Discrete_Hom : (=(b) ↓ =(a)) ≅[Cat] HomDiscrete b a := {|
  to   := Comma_Hom;
  from := Hom_Comma
|}.
Next Obligation.
  (*
   本节说明 Special 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  exists (fun _ => iso_id).
  intros x y e; exact I.
Qed.
Next Obligation.
  (* Hom_Comma ◯ Comma_Hom ≈ Id[(=(b) ↓ =(a))]: renormalise the unit padding.
     The coherence clause is an equation between parallel comma morphisms. *)
  exists comma_const_iso.
  intros X Y m.
  first [ apply comma_const_thin | (split; reflexivity) ].
Qed.

#[local] Obligation Tactic := cat_simpl.

End CommaConstant.

(** ** Block C: the plain [DiscreteCat] reading and its exact price *)

Section CommaDiscreteEq.

Context {C : Category}.
Context {b a : C}.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* `=` implies `≈`: transport the reflexivity witness along the equality. *)
Definition discrete_eq_equiv (x y : b ~{C}~> a) (e : x = y) : x ≈ y :=
  match e in _ = z return x ≈ z with eq_refl => reflexivity x end.

Definition comma_const_eq_mor (x y : b ~{C}~> a) (e : x = y) :
  comma_const_obj x ~> comma_const_obj y :=
  comma_const_mor (X := comma_const_obj x) (Y := comma_const_obj y)
    (discrete_eq_equiv x y e).

(* Every functor law is an instance of [comma_const_thin]; [Proper] is a
   definitional single-field class, so its field too is supplied as a plain
   lambda rather than through [Program]. *)
Definition Comma_Discrete_eq : DiscreteCat (b ~{C}~> a) ⟶ (=(b) ↓ =(a)) :=
  @Build_Functor (DiscreteCat (b ~{C}~> a)) (=(b) ↓ =(a))
    comma_const_obj comma_const_eq_mor
    (fun _ _ _ _ _ => comma_const_thin _ _ _ _)
    (fun _ => comma_const_thin _ _ _ _)
    (fun _ _ _ _ _ => comma_const_thin _ _ _ _).

(* The hypothesis that would make the hom-setoid strict. *)
Definition HomStrict : Type := ∀ f g : b ~{C}~> a, f ≈ g → f = g.

(* ... and uniqueness of identity proofs on the hom-type. *)
Definition HomUIP : Type := ∀ (f g : b ~{C}~> a) (p q : f = g), p = q.

(* Essential surjectivity is free: every comma object is the canonical one on
   its own arrow, up to the unit-renormalising isomorphism. *)
Program Definition Comma_Discrete_eq_ESO :
  EssentiallySurjective Comma_Discrete_eq := {|
  eso_obj := fun X => `2 X;
  eso_iso := comma_const_iso
|}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Comma_Discrete_eq_Full_iff : Full Comma_Discrete_eq ↔ HomStrict.
Proof.
  split.
  - intros F f g e.
    exact (@prefmap _ _ _ F f g (comma_const_mor (X:=comma_const_obj f)
                                                 (Y:=comma_const_obj g) e)).
  - intro HE.
    exact (@Build_Full _ _ Comma_Discrete_eq
             (fun f g m => HE f g (comma_const_equiv m))
             (fun f g m => comma_const_thin _ _ _ _)).
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Comma_Discrete_eq_Faithful_iff : Faithful Comma_Discrete_eq ↔ HomUIP.
Proof.
  split.
  - intros F f g p q.
    exact (@fmap_inj _ _ _ F f g p q (comma_const_thin _ _ _ _)).
  - intro HU.
    constructor; intros f g p q _; exact (HU f g p q).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Hom_Discrete_eq (HE : HomStrict) (HU : HomUIP) :
  HomDiscrete b a ⟶ DiscreteCat (b ~{C}~> a) :=
  @Build_Functor (HomDiscrete b a) (DiscreteCat (b ~{C}~> a))
    (fun h => h) HE
    (fun _ _ _ _ _ => HU _ _ _ _)     (* fmap_respects *)
    (fun _ => HU _ _ _ _)             (* fmap_id *)
    (fun _ _ _ _ _ => HU _ _ _ _).    (* fmap_comp *)

(* The other leg, again hand-built rather than [DiscreteCat_Functor] so that no
   universe is baked in; every law is an equation in the thin [HomDiscrete]. *)
Definition Discrete_eq_Hom : DiscreteCat (b ~{C}~> a) ⟶ HomDiscrete b a :=
  @Build_Functor (DiscreteCat (b ~{C}~> a)) (HomDiscrete b a)
    (fun h => h) discrete_eq_equiv
    (fun _ _ _ _ _ => I) (fun _ => I) (fun _ _ _ _ _ => I).

#[local] Obligation Tactic := idtac.

Program Definition Discrete_HomDiscrete (HE : HomStrict) (HU : HomUIP) :
  DiscreteCat (b ~{C}~> a) ≅[Cat] HomDiscrete b a := {|
  to   := Discrete_eq_Hom;
  from := Hom_Discrete_eq HE HU
|}.
Next Obligation.
  (* Discrete_eq_Hom ◯ Hom_Discrete_eq ≈ Id[HomDiscrete b a]: identity on
     objects definitionally, and the target is thin. *)
  intros HE HU.
  exists (fun _ => iso_id).
  intros x y e; exact I.
Qed.
Next Obligation.
  (* Hom_Discrete_eq ◯ Discrete_eq_Hom ≈ Id[DiscreteCat ...]: identity on
     objects definitionally; the coherence clause is an equation between
     equality proofs in the hom-type, hence exactly [HomUIP]. *)
  intros HE HU.
  exists (fun _ => iso_id).
  intros x y p; apply HU.
Qed.

#[local] Obligation Tactic := cat_simpl.

(* Mac Lane's remark in its literal, strictly-discrete form — available exactly
   under the two explicit hypotheses, and (by the theorem after it) not for
   free. *)
Definition Comma_Discrete_Hom_eq (HE : HomStrict) (HU : HomUIP) :
  DiscreteCat (b ~{C}~> a) ≅[Cat] (=(b) ↓ =(a)) :=
  iso_compose (iso_sym Comma_Discrete_Hom) (Discrete_HomDiscrete HE HU).

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem comma_discrete_iso_forces_UIP
  (iso : DiscreteCat (b ~{C}~> a) ≅[Cat] (=(b) ↓ =(a))) : HomUIP.
Proof.
  intros f g p q.
  exact (@fmap_inj _ _ _ (Cat_Iso_to_Faithful iso) f g p q
           (comma_const_thin _ _ _ _)).
Qed.

End CommaDiscreteEq.

(** ** Block D: witnesses — both hypotheses inhabited, and both necessary *)

(*
   本节说明hom、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

From Coq Require Import Eqdep_dec.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Blur : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ _ _ => true
|}.

(* Its hom-setoid does not collapse to equality: `true ≈ false` yet
   `true <> false`. *)
Lemma Blur_HomStrict_absurd : @HomStrict Blur ttt ttt → False.
Proof. intro HE; discriminate (HE true false I). Qed.

(* But UIP on the hom-type does hold, by Hedberg's theorem at the decidable
   equality of [bool] (stdlib [UIP_dec]; no axiom). *)
Lemma Blur_HomUIP : @HomUIP Blur ttt ttt.
Proof.
  intros f g p q; apply UIP_dec.
  intros x y; destruct x, y; solve [ now left | right; discriminate ].
Qed.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Blur_no_discrete_iso :
  (DiscreteCat (ttt ~{Blur}~> ttt) ≅[Cat] (=((ttt : Blur)) ↓ =((ttt : Blur)))) → False.
Proof.
  intro iso.
  (* the two comma images are isomorphic, all Blur-arrows being ≈ *)
  pose proof (comma_const_obj_iso
                (X := to iso true) (Y := to iso false) I) as Hcomma.
  (* transport that isomorphism back along `from iso` *)
  pose proof (@fobj_iso _ _ (from iso) _ _ Hcomma) as Hback.
  (* the round trip identifies `from (to x)` with `x` *)
  pose proof (`1 (iso_from_to iso) true) as Ht.
  pose proof (`1 (iso_from_to iso) false) as Hf.
  assert (Heq : (true : DiscreteCat (ttt ~{Blur}~> ttt)) = false).
  { transitivity (from iso (to iso true)).
    - exact (eq_sym (to Ht)).
    - transitivity (from iso (to iso false)).
      + exact (to Hback).
      + exact (to Hf). }
  discriminate Heq.
Qed.

(*
   本节说明hom、始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Blur_Terminal : @Terminal Blur := {|
  terminal_obj := ttt;
  one := fun _ => true
|}.

Theorem slice_terminal_not_strict :
  (@Slice Blur (@terminal_obj Blur Blur_Terminal) ≅[StrictCat] Blur) → False.
Proof.
  intro iso.
  pose proof (`1 (iso_from_to iso) ((ttt; true) : @Slice Blur ttt)) as Ht.
  pose proof (`1 (iso_from_to iso) ((ttt; false) : @Slice Blur ttt)) as Hf.
  assert (Hmid : fobj[to iso] ((ttt; true) : @Slice Blur ttt)
               = fobj[to iso] ((ttt; false) : @Slice Blur ttt)).
  { now destruct (fobj[to iso] ((ttt; true) : @Slice Blur ttt)),
                 (fobj[to iso] ((ttt; false) : @Slice Blur ttt)). }
  assert (Heq : ((ttt; true) : @Slice Blur ttt) = (ttt; false)).
  { transitivity (fobj[from iso] (fobj[to iso] ((ttt; true) : @Slice Blur ttt))).
    - exact (eq_sym Ht).
    - transitivity (fobj[from iso] (fobj[to iso] ((ttt; false) : @Slice Blur ttt))).
      + exact (f_equal (fobj[from iso]) Hmid).
      + exact Hf. }
  exact (Bool.diff_true_false
           (f_equal (fun s : @Slice Blur ttt => projT2 s) Heq)).
Qed.

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma One_HomStrict : @HomStrict _1 ttt ttt.
Proof. intros f g e; exact e. Qed.

Lemma One_HomUIP : @HomUIP _1 ttt ttt.
Proof.
  intros f g p q.
  apply UIP_dec.
  now intros x y; destruct x, y; left.
Qed.

Definition One_Comma_Discrete_Hom_eq :
  DiscreteCat (ttt ~{_1}~> ttt) ≅[Cat] (=((ttt : _1)) ↓ =((ttt : _1))) :=
  Comma_Discrete_Hom_eq One_HomStrict One_HomUIP.
