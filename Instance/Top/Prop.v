Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Spaces with Prop-valued opens *)

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/topological+space
 nLab: https://ncatlab.org/nlab/show/initial+topology

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** Spaces *)

(*
   本节说明 Prop 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record PTop@{o} := {
  pt_carrier :> SetoidObject@{o o};    (* the setoid of points *)

  (* the topology: which predicates on the points are open *)
  POpen : (pt_carrier → Prop) → Prop;

  (* being open is invariant under pointwise equivalence of predicates *)
  popen_respects (U V : pt_carrier → Prop) :
    (∀ x, U x <-> V x) → POpen U → POpen V;

  (* every open respects the carrier's own equality on points *)
  popen_proper (U : pt_carrier → Prop) :
    POpen U → ∀ x y : pt_carrier, x ≈ y → U x → U y;

  (* closure under arbitrary unions: the union of every family of opens *)
  popen_union (F : (pt_carrier → Prop) → Prop) :
    (∀ U, F U → POpen U) → POpen (fun x => ex (fun U => F U /\ U x));

  (* the whole space is open *)
  popen_whole : POpen (fun _ => True);

  (* closure under binary intersection *)
  popen_inter (U V : pt_carrier → Prop) :
    POpen U → POpen V → POpen (fun x => U x /\ V x)
}.

(*
   本节说明 Prop 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma popen_union_indexed@{o i} (X : PTop@{o}) (I : Type@{i})
  (U : I → pt_carrier X → Prop) :
  (∀ k, POpen X (U k)) → POpen X (fun x => ex (fun k => U k x)).
Proof.
  intro HU.
  apply (popen_respects X
           (fun x => ex (fun W => ex (fun k => ∀ y, W y <-> U k y) /\ W x))).
  - intro x; split.
    + intros [W [[k Hk] w]]. exists k. exact (proj1 (Hk x) w).
    + intros [k u]. exists (U k). split; [|exact u].
      exists k. intro y; exact (iff_refl _).
  - apply popen_union.
    intros W [k Hk].
    apply (popen_respects X (U k)); [|exact (HU k)].
    intro y; exact (iff_sym (Hk y)).
Qed.

(* Every constant proposition is open: the union of the family holding of
   the whole space exactly when [P] does. *)
Lemma popen_const@{o} (X : PTop@{o}) (P : Prop) : POpen X (fun _ => P).
Proof.
  apply (popen_respects X
           (fun x => ex (fun W => (P /\ ∀ y, W y <-> True) /\ W x))).
  - intro x; split.
    + intros [W [[p _] _]]; exact p.
    + intro p. exists (fun _ => True). split; [split; [exact p|]|exact I].
      intro y; exact (iff_refl _).
  - apply popen_union.
    intros W [_ HW].
    apply (popen_respects X (fun _ => True)); [|exact (popen_whole X)].
    intro y; exact (iff_sym (HW y)).
Qed.

(* The empty predicate is open: [popen_const] at [False]. *)
Corollary popen_empty@{o} (X : PTop@{o}) : POpen X (fun _ => False).
Proof. exact (popen_const X False). Qed.

(** ** Continuous maps *)

(* Continuity: the preimage of every open is open.  It is a proposition, so
   a continuous map is a setoid map with a proof attached, at the level of
   the points. *)
Definition PCont@{o} {X Y : PTop@{o}} (f : SetoidMorphism@{o o o} X Y) :
  Prop :=
  ∀ U : Y → Prop, POpen Y U → POpen X (fun x => U (f x)).

(* Continuity depends on the map only up to pointwise [≈]: every open
   respects the codomain's equality. *)
Lemma pcont_respects@{o} {X Y : PTop@{o}} (f g : SetoidMorphism@{o o o} X Y) :
  (∀ x, f x ≈ g x) → PCont f → PCont g.
Proof.
  intros Hfg Hf U HU.
  apply (popen_respects X (fun x => U (f x))); [|exact (Hf U HU)].
  intro x; split; intro u.
  - exact (popen_proper Y U HU (f x) (g x) (Hfg x) u).
  - exact (popen_proper Y U HU (g x) (f x) (symmetry (Hfg x)) u).
Qed.

Record PMor@{o} (X Y : PTop@{o}) : Type@{o} := {
  pmap :> SetoidMorphism@{o o o} X Y;
  pcont : PCont pmap
}.

Arguments pmap {X Y} _.
Arguments pcont {X Y} _ _ _.

(* The hom-setoid compares the map parts pointwise, as [Sets] does; the
   continuity proofs are not compared. *)
Program Definition PMor_Setoid@{o} (X Y : PTop@{o}) :
  Setoid@{o o} (PMor@{o} X Y) := {|
  equiv := fun f g => ∀ x, pmap f x ≈ pmap g x
|}.
Next Obligation.
  intros X Y; constructor.
  - intros f x; reflexivity.
  - intros f g H x; symmetry; exact (H x).
  - intros f g k H1 H2 x; transitivity (pmap g x); [exact (H1 x)|exact (H2 x)].
Qed.

Definition pid@{o} (X : PTop@{o}) : PMor@{o} X X :=
  {| pmap := setoid_morphism_id@{o o o}; pcont := fun U H => H |}.

Definition pcompose@{o} {X Y Z : PTop@{o}} (g : PMor@{o} Y Z)
  (f : PMor@{o} X Y) : PMor@{o} X Z :=
  {| pmap := setoid_morphism_compose@{o o o} g f;
     pcont := fun U H => pcont f _ (pcont g U H) |}.

Lemma pcompose_respects@{o} {X Y Z : PTop@{o}} :
  Proper@{o o} (@equiv _ (PMor_Setoid@{o} Y Z)
                ==> @equiv _ (PMor_Setoid@{o} X Y)
                ==> @equiv _ (PMor_Setoid@{o} X Z)) (@pcompose@{o} X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  transitivity (pmap g1 (pmap f2 x)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category and its underlying-set functor *)

Program Definition PTopCat@{o so | o < so +} : Category@{so o o} := {|
  obj     := PTop@{o};
  hom     := PMor@{o};
  homset  := PMor_Setoid@{o};
  id      := pid@{o};
  compose := @pcompose@{o};

  compose_respects := @pcompose_respects@{o}
|}.
Solve All Obligations with (intros; simpl; intros; reflexivity).

(* The points, into the Sets whose objects ARE the point setoids. *)
Program Definition PForget@{o so | o < so +} :
  PTopCat@{o so} ⟶ Sets@{o so} := {|
  fobj := fun X => pt_carrier X;
  fmap := fun X Y f => pmap f
|}.
Next Obligation. intros X Y f g H x; exact (H x). Qed.
Next Obligation. intros X x; reflexivity. Qed.
Next Obligation. intros X Y Z f g x; reflexivity. Qed.

Example PForget_fobj@{o so | o < so +} (X : PTop@{o}) :
  fobj[PForget@{o so}] X = pt_carrier X := eq_refl.

Example PForget_fmap@{o so | o < so +} {X Y : PTop@{o}}
  (f : X ~{PTopCat@{o so}}~> Y) :
  fmap[PForget@{o so}] f = pmap f := eq_refl.

#[export] Instance PForget_Faithful@{o so | o < so +} :
  Faithful PForget@{o so}.
Proof. constructor; intros x y f g H p; exact (H p). Qed.

(** ** Concrete spaces: the discrete topology, the point and two points *)

(*
   本节说明 Prop 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pdisc_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) : Prop :=
  ∀ x y : S, x ≈ y → U x → U y.

Lemma pdisc_open_respects@{o} (S : SetoidObject@{o o}) (U V : S → Prop) :
  (∀ x, U x <-> V x) → pdisc_open S U → pdisc_open S V.
Proof.
  intros HUV HU x y Hxy v.
  apply (proj1 (HUV y)), (HU x y Hxy), (proj2 (HUV x)), v.
Qed.

Lemma pdisc_open_proper@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  pdisc_open S U → ∀ x y : S, x ≈ y → U x → U y.
Proof. intro HU; exact HU. Qed.

Lemma pdisc_open_union@{o} (S : SetoidObject@{o o})
  (F : (S → Prop) → Prop) :
  (∀ U, F U → pdisc_open S U) →
  pdisc_open S (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF x y Hxy [U [FU u]]. exists U; split; [exact FU|].
  exact (HF U FU x y Hxy u).
Qed.

Lemma pdisc_open_whole@{o} (S : SetoidObject@{o o}) :
  pdisc_open S (fun _ => True).
Proof. intros x y _ t; exact t. Qed.

Lemma pdisc_open_inter@{o} (S : SetoidObject@{o o}) (U V : S → Prop) :
  pdisc_open S U → pdisc_open S V → pdisc_open S (fun x => U x /\ V x).
Proof.
  intros HU HV x y Hxy [u v]; exact (conj (HU x y Hxy u) (HV x y Hxy v)).
Qed.

(* A record literal over the five lemmas, so that the points and the opens
   read back at [eq_refl]. *)
Definition PDiscrete@{o} (S : SetoidObject@{o o}) : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pdisc_open S;
  popen_respects := pdisc_open_respects S;
  popen_proper   := pdisc_open_proper S;
  popen_union    := pdisc_open_union S;
  popen_whole    := pdisc_open_whole S;
  popen_inter    := pdisc_open_inter S
|}.

Example PDiscrete_carrier@{o} (S : SetoidObject@{o o}) :
  pt_carrier (PDiscrete S) = S := eq_refl.

Example PDiscrete_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  POpen (PDiscrete S) U = (∀ x y : S, x ≈ y → U x → U y) := eq_refl.

(* Every setoid map out of a discrete space is continuous: the preimage of
   an open respects the domain's equality because the map and the open
   do. *)
Lemma pdisc_cont@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : @PCont (PDiscrete S) Y f.
Proof.
  intros U HU x y Hxy u.
  exact (popen_proper Y U HU (f x) (f y) (proper_morphism f x y Hxy) u).
Qed.

Definition pdisc_mor@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : PMor@{o} (PDiscrete S) Y :=
  @Build_PMor (PDiscrete S) Y f (pdisc_cont S Y f).

Example pdisc_mor_map@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : pmap (pdisc_mor S Y f) = f := eq_refl.

(* The constant map at a point [y] of a space, as a setoid map from any
   setoid. *)
Definition pconst@{o} (S : SetoidObject@{o o}) (Y : PTop@{o}) (y : Y) :
  SetoidMorphism@{o o o} S Y :=
  {| morphism := fun _ => y; proper_morphism := fun _ _ _ => reflexivity y |}.

(* The one-point space and the two-point discrete space, on
   Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object]. *)
Definition PPoint@{o} : PTop@{o} := PDiscrete unit_setoid_object@{o o}.

Definition PBool@{o} : PTop@{o} := PDiscrete bool_setoid_object@{o o}.

(* The two points of [PBool] are distinct: its equality is Leibniz. *)
Lemma PBool_points_distinct@{o} : @equiv _ PBool@{o} false true → False.
Proof. intro H; discriminate H. Qed.
