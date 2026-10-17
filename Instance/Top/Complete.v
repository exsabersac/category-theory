Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

Generalizable All Variables.

(** * Spaces are complete: initial topologies, products and limits over
      [PTopCat] *)

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/initial+topology
 nLab: https://ncatlab.org/nlab/show/complete+category
 nLab: https://ncatlab.org/nlab/show/topological+concrete+category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** The initial topology for a family of functions *)

(*
   本节说明等价、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PIsTopology@{o} (S : SetoidObject@{o o})
  (T : (S → Prop) → Prop) : Prop :=
  (∀ U V : S → Prop, (∀ x, U x <-> V x) → T U → T V) /\
  (∀ F : (S → Prop) → Prop, (∀ U, F U → T U) →
       T (fun x => ex (fun U => F U /\ U x))) /\
  T (fun _ => True) /\
  (∀ U V : S → Prop, T U → T V → T (fun x => U x /\ V x)).

(* The opens of a space form a topology in that sense. *)
Lemma popen_topology@{o} (X : PTop@{o}) : PIsTopology X (POpen X).
Proof.
  split; [|split; [|split]].
  - exact (popen_respects X).
  - exact (popen_union X).
  - exact (popen_whole X).
  - exact (popen_inter X).
Qed.

Section Initial.

Universes o i.

Context (S : SetoidObject@{o o}) (I : Type@{i}) (X : I → PTop@{o})
        (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)).

(* The subbasic opens: preimages along some [t k] of an open of [X k]. *)
Definition pinit_sub (V : S → Prop) : Prop :=
  ex (fun k => ex (fun U : X k → Prop =>
    POpen (X k) U /\ ∀ s, V s <-> U (t k s))).

(* The weakest topology making every [t k] continuous: the predicates lying
   in every topology that contains the subbasic opens. *)
Definition pinit_open (V : S → Prop) : Prop :=
  ∀ T : (S → Prop) → Prop, PIsTopology S T →
    (∀ W, pinit_sub W → T W) → T V.

Lemma pinit_open_respects (U V : S → Prop) :
  (∀ x, U x <-> V x) → pinit_open U → pinit_open V.
Proof.
  intros H HU T HT Hs. exact (proj1 HT U V H (HU T HT Hs)).
Qed.

Definition pproper (V : S → Prop) : Prop :=
  ∀ x y : S, x ≈ y → V x → V y.

Lemma pproper_topology : PIsTopology S pproper.
Proof.
  split; [|split; [|split]].
  - intros U V H HU x y e v.
    apply (proj1 (H y)), (HU x y e), (proj2 (H x)), v.
  - intros F HF x y e [U [FU u]]. exists U. split; [exact FU|].
    exact (HF U FU x y e u).
  - intros x y _ w; exact w.
  - intros U V HU HV x y e [u v]. exact (conj (HU x y e u) (HV x y e v)).
Qed.

Lemma pinit_open_proper (U : S → Prop) :
  pinit_open U → ∀ x y : S, x ≈ y → U x → U y.
Proof.
  intro HU. apply (HU pproper pproper_topology).
  intros W [k [V [HV HW]]] x y e w.
  apply (proj2 (HW y)).
  apply (popen_proper (X k) V HV (t k x) (t k y) (proper_morphism (t k) x y e)).
  exact (proj1 (HW x) w).
Qed.

Lemma pinit_open_union (F : (S → Prop) → Prop) :
  (∀ U, F U → pinit_open U) → pinit_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF T HT Hs. apply (proj1 (proj2 HT)).
  intros U FU. exact (HF U FU T HT Hs).
Qed.

Lemma pinit_open_whole : pinit_open (fun _ => True).
Proof. intros T HT _. exact (proj1 (proj2 (proj2 HT))). Qed.

Lemma pinit_open_inter (U V : S → Prop) :
  pinit_open U → pinit_open V → pinit_open (fun x => U x /\ V x).
Proof.
  intros HU HV T HT Hs.
  exact (proj2 (proj2 (proj2 HT)) U V (HU T HT Hs) (HV T HT Hs)).
Qed.

(* A record literal over the five lemmas, so that the points and the opens
   read back at [eq_refl]. *)
Definition PInit : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := pinit_open;
  popen_respects := pinit_open_respects;
  popen_proper   := pinit_open_proper;
  popen_union    := pinit_open_union;
  popen_whole    := pinit_open_whole;
  popen_inter    := pinit_open_inter
|}.

Example PInit_carrier : pt_carrier PInit = S := eq_refl.

Example PInit_open (V : S → Prop) : POpen PInit V = pinit_open V := eq_refl.

(* Every [t k] is continuous out of the initial topology. *)
Lemma pinit_leg_cont (k : I) : @PCont PInit (X k) (t k).
Proof.
  intros U HU T HT Hs. apply Hs. exists k, U. split; [exact HU|].
  intro s; exact (iff_refl _).
Qed.

Definition pinit_leg (k : I) : PMor@{o} PInit (X k) :=
  @Build_PMor PInit (X k) (t k) (pinit_leg_cont k).

Example pinit_leg_map (k : I) : pmap (pinit_leg k) = t k := eq_refl.

(* The universal property over ARBITRARY spaces mapping in: a setoid map
   into [S] is continuous into the initial topology iff every composite
   with a [t k] is continuous. *)
Lemma pinit_universal (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z PInit g <->
  (∀ k, @PCont Z (X k) (setoid_morphism_compose@{o o o} (t k) g)).
Proof.
  split.
  - intros Hg k U HU. exact (Hg _ (pinit_leg_cont k U HU)).
  - intros Hk V HV.
    apply (HV (fun W => POpen Z (fun z => W (g z)))).
    + split; [|split; [|split]].
      * intros U W H HU.
        apply (popen_respects Z (fun z => U (g z))); [|exact HU].
        intro z; exact (H (g z)).
      * intros F HF.
        apply (popen_respects Z
                 (fun z => ex (fun W => (ex (fun U => F U /\
                    ∀ z', W z' <-> U (g z'))) /\ W z))).
        -- intro z; split.
           ++ intros [W [[U [FU HW]] w]]. exists U. split; [exact FU|].
              exact (proj1 (HW z) w).
           ++ intros [U [FU u]]. exists (fun z' => U (g z')). split; [|exact u].
              exists U. split; [exact FU|]. intro z'; exact (iff_refl _).
        -- apply popen_union. intros W [U [FU HW]].
           apply (popen_respects Z (fun z => U (g z))); [|exact (HF U FU)].
           intro z; exact (iff_sym (HW z)).
      * exact (popen_whole Z).
      * intros U W HU HW. exact (popen_inter Z _ _ HU HW).
    + intros W [k [U [HU HW]]].
      apply (popen_respects Z (fun z => U (t k (g z)))).
      * intro z; exact (iff_sym (HW (g z))).
      * exact (Hk k U HU).
Qed.

Definition pinit_lift (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z S)
  (Hk : ∀ k, @PCont Z (X k) (setoid_morphism_compose@{o o o} (t k) g)) :
  PMor@{o} Z PInit :=
  @Build_PMor Z PInit g (proj2 (pinit_universal Z g) Hk).

Example pinit_lift_map (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z S)
  (Hk : ∀ k, @PCont Z (X k) (setoid_morphism_compose@{o o o} (t k) g)) :
  pmap (pinit_lift Z g Hk) = g := eq_refl.

(* It is the WEAKEST topology making every [t k] continuous: every
   topology on [S] making each [t k] continuous contains all its opens. *)
Lemma pinit_weakest (T : (S → Prop) → Prop) (HT : PIsTopology S T)
  (Hc : ∀ k (U : X k → Prop), POpen (X k) U → T (fun s => U (t k s))) :
  ∀ V, pinit_open V → T V.
Proof.
  intros V HV. apply (HV T HT).
  intros W [k [U [HU HW]]]. apply (proj1 HT (fun s => U (t k s)) W).
  - intro s; exact (iff_sym (HW s)).
  - exact (Hc k U HU).
Qed.

End Initial.

(* One map: the initial topology along a single [h] is Instance/Top/
   Subspace.v's subspace topology [PSub], opens for opens. *)
Lemma PInit_one_PSub@{o +} (X : PTop@{o}) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} S X) (V : S → Prop) :
  POpen (PInit S Datatypes.unit (fun _ => X) (fun _ => h)) V <-> POpen (PSub X S h) V.
Proof.
  split.
  - apply (pinit_weakest S Datatypes.unit (fun _ => X) (fun _ => h)
             (POpen (PSub X S h)) (popen_topology (PSub X S h))).
    intros _ U HU. exists U. split; [exact HU|]. intro s; exact (iff_refl _).
  - intros [U [HU HV]].
    apply (pinit_open_respects S Datatypes.unit (fun _ => X) (fun _ => h)
             (fun s => U (h s))).
    + intro s; exact (iff_sym (HV s)).
    + exact (pinit_leg_cont S Datatypes.unit (fun _ => X) (fun _ => h) tt U HU).
Qed.

(** ** The recipe as a lemma: topologize a limit of the underlying sets *)

Section Recipe.

Universes j o so.
Constraint o < so.

Context {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}).

(* A cone over the underlying diagram, its apex given the initial topology
   for its legs. *)
Definition pinit_top (N : Cone (PForget@{o so} ◯ T)) : PTop@{o} :=
  PInit (vertex_obj[N]) (obj[J]) (fun k => fobj[T] k) (fun k => cone_leg N k).

Definition pinit_cone (N : Cone (PForget@{o so} ◯ T)) : Cone T.
Proof.
  unshelve refine (@Build_Cone J PTopCat@{o so} T (pinit_top N)
    (@Build_ACone J PTopCat@{o so} (pinit_top N) T
       (fun k => pinit_leg _ _ _ _ k) _)).
  intros x y f s; simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f s).
Defined.

Example pinit_cone_points (N : Cone (PForget@{o so} ◯ T)) :
  pt_carrier (vertex_obj[pinit_cone N]) = vertex_obj[N] := eq_refl.

Example pinit_cone_leg (N : Cone (PForget@{o so} ◯ T)) (k : obj[J]) :
  pmap (cone_leg (pinit_cone N) k) = cone_leg N k := eq_refl.

(* Riehl's recipe: a LIMITING cone over the underlying diagram, topologized
   by the initial topology for its legs, is a limiting cone over [T]. *)
Definition pinit_cone_limiting@{v v1 w w1 +}
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone@{v v1 j o so} N) :
  IsLimitCone@{w w1 j o so} (pinit_cone N).
Proof.
  intro M.
  unshelve refine
    {| unique_obj :=
         @Build_PMor (vertex_obj[M]) (pinit_top N)
           (unique_obj (HN (FCone PForget M))) _ |}.
  - apply (proj2 (pinit_universal _ _ _ _ (vertex_obj[M])
                    (unique_obj (HN (FCone PForget M))))).
    intro k.
    apply (pcont_respects (pmap (cone_leg M k))).
    + intro x. symmetry. exact (unique_property (HN (FCone PForget M)) k x).
    + exact (pcont (cone_leg M k)).
  - intro k. exact (unique_property (HN (FCone PForget M)) k).
  - intros v Hv. exact (uniqueness (HN (FCone PForget M)) (pmap v) Hv).
Defined.

Example pinit_cone_med_map (N : Cone (PForget@{o so} ◯ T))
  (HN : IsLimitCone N) (M : Cone T) :
  pmap (unique_obj (pinit_cone_limiting N HN M))
    = unique_obj (HN (FCone PForget M)) := eq_refl.

(* A chosen limit of the underlying diagram gives a limit of [T]. *)
Definition PTop_Limit_lift@{r0 r +}
  (L : Limit@{r0 j o so} (PForget@{o so} ◯ T)) : Limit@{r j o so} T :=
  limitcone_limit (pinit_cone L) (pinit_cone_limiting L (limit_limitcone L)).

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition plimit_point_cone (L : Cone T) (x : vertex_obj[L]) : Cone T.
Proof.
  unshelve refine (@Build_Cone J PTopCat@{o so} T PPoint@{o}
    (@Build_ACone J PTopCat@{o so} PPoint@{o} T (fun k =>
       pdisc_mor unit_setoid_object (fobj[T] k)
         (pconst unit_setoid_object (fobj[T] k) (pmap (cone_leg L k) x))) _)).
  intros k k' f u; simpl.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ L) k k' f x).
Defined.

Definition plimit_point (L : Cone T) (x : vertex_obj[L]) :
  PPoint@{o} ~{PTopCat@{o so}}~> vertex_obj[L] :=
  pdisc_mor unit_setoid_object (vertex_obj[L])
    (pconst unit_setoid_object (vertex_obj[L]) x).

Lemma plimit_points_jointly_monic (L : Cone T) (HL : IsLimitCone L)
  (x y : vertex_obj[L]) :
  (∀ k, pmap (cone_leg L k) x ≈ pmap (cone_leg L k) y) → x ≈ y.
Proof.
  intro Hxy.
  pose (U := HL (plimit_point_cone L x)).
  transitivity (pmap (unique_obj U) ttt).
  - symmetry. refine (uniqueness U (plimit_point L x) _ ttt).
    intros k u; simpl. reflexivity.
  - refine (uniqueness U (plimit_point L y) _ ttt).
    intros k u; simpl. symmetry. exact (Hxy k).
Qed.

Lemma PTop_limit_open_iff_initial (L : Cone T) (HL : IsLimitCone L)
  (V : vertex_obj[L] → Prop) :
  POpen (vertex_obj[L]) V <-> POpen (vertex_obj[pinit_cone (FCone PForget L)]) V.
Proof.
  split.
  - intro HV.
    pose (U := HL (pinit_cone (FCone PForget L))).
    assert (Hu : ∀ x, pmap (unique_obj U) x ≈ x).
    { intro x. apply (plimit_points_jointly_monic L HL).
      intro k. exact (unique_property U k x). }
    apply (popen_respects _ (fun x => V (pmap (unique_obj U) x))).
    + intro x; split; intro v.
      * exact (popen_proper _ V HV _ _ (Hu x) v).
      * exact (popen_proper _ V HV _ _ (symmetry (Hu x)) v).
    + exact (pcont (unique_obj U) V HV).
  - apply (pinit_weakest _ _ _ _ (POpen (vertex_obj[L]))
             (popen_topology (vertex_obj[L]))).
    intros k U HU. exact (pcont (cone_leg L k) U HU).
Qed.

End Recipe.

(** ** The discrete-space functor, left adjoint to the points *)

Section Discrete.

Universes o so.
Constraint o < so.

Program Definition PDisc : Sets@{o so} ⟶ PTopCat@{o so} := {|
  fobj := fun S => PDiscrete S;
  fmap := fun S T f => pdisc_mor S (PDiscrete T) f
|}.
Next Obligation. intros S T f g H x; exact (H x). Qed.
Next Obligation. intros S x; reflexivity. Qed.
Next Obligation. intros S T U f g x; reflexivity. Qed.

Program Definition pdisc_forget_iso (S : Sets@{o so}) (X : PTopCat@{o so}) :
  @Isomorphism Sets
    {| carrier := @hom PTopCat@{o so} (PDisc S) X
     ; is_setoid := @homset PTopCat@{o so} (PDisc S) X |}
    {| carrier := @hom Sets@{o so} S (PForget X)
     ; is_setoid := @homset Sets@{o so} S (PForget X) |} := {|
  to   := {| morphism := fun k => pmap k |};
  from := {| morphism := fun f => pdisc_mor S X f |}
|}.
Next Obligation. intros S X k k' H x; exact (H x). Qed.
Next Obligation. intros S X f g H x; exact (H x). Qed.
Next Obligation. intros S X f x; reflexivity. Qed.
Next Obligation. intros S X k x; reflexivity. Qed.

Definition PDisc_PForget : PDisc ⊣ PForget@{o so}.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PDisc PForget pdisc_forget_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

Definition PForget_Continuous : ContinuousFunctor PForget@{o so} :=
  right_adjoint_Continuous PDisc_PForget.

End Discrete.

(* Per shape, with the shape universe named. *)
Definition PForget_PreservesLimitCone@{s o so +| o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  PreservesLimitCone T PForget@{o so} :=
  right_adjoint_PreservesLimitCone PDisc_PForget T.

(** ** Products: the product topology *)

Section Product.

Universes i o.
Constraint i <= o.

Context (A : Type@{i}) (X : A → PTop@{o}).

Definition PProd_carrier : SetoidObject@{o o} :=
  Sets_iprod_obj@{i o o o o} (fun a => pt_carrier (X a)).

Definition pprod_leg (a : A) : SetoidMorphism@{o o o} PProd_carrier (X a).
Proof.
  unshelve refine {| morphism := fun x : PProd_carrier => x a |}.
  intros x y e. exact (e a).
Defined.

Definition PProd : PTop@{o} := PInit PProd_carrier A X pprod_leg.

Definition pproj (a : A) : PMor@{o} PProd (X a) :=
  pinit_leg PProd_carrier A X pprod_leg a.

Definition pprod_tuple (Z : PTop@{o}) (f : ∀ a, PMor@{o} Z (X a)) :
  SetoidMorphism@{o o o} Z PProd_carrier.
Proof.
  unshelve refine {| morphism := fun z a => pmap (f a) z |}.
  intros z z' e a. exact (proper_morphism (pmap (f a)) z z' e).
Defined.

Definition ptuple (Z : PTop@{o}) (f : ∀ a, PMor@{o} Z (X a)) :
  PMor@{o} Z PProd :=
  pinit_lift PProd_carrier A X pprod_leg Z (pprod_tuple Z f)
    (fun a => pcont (f a)).

End Product.

Program Definition PTop_iprod_ump@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) (Z : PTop@{o})
  (pi : ∀ a : A, Z ~{PTopCat@{o so}}~> X a) :
  ∃! u : Z ~{PTopCat@{o so}}~> PProd A X,
    ∀ a : A, @compose PTopCat@{o so} _ _ _ (pproj A X a) u ≈ pi a := {|
  unique_obj := ptuple A X Z pi
|}.
Next Obligation. intros A X Z pi a x; reflexivity. Qed.
Next Obligation. intros A X Z pi v Hv x a; symmetry; exact (Hv a x). Qed.

Definition PTop_IsIndexedProduct@{i o so +| i <= o, o < so +} (A : Type@{i})
  (X : A → PTop@{o}) :
  @IsIndexedProduct PTopCat@{o so} A X (PProd A X) (pproj A X) :=
  @Build_IsIndexedProduct PTopCat@{o so} A X (PProd A X) (pproj A X)
    (fun Z pi => PTop_iprod_ump A X Z pi).

Definition PTop_HasIndexedProducts@{i o so +| i <= o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  @Build_HasIndexedProducts PTopCat@{o so}
    (@PProd) (@pproj) (@PTop_IsIndexedProduct).

(* The product IS the product topology on the product of the points. *)
Example PTop_product_obj@{i o so +| i <= o, o < so +} (A : Type@{i})
  (X : A → PTop@{o}) :
  @indexed_product PTopCat@{o so} PTop_HasIndexedProducts A X = PProd A X :=
  eq_refl.

Example PProd_open@{i o +| i <= o +} (A : Type@{i}) (X : A → PTop@{o})
  (V : PProd_carrier A X → Prop) :
  POpen (PProd A X) V = pinit_open (PProd_carrier A X) A X (pprod_leg A X) V :=
  eq_refl.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section ProductForced.

Universes i o so.
Constraint i <= o.
Constraint o < so.

Context (A : Type@{i}) (X : A → PTop@{o}) (Y : PTop@{o})
        (p : ∀ a, Y ~{PTopCat@{o so}}~> X a)
        (H : @IsIndexedProduct PTopCat@{o so} A X Y p).

Lemma iprod_points_jointly_monic (y y' : Y) :
  (∀ a, pmap (p a) y ≈ pmap (p a) y') → y ≈ y'.
Proof using H.
  intro Hyy.
  pose (U := iprod_desc H (c := PPoint@{o})
               (fun a => pdisc_mor unit_setoid_object (X a)
                  (pconst unit_setoid_object (X a) (pmap (p a) y)))).
  transitivity (pmap (unique_obj U) ttt).
  - symmetry.
    refine (uniqueness U (pdisc_mor unit_setoid_object Y
                            (pconst unit_setoid_object Y y)) _ ttt).
    intros a u; simpl. reflexivity.
  - refine (uniqueness U (pdisc_mor unit_setoid_object Y
                            (pconst unit_setoid_object Y y')) _ ttt).
    intros a u; simpl. symmetry. exact (Hyy a).
Qed.

Lemma PTop_iprod_open_iff_initial (V : Y → Prop) :
  POpen Y V <-> POpen (PInit Y A X (fun a => pmap (p a))) V.
Proof using H.
  split.
  - intro HV.
    pose (U := iprod_desc H (c := PInit Y A X (fun a => pmap (p a)))
                 (pinit_leg Y A X (fun a => pmap (p a)))).
    assert (Hu : ∀ y, pmap (unique_obj U) y ≈ y).
    { intro y. apply iprod_points_jointly_monic.
      intro a. exact (unique_property U a y). }
    apply (popen_respects _ (fun y => V (pmap (unique_obj U) y))).
    + intro y; split; intro v.
      * exact (popen_proper _ V HV _ _ (Hu y) v).
      * exact (popen_proper _ V HV _ _ (symmetry (Hu y)) v).
    + exact (pcont (unique_obj U) V HV).
  - apply (pinit_weakest _ _ _ _ (POpen Y) (popen_topology Y)).
    intros a U HU. exact (pcont (p a) U HU).
Qed.

End ProductForced.

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section EqualizerForced.

Universes o so.
Constraint o < so.

Context {X Y : PTop@{o}} (f g : X ~{PTopCat@{o so}}~> Y) (E : PTop@{o})
        (e : E ~{PTopCat@{o so}}~> X)
        (H : @IsEqualizer PTopCat@{o so} X Y f g E e).

Lemma equalizer_points_monic (y y' : E) : pmap e y ≈ pmap e y' → y ≈ y'.
Proof using H.
  intro Hyy.
  pose (pt := fun z : E =>
          pdisc_mor unit_setoid_object E (pconst unit_setoid_object E z)
          : PPoint@{o} ~{PTopCat@{o so}}~> E).
  assert (Hf : f ∘ (e ∘ pt y) ≈ g ∘ (e ∘ pt y)).
  { intro u. exact (fork_eq H (pmap (pt y) u)). }
  pose (U := eq_desc H (e ∘ pt y) Hf).
  transitivity (pmap (unique_obj U) ttt).
  - symmetry. refine (uniqueness U (pt y) _ ttt).
    intro u; simpl. reflexivity.
  - refine (uniqueness U (pt y') _ ttt).
    intro u; simpl. symmetry. exact Hyy.
Qed.

Lemma PTop_equalizer_open_iff_PSub (V : E → Prop) :
  POpen E V <-> POpen (PSub X E (pmap e)) V.
Proof using H.
  split.
  - intro HV.
    assert (Hf : f ∘ psub_incl X E (pmap e) ≈ g ∘ psub_incl X E (pmap e)).
    { intro y. exact (fork_eq H y). }
    pose (U := eq_desc H (psub_incl X E (pmap e)) Hf).
    assert (Hu : ∀ y, pmap (unique_obj U) y ≈ y).
    { intro y. apply equalizer_points_monic. exact (unique_property U y). }
    apply (popen_respects _ (fun y => V (pmap (unique_obj U) y))).
    + intro y; split; intro v.
      * exact (popen_proper _ V HV _ _ (Hu y) v).
      * exact (popen_proper _ V HV _ _ (symmetry (Hu y)) v).
    + exact (pcont (unique_obj U) V HV).
  - intros [U [HU HVU]].
    apply (popen_respects E (fun y => U (pmap e y))).
    + intro y; exact (iff_sym (HVU y)).
    + exact (pcont e U HU).
Qed.

End EqualizerForced.

(** ** Remark 1: completeness *)

(* Directly, by the recipe: at every shape universe at or below the
   points', with the limit's universe free above them. *)
Definition PTop_Complete@{r s o so +| s <= o, o < so, o <= r +} :
  @Complete@{r s o so} PTopCat@{o so} :=
  fun J T => PTop_Limit_lift T (Sets_Limit (PForget ◯ T)).

(* Its limit is the initial topology on Instance/Sets/Complete.v's
   compatible families. *)
Example PTop_Complete_apex@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T)]
    = pinit_top T (Sets_limit_cone (PForget ◯ T)) := eq_refl.

(* By the book's route: products and equalizers, through #416's
   [Complete_from_products_equalizers] and #457's [PTop_HasEqualizers]. *)
Definition PTop_Complete_via_products@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} :=
  @Complete_from_products_equalizers PTopCat@{o so}
    PTop_HasIndexedProducts PTop_HasEqualizers.

(* Its limit is a subspace of a product space: #416's equalizer of two maps
   out of the product over the objects of the shape, which #457's
   [PTop_HasEqualizers] makes a [PSub]. *)
Lemma PTop_Complete_via_products_apex@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  ex (fun S => ex (fun h =>
    vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)]
      = PSub (PProd (obj[J]) (fun j => fobj[T] j)) S h)).
Proof. eexists. eexists. reflexivity. Qed.

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PTop_Complete_routes_iso@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete J T)]
    ≅[PTopCat@{o so}]
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)] :=
  limit_unique_iso (limit_is_alimit _) (limit_is_alimit _).

Lemma PTop_Complete_routes_iso_legs@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) (j : J) :
  limit_leg (limit_is_alimit (PTop_Complete_via_products J T)) j
    ∘ to (PTop_Complete_routes_iso J T)
  ≈ limit_leg (limit_is_alimit (PTop_Complete J T)) j.
Proof. exact (fst (limit_unique_iso_legs _ _) j). Qed.

(** ** Awodey §2.6: the binary product, and its opens as unions of boxes *)

Section Binary.

Universe o.

Context (X1 X2 : PTop@{o}).

(* The pairs, with Lib/Datatypes.v's componentwise [prod_setoid]. *)
Definition PPair_carrier : SetoidObject@{o o} :=
  {| carrier := (pt_carrier X1 * pt_carrier X2)%type;
     is_setoid := prod_setoid |}.

Definition ppair_fst : SetoidMorphism@{o o o} PPair_carrier X1.
Proof.
  unshelve econstructor; [exact (fun q : PPair_carrier => fst q)|].
  intros q q' e. exact (fst e).
Defined.

Definition ppair_snd : SetoidMorphism@{o o o} PPair_carrier X2.
Proof.
  unshelve econstructor; [exact (fun q : PPair_carrier => snd q)|].
  intros q q' e. exact (snd e).
Defined.

Definition ppair_fam (b : bool) : PTop@{o} := if b then X1 else X2.

Definition ppair_leg (b : bool) : SetoidMorphism@{o o o} PPair_carrier (ppair_fam b) :=
  match b with true => ppair_fst | false => ppair_snd end.

Definition PPair : PTop@{o} := PInit PPair_carrier bool ppair_fam ppair_leg.

(* Awodey: "every W ∈ O(X × Y) is a union of such basic opens" U × V. *)
Definition pair_box_union (W : PPair_carrier → Prop) : Prop :=
  ∀ q, W q <-> ex (fun U1 : X1 → Prop => ex (fun U2 : X2 → Prop =>
    POpen X1 U1 /\ POpen X2 U2 /\
    (∀ q' : PPair_carrier, U1 (fst q') → U2 (snd q') → W q') /\
    U1 (fst q) /\ U2 (snd q))).

Lemma pair_box_union_topology : PIsTopology PPair_carrier pair_box_union.
Proof.
  split; [|split; [|split]].
  - intros U V H HU q. split.
    + intro v. destruct (proj1 (HU q) (proj2 (H q) v))
        as [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]].
      exists U1, U2. repeat split; try assumption.
      intros q' a b. exact (proj1 (H q') (Hb q' a b)).
    + intros [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]]. exact (Hb q u1 u2).
  - intros F HF q. split.
    + intros [U [FU u]].
      destruct (proj1 (HF U FU q) u) as [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]].
      exists U1, U2. repeat split; try assumption.
      intros q' a b. exists U. exact (conj FU (Hb q' a b)).
    + intros [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]]. exact (Hb q u1 u2).
  - intro q. split.
    + intros _. exists (fun _ => True), (fun _ => True).
      repeat split; try exact (popen_whole _).
    + intros _; exact I.
  - intros U V HU HV q. split.
    + intros [u v].
      destruct (proj1 (HU q) u) as [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]].
      destruct (proj1 (HV q) v) as [V1 [V2 [o1' [o2' [Hb' [v1 v2]]]]]].
      exists (fun x => U1 x /\ V1 x), (fun y => U2 y /\ V2 y).
      split; [exact (popen_inter _ _ _ o1 o1')|].
      split; [exact (popen_inter _ _ _ o2 o2')|].
      split; [|exact (conj (conj u1 v1) (conj u2 v2))].
      intros q' [a1 b1] [a2 b2]. exact (conj (Hb q' a1 a2) (Hb' q' b1 b2)).
    + intros [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]]. exact (Hb q u1 u2).
Qed.

Theorem PPair_open_iff_box (W : PPair_carrier → Prop) :
  POpen PPair W <-> pair_box_union W.
Proof.
  split.
  - intro HW. apply (HW pair_box_union pair_box_union_topology).
    intros V [b [U [HU HV]]] q. split.
    + intro v. destruct b; simpl in *.
      * exists U, (fun _ => True). repeat split; try assumption.
        -- exact (popen_whole _).
        -- intros q' a _. exact (proj2 (HV q') a).
        -- exact (proj1 (HV q) v).
      * exists (fun _ => True), U. repeat split; try assumption.
        -- exact (popen_whole _).
        -- intros q' _ a. exact (proj2 (HV q') a).
        -- exact (proj1 (HV q) v).
    + intros [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]]. exact (Hb q u1 u2).
  - intro HW.
    apply (popen_respects PPair
      (fun q => ex (fun B => (ex (fun U1 : X1 → Prop => ex (fun U2 : X2 → Prop =>
          POpen X1 U1 /\ POpen X2 U2 /\
          (∀ q', B q' <-> U1 (fst q') /\ U2 (snd q')) /\
          (∀ q', B q' → W q')))) /\ B q))).
    + intro q; split.
      * intros [B [[U1 [U2 [_ [_ [HB HBW]]]]] b]]. exact (HBW q b).
      * intro w. destruct (proj1 (HW q) w) as [U1 [U2 [o1 [o2 [Hb [u1 u2]]]]]].
        exists (fun q' => U1 (fst q') /\ U2 (snd q')).
        split; [|exact (conj u1 u2)].
        exists U1, U2. split; [exact o1|]. split; [exact o2|]. split.
        -- intro q'; exact (iff_refl _).
        -- intros q' [a b]; exact (Hb q' a b).
    + apply popen_union. intros B [U1 [U2 [o1 [o2 [HB _]]]]].
      apply (popen_respects PPair (fun q => U1 (fst q) /\ U2 (snd q))).
      * intro q; exact (iff_sym (HB q)).
      * apply popen_inter.
        -- exact (pinit_leg_cont PPair_carrier bool ppair_fam ppair_leg true U1 o1).
        -- exact (pinit_leg_cont PPair_carrier bool ppair_fam ppair_leg false U2 o2).
Qed.

Definition ppair_exl : PMor@{o} PPair X1 :=
  pinit_leg PPair_carrier bool ppair_fam ppair_leg true.

Definition ppair_exr : PMor@{o} PPair X2 :=
  pinit_leg PPair_carrier bool ppair_fam ppair_leg false.

Definition ppair_fork_map (Z : PTop@{o}) (f : PMor@{o} Z X1) (g : PMor@{o} Z X2) :
  SetoidMorphism@{o o o} Z PPair_carrier.
Proof.
  unshelve refine {| morphism := fun z => (pmap f z, pmap g z) |}.
  intros z z' e. split.
  - exact (proper_morphism (pmap f) z z' e).
  - exact (proper_morphism (pmap g) z z' e).
Defined.

(* Awodey's second bullet: the pairing of two continuous maps is
   continuous, here by the initial topology's universal property. *)
Definition ppair_fork (Z : PTop@{o}) (f : PMor@{o} Z X1) (g : PMor@{o} Z X2) :
  PMor@{o} Z PPair.
Proof.
  refine (pinit_lift PPair_carrier bool ppair_fam ppair_leg Z
            (ppair_fork_map Z f g) _).
  intros [|].
  - exact (pcont f).
  - exact (pcont g).
Defined.

End Binary.

Definition PTop_Cartesian@{o so +| o < so +} : @Cartesian PTopCat@{o so}.
Proof.
  unshelve refine (@Build_Cartesian PTopCat@{o so} (fun x y => PPair x y)
    (fun x y z f g => ppair_fork y z x f g)
    (fun x y => ppair_exl x y) (fun x y => ppair_exr x y) _ _).
  - intros x y z f f' Hf g g' Hg w. split; [exact (Hf w)|exact (Hg w)].
  - intros x y z f g h. split.
    + intro Hh. split; intro w; [exact (fst (Hh w))|exact (snd (Hh w))].
    + intros [Hl Hr] w. split; [exact (Hl w)|exact (Hr w)].
Defined.

(** ** Riehl §3.1 Example 10: the box topology, a non-example *)

Section Box.

Universes i o.
Constraint i <= o.

Context (A : Type@{i}) (X : A → PTop@{o}).

(* The box topology on the product of the underlying sets: W is open when
   it respects the points' equality and every point of W lies in a box of
   opens, one per index, inside W. *)
Definition pbox_open (W : PProd_carrier A X → Prop) : Prop :=
  (∀ x y : PProd_carrier A X, x ≈ y → W x → W y) /\
  ∀ x, W x → ex (fun U : ∀ a, X a → Prop =>
    (∀ a, POpen (X a) (U a)) /\ (∀ a, U a (x a)) /\
    ∀ y : PProd_carrier A X, (∀ a, U a (y a)) → W y).

Lemma pbox_open_respects (U V : PProd_carrier A X → Prop) :
  (∀ x, U x <-> V x) → pbox_open U → pbox_open V.
Proof.
  intros H [HUp HU]. split.
  - intros x y e v. apply (proj1 (H y)), (HUp x y e), (proj2 (H x)), v.
  - intros x v. destruct (HU x (proj2 (H x) v)) as [B [HB [Bx HBW]]].
    exists B. split; [exact HB|]. split; [exact Bx|].
    intros y Hy. exact (proj1 (H y) (HBW y Hy)).
Qed.

Lemma pbox_open_proper (U : PProd_carrier A X → Prop) :
  pbox_open U → ∀ x y : PProd_carrier A X, x ≈ y → U x → U y.
Proof. intros [HUp _]. exact HUp. Qed.

Lemma pbox_open_union (F : (PProd_carrier A X → Prop) → Prop) :
  (∀ U, F U → pbox_open U) →
  pbox_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF. split.
  - intros x y e [U [FU u]]. exists U. split; [exact FU|].
    exact (proj1 (HF U FU) x y e u).
  - intros x [U [FU u]]. destruct (proj2 (HF U FU) x u) as [B [HB [Bx HBW]]].
    exists B. split; [exact HB|]. split; [exact Bx|].
    intros y Hy. exists U. exact (conj FU (HBW y Hy)).
Qed.

Lemma pbox_open_whole : pbox_open (fun _ => True).
Proof.
  split.
  - intros; exact I.
  - intros x _. exists (fun _ _ => True). split; [|split].
    + intro a. exact (popen_whole (X a)).
    + intro a. exact I.
    + intros; exact I.
Qed.

Lemma pbox_open_inter (U V : PProd_carrier A X → Prop) :
  pbox_open U → pbox_open V → pbox_open (fun x => U x /\ V x).
Proof.
  intros [HUp HU] [HVp HV]. split.
  - intros x y e [u v]. exact (conj (HUp x y e u) (HVp x y e v)).
  - intros x [u v].
    destruct (HU x u) as [B [HB [Bx HBW]]], (HV x v) as [C [HC [Cx HCW]]].
    exists (fun a b => B a b /\ C a b). split; [|split].
    + intro a. exact (popen_inter (X a) _ _ (HB a) (HC a)).
    + intro a. exact (conj (Bx a) (Cx a)).
    + intros y Hy. split.
      * apply HBW. intro a. exact (proj1 (Hy a)).
      * apply HCW. intro a. exact (proj2 (Hy a)).
Qed.

Definition PBoxTop : PTop@{o} := {|
  pt_carrier     := PProd_carrier A X;
  POpen          := pbox_open;
  popen_respects := pbox_open_respects;
  popen_proper   := pbox_open_proper;
  popen_union    := pbox_open_union;
  popen_whole    := pbox_open_whole;
  popen_inter    := pbox_open_inter
|}.

(* The box that is [V] at the index [a] and the whole space elsewhere,
   for an index type with decidable equality. *)
Definition pbox_at (dec : ∀ a b : A, {a = b} + {a ≠ b}) (a : A)
  (V : X a → Prop) (c : A) : X c → Prop :=
  match dec c a with
  | left e => fun y => V (eq_rect c X y a e)
  | right _ => fun _ => True
  end.

(* The projections out of the box space are continuous. *)
Lemma pbox_proj_cont (dec : ∀ a b : A, {a = b} + {a ≠ b}) (a : A) :
  @PCont PBoxTop (X a) (pprod_leg A X a).
Proof.
  intros V HV. split.
  - intros x y e v. exact (popen_proper (X a) V HV (x a) (y a) (e a) v).
  - intros x v. exists (pbox_at dec a V). split; [|split].
    + intro c. unfold pbox_at. destruct (dec c a) as [e|n].
      * destruct e. exact HV.
      * exact (popen_whole (X c)).
    + intro c. unfold pbox_at. destruct (dec c a) as [e|n].
      * destruct e. exact v.
      * exact I.
    + intros y Hy. specialize (Hy a). unfold pbox_at in Hy.
      destruct (dec a a) as [e|n].
      * rewrite (UIP_dec dec e eq_refl) in Hy. exact Hy.
      * destruct (n eq_refl).
Qed.

Definition pbox_proj (dec : ∀ a b : A, {a = b} + {a ≠ b}) (a : A) :
  PMor@{o} PBoxTop (X a) :=
  @Build_PMor PBoxTop (X a) (pprod_leg A X a) (pbox_proj_cont dec a).

(* The box topology is finer than the product topology. *)
Lemma pprod_open_pbox_open (dec : ∀ a b : A, {a = b} + {a ≠ b})
  (W : PProd_carrier A X → Prop) :
  POpen (PProd A X) W → POpen PBoxTop W.
Proof.
  apply (pinit_weakest _ _ _ _ pbox_open (popen_topology PBoxTop)).
  intros a U HU. exact (pbox_proj_cont dec a U HU).
Qed.

End Box.

(* The witness: the convergent sequence ℕ∞, [None] its limit point, and
   the indicator maps of its points into the two-point discrete space. *)
Section BoxNot.

Universe o.

Definition pconv_setoid : SetoidObject@{o o} :=
  {| carrier := option nat; is_setoid := eq_Setoid (option nat) |}.

(* Open: containing the limit point forces a tail of the sequence. *)
Definition pconv_open (V : pconv_setoid → Prop) : Prop :=
  V None → ex (fun N => ∀ m, (N <= m)%nat → V (Some m)).

Lemma pconv_open_respects (U V : pconv_setoid → Prop) :
  (∀ x, U x <-> V x) → pconv_open U → pconv_open V.
Proof.
  intros H HU v. destruct (HU (proj2 (H None) v)) as [N HN].
  exists N. intros m Hm. exact (proj1 (H (Some m)) (HN m Hm)).
Qed.

Lemma pconv_open_proper (U : pconv_setoid → Prop) :
  pconv_open U → ∀ x y : pconv_setoid, x ≈ y → U x → U y.
Proof. intros _ x y e u. simpl in e. subst y. exact u. Qed.

Lemma pconv_open_union (F : (pconv_setoid → Prop) → Prop) :
  (∀ U, F U → pconv_open U) → pconv_open (fun x => ex (fun U => F U /\ U x)).
Proof.
  intros HF [U [FU u]]. destruct (HF U FU u) as [N HN].
  exists N. intros m Hm. exists U. exact (conj FU (HN m Hm)).
Qed.

Lemma pconv_open_whole : pconv_open (fun _ => True).
Proof. intros _. exists O. intros; exact I. Qed.

Lemma pconv_open_inter (U V : pconv_setoid → Prop) :
  pconv_open U → pconv_open V → pconv_open (fun x => U x /\ V x).
Proof.
  intros HU HV [u v].
  destruct (HU u) as [N HN], (HV v) as [M HM].
  exists (N + M)%nat. intros m Hm. split.
  - apply HN. apply (Nat.le_trans _ (N + M)%nat); [apply Nat.le_add_r|exact Hm].
  - apply HM. apply (Nat.le_trans _ (N + M)%nat); [|exact Hm].
    rewrite Nat.add_comm. apply Nat.le_add_r.
Qed.

Definition PConv : PTop@{o} := {|
  pt_carrier     := pconv_setoid;
  POpen          := pconv_open;
  popen_respects := pconv_open_respects;
  popen_proper   := pconv_open_proper;
  popen_union    := pconv_open_union;
  popen_whole    := pconv_open_whole;
  popen_inter    := pconv_open_inter
|}.

(* The limit point alone is not open. *)
Lemma pconv_limit_point_not_open : POpen PConv (fun z => z = None) → False.
Proof.
  intro H. destruct (H eq_refl) as [N HN]. discriminate (HN N (le_n N)).
Qed.

Definition pconv_ind (n : nat) (z : option nat) : bool :=
  match z with None => false | Some m => Nat.eqb m n end.

Definition pconv_ind_map (n : nat) : SetoidMorphism@{o o o} pconv_setoid PBool@{o}.
Proof.
  unshelve econstructor; [exact (pconv_ind n)|].
  intros x y e. simpl in e. subst y. reflexivity.
Defined.

(* Every indicator is continuous: past [n] the sequence is at [false], the
   value at the limit point. *)
Lemma pconv_ind_cont (n : nat) : @PCont PConv PBool@{o} (pconv_ind_map n).
Proof.
  intros V HV v. exists (S n). intros m Hm. simpl in *.
  assert (E : Nat.eqb m n = false).
  { apply Nat.eqb_neq. intro H. subst m. exact (Nat.nle_succ_diag_l _ Hm). }
  rewrite E. exact v.
Qed.

Definition pconv_ind_mor (n : nat) : PMor@{o} PConv PBool@{o} :=
  @Build_PMor PConv PBool (pconv_ind_map n) (pconv_ind_cont n).

(* The point of the box space all of whose coordinates are [false] is an
   open box, a product of opens of [PBool]. *)
Definition pbox_all_false (x : PProd_carrier nat (fun _ => PBool@{o})) : Prop :=
  ∀ n, x n = false.

Lemma pbox_all_false_open :
  POpen (PBoxTop nat (fun _ => PBool@{o})) pbox_all_false.
Proof.
  split.
  - intros x y e w n. rewrite <- (e n). exact (w n).
  - intros x w. exists (fun _ b => b = false). split; [|split].
    + intros n b b' e H. simpl in e. rewrite <- e. exact H.
    + exact w.
    + intros y Hy. exact Hy.
Qed.

(* No continuous map from ℕ∞ into the box space has the indicators as
   components: it would pull [pbox_all_false] back to the limit point alone. *)
Theorem pbox_no_mediator (u : PMor@{o} PConv (PBoxTop nat (fun _ => PBool@{o})))
  (Hu : ∀ n z, pmap u z n = pconv_ind n z) : False.
Proof.
  apply pconv_limit_point_not_open.
  apply (popen_respects PConv (fun z => pbox_all_false (pmap u z))).
  - intro z; split.
    + intro H. destruct z as [m|]; [|reflexivity].
      specialize (H m). rewrite Hu in H. simpl in H.
      rewrite Nat.eqb_refl in H. discriminate H.
    + intros ->. intro n. rewrite Hu. reflexivity.
  - exact (pcont u pbox_all_false pbox_all_false_open).
Qed.

End BoxNot.

(* The box space with its continuous projections is NOT an indexed product
   of [PBool] over [nat] in [PTopCat]. *)
Theorem box_not_indexed_product@{o so +| o < so +} :
  @IsIndexedProduct PTopCat@{o so} nat (fun _ => PBool@{o})
    (PBoxTop nat (fun _ => PBool@{o})) (pbox_proj nat (fun _ => PBool@{o}) Nat.eq_dec)
  → False.
Proof.
  intro H.
  destruct (iprod_desc H (c := PConv@{o}) pconv_ind_mor) as [u Hu _].
  apply (pbox_no_mediator u). intros n z. exact (Hu n z).
Qed.

(* Whereas the product topology mediates: the tuple of the indicators. *)
Definition pconv_prod_mediator@{o +} :
  PMor@{o} PConv@{o} (PProd nat (fun _ => PBool@{o})) :=
  ptuple nat (fun _ => PBool) PConv pconv_ind_mor.

(* So [pbox_all_false] is box-open and not product-open: the box topology is
   strictly finer on an infinite product. *)
Theorem pbox_all_false_not_product_open@{o +} :
  POpen (PProd nat (fun _ => PBool@{o})) pbox_all_false → False.
Proof.
  intro H.
  apply pconv_limit_point_not_open.
  apply (popen_respects PConv (fun z => pbox_all_false (pmap pconv_prod_mediator z))).
  - intro z; split.
    + intro Hz. destruct z as [m|]; [|reflexivity].
      specialize (Hz m). simpl in Hz. rewrite Nat.eqb_refl in Hz. discriminate Hz.
    + intros ->. intro n. reflexivity.
  - exact (pcont pconv_prod_mediator pbox_all_false H).
Qed.
