Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Quotient.

Generalizable All Variables.

(* * * The 范畴 pairs, X/A 左伴随 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/Top
 nLab:      https://ncatlab.org/nlab/show/pointed+object
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)
 Book:      A. Hatcher, "Algebraic Topology", Cambridge University Press

   本文件给出商相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* * ** The 范畴 pairs [Top^(2)] （已译） *)

(* 相关说明。 （已译） *)
Record PairTop@{o} := {
  pair_space :> TopSpace@{o};
  pair_sub : carrier (top_carrier pair_space) → Type@{o};
  pair_sub_proper : ∀ x y, x ≈ y → pair_sub x → pair_sub y
}.

(* A map pairs: continuous map carrying subset 进入 subset. （已译） *)
Record PairMap@{h o | o < h +} (X Y : PairTop@{o}) := {
  pair_map :> pair_space X ~{Top@{h o}}~> pair_space Y;
  pair_carries : ∀ x, pair_sub X x → pair_sub Y (pair_map x)
}.

Arguments pair_map {X Y} _.
Arguments pair_carries {X Y} _ _ _.

(* 相关说明。 （已译） *)
Lemma PairMap_equiv_Equivalence@{h o | o < h +} {X Y : PairTop@{o}} :
  Equivalence (fun p q : PairMap@{h o} X Y => pair_map p ≈ pair_map q).
Proof.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; symmetry; exact Hpq.
  - intros p q r Hpq Hqr.
    transitivity (pair_map q); [ exact Hpq | exact Hqr ].
Qed.

#[export]
Instance PairMap_Setoid@{h o | o < h +} {X Y : PairTop@{o}} :
  Setoid@{h h} (PairMap@{h o} X Y) := {|
  equiv := fun p q => pair_map p ≈ pair_map q;
  setoid_equiv := PairMap_equiv_Equivalence@{h o}
|}.

Definition pair_id@{h o | o < h +} {X : PairTop@{o}} : PairMap@{h o} X X :=
  @Build_PairMap@{h o} X X (@id Top@{h o} (pair_space X)) (fun x a => a).

Definition pair_compose@{h o | o < h +} {X Y Z : PairTop@{o}}
  (p : PairMap@{h o} Y Z) (q : PairMap@{h o} X Y) : PairMap@{h o} X Z :=
  @Build_PairMap@{h o} X Z (pair_map p ∘[Top@{h o}] pair_map q)
    (fun x a => pair_carries p _ (pair_carries q x a)).

Lemma pair_compose_respects@{h o | o < h +} {X Y Z : PairTop@{o}} :
  Proper (equiv ==> equiv ==> equiv) (@pair_compose@{h o} X Y Z).
Proof.
  intros p p' Hp q q' Hq x; simpl.
  transitivity (pair_map p (pair_map q' x)).
  - apply proper_morphism; exact (Hq x).
  - exact (Hp (pair_map q' x)).
Qed.

(* Mac Lane's [Top^(2)].

 对象: pairs ⟨X, A⟩ (a space subset its points)
 arrows: maps carrying A into A'
 恒等: 恒等 map
 复合: 复合 continuous maps（已译） *)
Program Definition Top_pairs@{h o | o < h +} : Category@{h h h} := {|
  obj     := PairTop@{o};
  hom     := PairMap@{h o};
  homset  := @PairMap_Setoid@{h o};
  id      := @pair_id@{h o};
  compose := @pair_compose@{h o};

  compose_respects := @pair_compose_respects@{h o}
|}.
Next Obligation. intros X Y f x; simpl. reflexivity. Qed.
Next Obligation. intros X Y f x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z W f g k x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z W f g k x; simpl. reflexivity. Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition point_pair@{o} (Y : PointedTop@{o}) : PairTop@{o} :=
  @Build_PairTop@{o} (ptop_space Y) (fun y => y ≈ ptop_pt Y)
    (fun x y e h => transitivity (symmetry e) h).

Definition point_pair_map@{h o | o < h +} {X Y : PointedTop@{o}}
  (p : X ~{Top_pointed@{h o}}~> Y) :
  point_pair X ~{Top_pairs@{h o}}~> point_pair Y.
Proof.
  refine (@Build_PairMap@{h o} (point_pair X) (point_pair Y) (ptop_map p) _).
  intros x Hx; simpl in *.
  transitivity (ptop_map p (ptop_pt X)).
  - apply proper_morphism; exact Hx.
  - exact (ptop_preserves p).
Defined.

(* Y ↦ ⟨Y, *⟩. *)
Program Definition PointPair@{h o | o < h +} :
  Top_pointed@{h o} ⟶ Top_pairs@{h o} := {|
  fobj := point_pair@{o};
  fmap := @point_pair_map@{h o}
|}.
Next Obligation. intros X Y f g Hfg x; simpl. exact (Hfg x). Qed.
Next Obligation. intros X x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z f g x; simpl. reflexivity. Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition pquot_rel@{o} (X : PairTop@{o})
  (u v : option (carrier (top_carrier (pair_space X)))) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (pair_sub X x ∧ pair_sub X y))%type
  | Some x, None => pair_sub X x
  | None, Some y => pair_sub X y
  | None, None => poly_unit@{o}
  end.

Lemma pquot_rel_Equivalence@{o} (X : PairTop@{o}) :
  Equivalence (pquot_rel X).
Proof.
  constructor.
  - intros [x|]; simpl; [left; reflexivity | exact ttt].
  - intros [x|] [y|] H; simpl in *; try exact H.
    destruct H as [H|[H1 H2]]; [left; now symmetry | right; exact (H2, H1)].
  - intros [x|] [y|] [z|] H1 H2; simpl in *; try exact ttt.
    + destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']].
      * left; now transitivity y.
      * right; split;
          [ exact (pair_sub_proper X _ _ (symmetry H1) H2) | exact H2' ].
      * right; split; [ exact H1 | exact (pair_sub_proper X _ _ H2 H1') ].
      * right; exact (H1, H2').
    + destruct H1 as [H1|[H1 H1']].
      * exact (pair_sub_proper X _ _ (symmetry H1) H2).
      * exact H1.
    + right; exact (H1, H2).
    + exact H1.
    + destruct H2 as [H2|[H2 H2']].
      * exact (pair_sub_proper X _ _ H2 H1).
      * exact H2'.
    + exact H2.
Qed.

Definition pquot_setoid@{o} (X : PairTop@{o}) :
  Setoid@{o o} (option (carrier (top_carrier (pair_space X)))) := {|
  equiv := pquot_rel X;
  setoid_equiv := pquot_rel_Equivalence X
|}.

Definition pquot_carrier@{o} (X : PairTop@{o}) : SetoidObject@{o o} := {|
  carrier := option (carrier (top_carrier (pair_space X)));
  is_setoid := pquot_setoid X
|}.

Definition pquot_some@{o} (X : PairTop@{o}) :
  SetoidMorphism@{o o o} (top_carrier (pair_space X)) (pquot_carrier X) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier (pair_space X))) _
    (pquot_setoid X) (@Some _)
    (fun x y (e : x ≈ y) => (inl e : pquot_rel X (Some x) (Some y))).

(* 相关说明。 （已译） *)
Definition pquot_space@{o} (X : PairTop@{o}) : TopSpace@{o} :=
  TQuot (pair_space X) (pquot_carrier X) (pquot_some X).

Definition pquot_pointed@{o} (X : PairTop@{o}) : PointedTop@{o} :=
  @Build_PointedTop@{o} (pquot_space X) None.

Definition pquot_in@{h o | o < h +} (X : PairTop@{o}) :
  pair_space X ~{Top@{h o}}~> pquot_space X :=
  tquot_proj (pair_space X) (pquot_carrier X) (pquot_some X).

(** ** The functor ⟨X, A⟩ ↦ X/A *)

Definition pquot_fmap_map@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  SetoidMorphism@{o o o} (pquot_carrier X) (pquot_carrier Y).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _ (pquot_setoid Y)
       (fun u => match u with
                 | Some x => Some (pair_map f x)
                 | None => None
                 end) _).
  intros [x|] [y|] H; simpl in *; try exact H.
  - destruct H as [H|[H1 H2]].
    + left; apply proper_morphism; exact H.
    + right; exact (pair_carries f _ H1, pair_carries f _ H2).
  - exact (pair_carries f _ H).
  - exact (pair_carries f _ H).
Defined.

Lemma pquot_fmap_cont@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  Continuous (pquot_space X) (pquot_space Y) (pquot_fmap_map f).
Proof.
  intros V [HVp HVo]; split.
  - intros u v e w.
    exact (HVp _ _ (proper_morphism (pquot_fmap_map f) u v e) w).
  - exact (continuity (pair_map f) _ HVo).
Qed.

Definition pquot_fmap@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  pquot_pointed X ~{Top_pointed@{h o}}~> pquot_pointed Y :=
  @Build_PointedMap@{h o} (pquot_pointed X) (pquot_pointed Y)
    (@Build_ContinuousMorphism@{h o} (pquot_space X) (pquot_space Y)
       (pquot_fmap_map f) (pquot_fmap_cont f))
    ttt.

Program Definition PairQuotient@{h o | o < h +} :
  Top_pairs@{h o} ⟶ Top_pointed@{h o} := {|
  fobj := pquot_pointed@{o};
  fmap := @pquot_fmap@{h o}
|}.
Next Obligation.
  intros X Y f g Hfg [x|]; simpl; [ left; exact (Hfg x) | exact ttt ].
Qed.
Next Obligation. intros X [x|]; simpl; [ left; reflexivity | exact ttt ]. Qed.
Next Obligation.
  intros X Y Z f g [x|]; simpl; [ left; reflexivity | exact ttt ].
Qed.

(* 相关说明。 （已译） *)

(* Restrict a based map out of X/A along [Some]. *)
Definition pquot_to@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (p : pquot_pointed X ~{Top_pointed@{h o}}~> Y) :
  X ~{Top_pairs@{h o}}~> point_pair Y.
Proof.
  refine (@Build_PairMap@{h o} X (point_pair Y)
            (ptop_map p ∘[Top@{h o}] pquot_in X) _).
  intros x Hx; simpl.
  transitivity (ptop_map p None).
  - apply (proper_morphism (continuous_map (ptop_map p)) (Some x) None).
    exact Hx.
  - exact (ptop_preserves p).
Defined.

(* 相关说明。 （已译） *)
Definition pquot_from_map@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  SetoidMorphism@{o o o} (pquot_carrier X) (top_carrier (ptop_space Y)).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _
       (is_setoid (top_carrier (ptop_space Y)))
       (fun u => match u with
                 | Some x => pair_map g x
                 | None => ptop_pt Y
                 end) _).
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H1 H2]].
    + apply proper_morphism; exact H.
    + transitivity (ptop_pt Y).
      * exact (pair_carries g _ H1).
      * symmetry; exact (pair_carries g _ H2).
  - exact (pair_carries g _ H).
  - symmetry; exact (pair_carries g _ H).
  - reflexivity.
Defined.

Definition pquot_from@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  pquot_pointed X ~{Top_pointed@{h o}}~> Y :=
  @Build_PointedMap@{h o} (pquot_pointed X) Y
    (tquot_desc (pair_space X) (pquot_carrier X) (pquot_some X)
       (ptop_space Y) (pair_map g) (pquot_from_map X Y g)
       (fun x => reflexivity _))
    (reflexivity _).

Program Definition pairs_quotient_iso@{h o u | o < h, h < u +}
  (X : PairTop@{o}) (Y : PointedTop@{o}) :
  @Isomorphism Sets@{h u}
    {| carrier := @hom Top_pointed@{h o} (PairQuotient@{h o} X) Y;
       is_setoid := @homset Top_pointed@{h o} (PairQuotient@{h o} X) Y |}
    {| carrier := @hom Top_pairs@{h o} X (PointPair@{h o} Y);
       is_setoid := @homset Top_pairs@{h o} X (PointPair@{h o} Y) |} := {|
  to   := {| morphism := pquot_to@{h o} X Y |};
  from := {| morphism := pquot_from@{h o} X Y |}
|}.
Next Obligation. intros X Y p q H x; exact (H (Some x)). Qed.
Next Obligation.
  intros X Y p q H [x|]; simpl; [ exact (H x) | reflexivity ].
Qed.
Next Obligation. intros X Y g x; reflexivity. Qed.
Next Obligation.
  intros X Y p [x|]; simpl;
    [ reflexivity | symmetry; exact (ptop_preserves p) ].
Qed.

(* Construction 6: ⟨X, A⟩ ↦ X/A is left adjoint to Y ↦ ⟨Y, *⟩. *)
Definition pairs_quotient_adjunction@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o}.
Proof.
  unshelve eapply (@Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o}
                     PairQuotient@{h o} PointPair@{h o}
                     pairs_quotient_iso@{h o u}).
  - intros X Y Z f g x; reflexivity.
  - intros X Y Z f g x; reflexivity.
Defined.

(** ** Readbacks *)

Example PointPair_sub@{h o | o < h +} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y))) :
  pair_sub (fobj[PointPair@{h o}] Y) y = (y ≈ ptop_pt Y) := eq_refl.

Example pquot_space_carrier@{h o | o < h +} (X : PairTop@{o}) :
  carrier (top_carrier (ptop_space (fobj[PairQuotient@{h o}] X)))
    = option (carrier (top_carrier (pair_space X))) := eq_refl.

Example pquot_basepoint@{h o | o < h +} (X : PairTop@{o}) :
  ptop_pt (fobj[PairQuotient@{h o}] X) = None := eq_refl.

Example pquot_space_open@{o} (X : PairTop@{o})
  (V : pquot_carrier X → Type@{o}) :
  IsOpen (pquot_space X) V
    = tquot_open (pair_space X) (pquot_carrier X) (pquot_some X) V
  := eq_refl.

Example pquot_to_eval@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (p : pquot_pointed X ~{Top_pointed@{h o}}~> Y)
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (pair_map (pquot_to X Y p)) x
    = continuous_map (ptop_map p) (Some x) := eq_refl.

Example pquot_from_eval_some@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y)
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (ptop_map (pquot_from X Y g)) (Some x)
    = continuous_map (pair_map g) x := eq_refl.

Example pquot_from_eval_none@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  continuous_map (ptop_map (pquot_from X Y g)) None = ptop_pt Y := eq_refl.

Example pairs_quotient_unit_eval@{h o u v | o < h, h < u +}
  (X : PairTop@{o}) (x : carrier (top_carrier (pair_space X))) :
  continuous_map
    (pair_map (@unit _ _ _ _ pairs_quotient_adjunction@{h o u v} X)) x
    = Some x := eq_refl.

Example pairs_quotient_counit_some@{h o u v | o < h, h < u +}
  (Y : PointedTop@{o}) (y : carrier (top_carrier (ptop_space Y))) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) (Some y)
    = y := eq_refl.

Example pairs_quotient_counit_none@{h o u v | o < h, h < u +}
  (Y : PointedTop@{o}) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) None
    = ptop_pt Y := eq_refl.

Example pairs_quotient_adj_is@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @adj _ _ _ _ pairs_quotient_adjunction@{h o u v} X Y
    = pairs_quotient_iso@{h o u} X Y := eq_refl.

(** ** X/A is the pushout X ⊔_A ∗ *)

(* 相关说明。 （已译） *)
Lemma pair_sub_equiv_Equivalence@{o} (X : PairTop@{o}) :
  Equivalence (fun a b : collapse_sub_points (pair_space X) (pair_sub X) =>
                 projT1 a ≈ projT1 b).
Proof.
  constructor.
  - intro a; reflexivity.
  - intros a b H; symmetry; exact H.
  - intros a b c H1 H2; transitivity (projT1 b); assumption.
Qed.

Definition pair_sub_setoid@{o} (X : PairTop@{o}) : SetoidObject@{o o} := {|
  carrier := collapse_sub_points (pair_space X) (pair_sub X);
  is_setoid := {| equiv := fun a b => projT1 a ≈ projT1 b;
                  setoid_equiv := pair_sub_equiv_Equivalence X |}
|}.

Definition pair_sub_space@{o} (X : PairTop@{o}) : TopSpace@{o} :=
  Discrete_Top (pair_sub_setoid X).

Definition pair_sub_incl_map@{o} (X : PairTop@{o}) :
  SetoidMorphism@{o o o} (pair_sub_setoid X) (top_carrier (pair_space X)) :=
  @Build_SetoidMorphism _ (is_setoid (pair_sub_setoid X)) _
    (is_setoid (top_carrier (pair_space X))) (@projT1 _ _)
    (fun a b (e : projT1 a ≈ projT1 b) => e).

Definition pair_sub_incl@{h o | o < h +} (X : PairTop@{o}) :
  pair_sub_space X ~{Top@{h o}}~> pair_space X :=
  @Build_ContinuousMorphism@{h o} (pair_sub_space X) (pair_space X)
    (pair_sub_incl_map X)
    (out_of_discrete_continuous _ (pair_space X) (pair_sub_incl_map X)).

(* 相关说明。 （已译） *)
Definition pquot_base@{h o | o < h +} (X : PairTop@{o}) :
  Point_Top@{o} ~{Top@{h o}}~> pquot_space X :=
  top_point@{h o} (pquot_space X) None.

Section Pushout.

Universes h o.
Constraint o < h.

Context (X : PairTop@{o}) {Q : Top@{h o}}
  (q1 : pair_space X ~{Top@{h o}}~> Q) (q2 : Point_Top@{o} ~{Top@{h o}}~> Q)
  (Hq : q1 ∘ pair_sub_incl X ≈ q2 ∘ top_one (pair_sub_space X)).

Definition pquot_po_map : SetoidMorphism@{o o o} (pquot_carrier X) Q.
Proof using X Q q1 q2 Hq.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _ (is_setoid (top_carrier Q))
       (fun u => match u with
                 | Some x => continuous_map q1 x
                 | None => continuous_map q2 ttt
                 end) _).
  assert (HA : ∀ x, pair_sub X x → q1 x ≈ q2 ttt).
  { intros x Hx. exact (Hq (x; Hx)). }
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H1 H2]].
    + apply proper_morphism; exact H.
    + transitivity (q2 ttt); [ exact (HA x H1) | symmetry; exact (HA y H2) ].
  - exact (HA x H).
  - symmetry; exact (HA y H).
  - reflexivity.
Defined.

Definition pquot_po_med : pquot_space X ~{Top@{h o}}~> Q :=
  tquot_desc (pair_space X) (pquot_carrier X) (pquot_some X) Q q1
    pquot_po_map (fun x => reflexivity _).

End Pushout.

Definition pquot_pushout@{h o | o < h +} (X : PairTop@{o}) :
  IsPushout (C := Top@{h o}) (pair_sub_incl X) (top_one (pair_sub_space X)).
Proof.
  unshelve refine (@Build_Pullback (Top@{h o}^op) _ _ _
                     (pair_sub_incl X) (top_one (pair_sub_space X))
                     (pquot_space X) (pquot_in X) (pquot_base X) _ _).
  - intro a; simpl. exact (projT2 a).
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + exact (pquot_po_med X q1 q2 Hq).
    + split.
      * intro x; simpl. reflexivity.
      * intro t; simpl. destruct t. reflexivity.
    + intros v [Hv1 Hv2] [x|]; simpl.
      * symmetry; exact (Hv1 x).
      * symmetry; exact (Hv2 ttt).
Defined.

Example pquot_pushout_apex@{h o | o < h +} (X : PairTop@{o}) :
  pushout_apex (pquot_pushout@{h o} X) = pquot_space X := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pquot_wide_legs@{o h | o < h +} (X : PairTop@{o}) (p : ParObj) :
  fobj[AWide@{h h h h h} (C := Top@{h o})
         (collapse_sub_family (pair_space X) (pair_sub X))] p
    ~{Top@{h o}}~> pquot_space X :=
  match p return
    fobj[AWide@{h h h h h} (C := Top@{h o})
           (collapse_sub_family (pair_space X) (pair_sub X))] p
      ~{Top@{h o}}~> pquot_space X with
  | ParX => pquot_base X
  | ParY => pquot_in X
  end.

Lemma pquot_wide_legs_coherence@{o h | o < h +} (X : PairTop@{o}) :
  ∀ (a b : ParObj)
    (k : b ~{WideParallel@{h h}
               (collapse_sub_points (pair_space X) (pair_sub X))}~> a),
    pquot_wide_legs X a
      ∘ fmap[AWide@{h h h h h} (C := Top@{h o})
               (collapse_sub_family (pair_space X) (pair_sub X))] k
    ≈ pquot_wide_legs X b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - intro t; simpl. exact ttt.
  - destruct k.
  - intro t; simpl. exact (projT2 k).
  - intro t; simpl. left; reflexivity.
Qed.

Definition pquot_wide_cocone@{o h | o < h +} (X : PairTop@{o}) :
  Cocone (AWide@{h h h h h} (C := Top@{h o})
            (collapse_sub_family (pair_space X) (pair_sub X))) :=
  @Build_Cone
    ((WideParallel@{h h}
        (collapse_sub_points (pair_space X) (pair_sub X)))^op)
    (Top@{h o}^op)
    ((AWide@{h h h h h} (C := Top@{h o})
        (collapse_sub_family (pair_space X) (pair_sub X)))^op)
    (pquot_space X)
    (@Build_ACone
       ((WideParallel@{h h}
           (collapse_sub_points (pair_space X) (pair_sub X)))^op)
       (Top@{h o}^op) (pquot_space X)
       ((AWide@{h h h h h} (C := Top@{h o})
           (collapse_sub_family (pair_space X) (pair_sub X)))^op)
       (pquot_wide_legs X) (pquot_wide_legs_coherence X)).

(* 相关说明。 （已译） *)
Lemma pquot_wide_ump@{o h | o < h +} (X : PairTop@{o})
  (N : Cocone (AWide@{h h h h h} (C := Top@{h o})
                 (collapse_sub_family (pair_space X) (pair_sub X)))) :
  ∃! u : pquot_space X ~{Top@{h o}}~> vertex_obj[N],
    ∀ p : ParObj, u ∘ pquot_wide_legs X p ≈ cocone_inj N p.
Proof.
  assert (Hq : cocone_inj N ParY ∘ pair_sub_incl X
               ≈ cocone_inj N ParX ∘ top_one (pair_sub_space X)).
  { intro a.
    exact (cocone_inj_coherence N (a : ParX ~{WideParallel _}~> ParY) ttt). }
  unshelve eapply Build_Unique.
  - exact (pquot_po_med X (cocone_inj N ParY) (cocone_inj N ParX) Hq).
  - intros p; destruct p; intro t; simpl.
    + destruct t; reflexivity.
    + reflexivity.
  - intros v Hv [x|]; simpl.
    + symmetry; exact (Hv ParY x).
    + symmetry; exact (Hv ParX ttt).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pquot_wide_coequalizer_colimit@{o h | o < h +}
  (X : PairTop@{o}) :
  WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  {| limit_cone := pquot_wide_cocone X;
     ump_limits := fun N => pquot_wide_ump X N |}.

Example pquot_wide_coequalizer_colimit_apex@{o h | o < h +}
  (X : PairTop@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) = pquot_space X
  := eq_refl.

Example pquot_wide_coequalizer_colimit_in@{o h | o < h +}
  (X : PairTop@{o}) :
  colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
    ParY = pquot_in X := eq_refl.

(* The leg out * picks 左伴随's basepoint. （已译） *)
Example pquot_wide_coequalizer_colimit_base@{o h | o < h +}
  (X : PairTop@{o}) :
  continuous_map
    (colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
       ParX) ttt
    = ptop_pt (fobj[PairQuotient@{h o}] X) := eq_refl.

(* The 左伴随's value at every pair IS colimit's apex. （已译） *)
Example pquot_wide_coequalizer_colimit_quotient@{o h | o < h +}
  (X : PairTop@{o}) :
  ptop_space (fobj[PairQuotient@{h o}] X)
    = colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) := eq_refl.

(* 相关说明。 （已译） *)
Definition collapse_colimit_point@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o})
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family X A))) :
  top_carrier (colimit_apex L) :=
  continuous_map (colimit_inj (colimit_is_acolimit L) ParX) ttt.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition pquot_coequalizer@{o h i | o < h, o <= i +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space X) (pair_sub X))
    (pquot_space X) (pquot_in X).
Proof.
  unshelve econstructor.
  - intros [a Ha] [b Hb] t; simpl; right; exact (Ha, Hb).
  - intros Z k Hk.
    unshelve eapply Build_Unique.
    + refine (pquot_po_med X k (k ∘ top_point (pair_space X) (projT1 a0)) _).
      intro a; simpl. exact (Hk a a0 ttt).
    + intro x; reflexivity.
    + intros v Hv [x|]; simpl.
      * symmetry; exact (Hv x).
      * transitivity (continuous_map v (Some (projT1 a0))).
        -- symmetry; exact (Hv (projT1 a0)).
        -- apply (proper_morphism (continuous_map v) (Some (projT1 a0)) None).
           exact (projT2 a0).
Defined.

(* The two readings X/A isomorphic [Top], 恒等 the
 points X. （已译） *)
Definition pquot_collapse_iso@{o h u | o < h, h < u +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Example pquot_collapse_iso_to@{o h u | o < h, h < u +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (to (pquot_collapse_iso X a0)) x = Some x := eq_refl.

Example pquot_collapse_iso_from_some@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (from (pquot_collapse_iso X a0)) (Some x) = x := eq_refl.

Example pquot_collapse_iso_from_none@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  continuous_map (from (pquot_collapse_iso X a0)) None = projT1 a0
  := eq_refl.

(* Construction 5's X/A, pointed at the point [a0] of A. *)
Definition collapse_pointed@{o} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) : PointedTop@{o} :=
  @Build_PointedTop@{o} (Top_collapse_sub (pair_space X) (pair_sub X))
    (projT1 a0).

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pquot_collapse_iso_pointed@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  collapse_pointed X a0 ≅[Top_pointed@{h o}] fobj[PairQuotient@{h o}] X :=
  @Build_Isomorphism Top_pointed@{h o} (collapse_pointed X a0)
    (fobj[PairQuotient@{h o}] X)
    (@Build_PointedMap@{h o} (collapse_pointed X a0)
       (fobj[PairQuotient@{h o}] X) (to (pquot_collapse_iso@{o h u} X a0))
       (projT2 a0))
    (@Build_PointedMap@{h o} (fobj[PairQuotient@{h o}] X)
       (collapse_pointed X a0) (from (pquot_collapse_iso@{o h u} X a0))
       (inl (reflexivity (projT1 a0))))
    (iso_to_from (pquot_collapse_iso@{o h u} X a0))
    (iso_from_to (pquot_collapse_iso@{o h u} X a0)).

(* 相关说明。 （已译） *)

Definition empty_pair@{o} (X : TopSpace@{o}) : PairTop@{o} :=
  @Build_PairTop@{o} X (fun _ => False) (fun _ _ _ f => f).

(* The collapse at ∅ has a genuinely new point ... *)
Lemma pquot_empty_new_point@{o} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  pquot_rel (empty_pair X) (Some x) None → False.
Proof. exact (fun f => f). Qed.

(* 相关说明。 （已译） *)
Definition pquot_empty_sum_to@{o} (X : TopSpace@{o}) :
  SetoidMorphism@{o o o} (pquot_carrier (empty_pair X))
    (sum_carrier X Point_Top@{o}).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid (empty_pair X)) _
       (is_setoid (sum_carrier X Point_Top@{o}))
       (fun u => match u with
                 | Some x => Datatypes.inl x
                 | None => Datatypes.inr ttt
                 end) _).
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H _]]; [ exact H | destruct H ].
  - destruct H.
  - destruct H.
  - reflexivity.
Defined.

Definition pquot_empty_sum_from@{o} (X : TopSpace@{o}) :
  SetoidMorphism@{o o o} (sum_carrier X Point_Top@{o})
    (pquot_carrier (empty_pair X)).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (is_setoid (sum_carrier X Point_Top@{o})) _
       (pquot_setoid (empty_pair X))
       (fun w => match w with
                 | Datatypes.inl x => Some x
                 | Datatypes.inr _ => None
                 end) _).
  intros [x|a] [y|b] H; simpl in *.
  - left; exact H.
  - destruct H.
  - destruct H.
  - exact ttt.
Defined.

Definition pquot_empty_sum_iso@{h o | o < h +} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) ≅[Top@{h o}] Sum_Top X Point_Top@{o}.
Proof.
  unshelve refine (@Build_Isomorphism Top@{h o}
            (pquot_space (empty_pair X)) (Sum_Top X Point_Top@{o})
            (@Build_ContinuousMorphism@{h o} (pquot_space (empty_pair X))
               (Sum_Top X Point_Top@{o}) (pquot_empty_sum_to X) _)
            (@Build_ContinuousMorphism@{h o} (Sum_Top X Point_Top@{o})
               (pquot_space (empty_pair X)) (pquot_empty_sum_from X) _)
            _ _).
  - apply (snd (tquot_universal (pair_space (empty_pair X))
                  (pquot_carrier (empty_pair X)) (pquot_some (empty_pair X))
                  (Sum_Top X Point_Top@{o}) (pquot_empty_sum_to X))).
    exact (continuity (Top_inl X Point_Top@{o})).
  - intros V [_ HV]; split.
    + exact HV.
    + exact (open_const Point_Top@{o} (V None)).
  - intros [x|a]; simpl.
    + reflexivity.
    + destruct a; reflexivity.
  - intros [x|]; simpl.
    + left; reflexivity.
    + exact ttt.
Defined.

Example pquot_empty_sum_iso_some@{h o | o < h +} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) (Some x) = Datatypes.inl x
  := eq_refl.

Example pquot_empty_sum_iso_none@{h o | o < h +} (X : TopSpace@{o}) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) None = Datatypes.inr ttt
  := eq_refl.

(* So, read 泛箭头, coequalizer empty family of
 point-inclusions, colimit above at ⟨X, ∅⟩, X ⊔ ∗. （已译） *)
Definition pquot_wide_coequalizer_colimit_empty@{o h | o < h +}
  (X : TopSpace@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} (empty_pair X))
    ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_empty_sum_iso@{h o} X.

(* 相关说明。 （已译） *)
Lemma pquot_empty_not_coequalizer@{o h i | o < h, o <= i +} :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space (empty_pair Empty_Top@{o}))
       (pair_sub (empty_pair Empty_Top@{o})))
    (pquot_space (empty_pair Empty_Top@{o}))
    (pquot_in (empty_pair Empty_Top@{o})) → False.
Proof.
  intro E.
  destruct (wcoeq_desc E (@id Top@{h o} Empty_Top@{o})
              (fun i => match projT2 i with end)) as [u _ _].
  exact (continuous_map u None).
Qed.

(* ... so [pquot_coequalizer]'s point of A cannot be dropped. *)
Lemma pquot_coequalizer_needs_point@{o h i | o < h, o <= i +} :
  (∀ X : PairTop@{o},
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X))
       (pquot_space X) (pquot_in X)) → False.
Proof.
  intro H.
  exact (pquot_empty_not_coequalizer@{o h i} (H (empty_pair Empty_Top@{o}))).
Qed.

(* 相关说明。 （已译） *)

(* No pointed space's underlying space is an elementary wide coequalizer
   of the empty family of point-inclusions at the empty space: its
   basepoint would be a point of it, which Instance/Top/Quotient.v's
   [empty_wide_coequalizer_pointless] refutes.（标题）（已译） *)
Lemma no_pointed_coequalizer_at_empty@{o h i | o < h, o <= i +}
  (Q : PointedTop@{o}) (e : Empty_Top@{o} ~{Top@{h o}}~> ptop_space Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (ptop_space Q) e →
  False.
Proof.
  intro E.
  exact (empty_wide_coequalizer_pointless@{o h i} (ptop_space Q) e E
           (ptop_pt Q)).
Qed.

(* Hence no assignment pointed space each pair, 函子 any
 other function 对象, makes every underlying space elementary
 wide coequalizer point-inclusions: at ⟨∅, ∅⟩ there is none. The
 余极限 form is met [PairQuotient] at every pair
 ([pquot_wide_coequalizer_colimit_quotient]).（已译） *)
Lemma no_pointed_elementary_coequalizers@{o h i | o < h, o <= i +}
  (L : PairTop@{o} → PointedTop@{o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False.
Proof.
  intro H.
  destruct (H (empty_pair Empty_Top@{o})) as [e E].
  exact (no_pointed_coequalizer_at_empty@{o h i} _ e E).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma empty_colimit_not_elementary@{o h i | o < h, o <= i +}
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family Empty_Top@{o}
                             (fun _ => False))))
  (e : Empty_Top@{o} ~{Top@{h o}}~> colimit_apex L) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (colimit_apex L) e →
  False.
Proof.
  intro E.
  exact (empty_wide_coequalizer_pointless@{o h i} (colimit_apex L) e E
           (collapse_colimit_point Empty_Top@{o} (fun _ => False) L)).
Qed.
