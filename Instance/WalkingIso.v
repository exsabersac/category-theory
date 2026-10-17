Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.

Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance edgeset.

(*
   nLab: https://ncatlab.org/nlab/show/walking+isomorphism
   nLab: https://ncatlab.org/nlab/show/free+category
   Book: Awodey, Category Theory, 1st ed., §4.4 Example 4.9, printed

   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Inductive WIsoNode : Set := WI_A | WI_B.

Inductive WIsoEdge : WIsoNode -> WIsoNode -> Set :=
  | WI_f : WIsoEdge WI_A WI_B
  | WI_g : WIsoEdge WI_B WI_A.

Definition WIsoQuiver : Quiver :=
  Build_Quiver_Standard_Eq WIsoNode WIsoEdge.

(** The free 范畴 it: paths alternating words f g. （已译） *)
Definition FreeWIso : Category := FreeOnQuiver WIsoQuiver.

(** The two generating edges, as one-step paths. *)
Definition wi_f : WI_A ~{FreeWIso}~> WI_B :=
  tlist_singleton (B:=@edges WIsoQuiver) WI_f.
Definition wi_g : WI_B ~{FreeWIso}~> WI_A :=
  tlist_singleton (B:=@edges WIsoQuiver) WI_g.

(*
   本节说明 WalkingIso 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint wi_AA (n : nat) : WI_A ~{FreeWIso}~> WI_A :=
  match n with
  | O => tnil
  | S m => tcons (B:=@edges WIsoQuiver) _ WI_f
             (tcons (B:=@edges WIsoQuiver) _ WI_g (wi_AA m))
  end.

Fixpoint wi_BB (n : nat) : WI_B ~{FreeWIso}~> WI_B :=
  match n with
  | O => tnil
  | S m => tcons (B:=@edges WIsoQuiver) _ WI_g
             (tcons (B:=@edges WIsoQuiver) _ WI_f (wi_BB m))
  end.

Definition wi_AB (n : nat) : WI_A ~{FreeWIso}~> WI_B :=
  tcons (B:=@edges WIsoQuiver) _ WI_f (wi_BB n).
Definition wi_BA (n : nat) : WI_B ~{FreeWIso}~> WI_A :=
  tcons (B:=@edges WIsoQuiver) _ WI_g (wi_AA n).

(** 本节：The empty path length-zero loop, each generator the
 length-one path own family. （已译） *)
Example wi_AA_0 : wi_AA 0 = @id FreeWIso WI_A := eq_refl.
Example wi_BB_0 : wi_BB 0 = @id FreeWIso WI_B := eq_refl.
Example wi_AB_0 : wi_AB 0 = wi_f := eq_refl.
Example wi_BA_0 : wi_BA 0 = wi_g := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wi_spec (y : WIsoNode) :
  forall x : WIsoNode, (x ~{FreeWIso}~> y) -> Type :=
  match y as y0 return forall x : WIsoNode, (x ~{FreeWIso}~> y0) -> Type
  with
  | WI_A => fun x => match x as x0
                      return (x0 ~{FreeWIso}~> WI_A) -> Type with
      | WI_A => fun p => { n : nat & p = wi_AA n }
      | WI_B => fun p => { n : nat & p = wi_BA n }
      end
  | WI_B => fun x => match x as x0
                      return (x0 ~{FreeWIso}~> WI_B) -> Type with
      | WI_A => fun p => { n : nat & p = wi_AB n }
      | WI_B => fun p => { n : nat & p = wi_BB n }
      end
  end.

(*
   本节说明 WalkingIso 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem wi_classify (y x : WIsoNode) (p : x ~{FreeWIso}~> y) :
  wi_spec y x p.
Proof.
  induction p as [ | i j e p IH ].
  - destruct y; exists 0%nat; reflexivity.
  - destruct e; destruct y; simpl in *;
      destruct IH as [n Hn]; subst.
    + exists (S n); reflexivity.
    + exists n; reflexivity.
    + exists n; reflexivity.
    + exists (S n); reflexivity.
Qed.

(* 相关说明。 （已译） *)

Definition WIsoEqn_count (x y : WIsoQuiver) : nat :=
  match x, y with
  | WI_A, WI_A => 1 | WI_B, WI_B => 1 | _, _ => 0
  end.

Definition WIsoEqn_lhs (x y : WIsoQuiver) :
  Fin.t (WIsoEqn_count x y) -> x ~{FreeWIso}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact (wi_AA 1) | exact (wi_BB 1) ].
Defined.

Definition WIsoEqn_rhs (x y : WIsoQuiver) :
  Fin.t (WIsoEqn_count x y) -> x ~{FreeWIso}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact (wi_AA 0) | exact (wi_BB 0) ].
Defined.

Definition WIsoEqns : FiniteEquations WIsoQuiver := {|
  fe_count := WIsoEqn_count;
  fe_lhs   := WIsoEqn_lhs;
  fe_rhs   := WIsoEqn_rhs
|}.

Definition WIso_node (i : Fin.t 2) : WIsoNode :=
  match i with Fin.F1 => WI_A | Fin.FS _ => WI_B end.

Definition WIso_index (x : WIsoNode) : Fin.t 2 :=
  match x with WI_A => Fin.F1 | WI_B => Fin.FS Fin.F1 end.

Lemma WIso_node_rt (x : WIsoNode) : WIso_node (WIso_index x) = x.
Proof. destruct x; reflexivity. Qed.

Definition WIso_ecount (x y : WIsoNode) : nat :=
  match x, y with
  | WI_A, WI_B => 1 | WI_B, WI_A => 1 | _, _ => 0
  end.

Definition WIso_edge (x y : WIsoNode) :
  Fin.t (WIso_ecount x y) -> WIsoEdge x y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact WI_f | exact WI_g ].
Defined.

Definition WIso_eindex (x y : WIsoNode) (e : WIsoEdge x y) :
  Fin.t (WIso_ecount x y) :=
  match e in WIsoEdge a b return Fin.t (WIso_ecount a b) with
  | WI_f => Fin.F1
  | WI_g => Fin.F1
  end.

Lemma WIso_edge_rt (x y : WIsoNode) (e : WIsoEdge x y) :
  WIso_edge x y (WIso_eindex x y e) = e.
Proof. destruct e; reflexivity. Qed.

Definition WIsoFinite : FiniteQuiver WIsoQuiver :=
  @Build_FiniteQuiver WIsoQuiver 2 WIso_node WIso_index WIso_node_rt
    WIso_ecount WIso_edge WIso_eindex WIso_edge_rt.

Definition WalkingIsoPresentation : FinitePresentation := {|
  fp_quiver := WIsoQuiver;
  fp_finite := WIsoFinite;
  fp_eqns   := WIsoEqns
|}.

(** The walking isomorphism. *)
Definition WalkingIso : Category :=
  FinitelyPresented WalkingIsoPresentation.

(** ...which presented 范畴 quiver 关系,
 definitionally. （已译） *)
Example WalkingIso_is_presented :
  WalkingIso = PresentedQuiver WIsoQuiver (fe_rel WIsoEqns) := eq_refl.

(** 本节：The hom TYPES [WalkingIso] free ones: equations merge,
 never add. This what makes trap header
 possible. （已译） *)
Example WalkingIso_hom_is_free (x y : WIsoNode) :
  (x ~{WalkingIso}~> y) = (x ~{FreeWIso}~> y) := eq_refl.

(** Composition free 范畴's, nose. （已译） *)
Example WalkingIso_compose_is_free {x y z : WIsoNode}
  (p : y ~{FreeWIso}~> z) (q : x ~{FreeWIso}~> y) :
  @compose WalkingIso x y z p q = @compose FreeWIso x y z p q := eq_refl.

(* 相关说明。 （已译） *)

Definition iso_f : WI_A ~{WalkingIso}~> WI_B :=
  @pgen WIsoQuiver (fe_rel WIsoEqns) _ _ WI_f.
Definition iso_g : WI_B ~{WalkingIso}~> WI_A :=
  @pgen WIsoQuiver (fe_rel WIsoEqns) _ _ WI_g.

(*
   本节说明 WalkingIso 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_gf_is_loop :
  @compose FreeWIso _ _ _ wi_g wi_f = wi_AA 1 := eq_refl.
Example free_fg_is_loop :
  @compose FreeWIso _ _ _ wi_f wi_g = wi_BB 1 := eq_refl.

(*
   本节说明 WalkingIso 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wiso_gf :
  @equiv _ (@homset WalkingIso WI_A WI_A)
    (@compose WalkingIso _ _ _ iso_g iso_f) (@id WalkingIso WI_A).
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

Lemma wiso_fg :
  @equiv _ (@homset WalkingIso WI_B WI_B)
    (@compose WalkingIso _ _ _ iso_f iso_g) (@id WalkingIso WI_B).
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition walking_iso : @Isomorphism WalkingIso WI_A WI_B := {|
  to          := iso_f;
  from        := iso_g;
  iso_to_from := wiso_fg;
  iso_from_to := wiso_gf
|}.

Example walking_iso_to : to walking_iso = iso_f := eq_refl.
Example walking_iso_from : from walking_iso = iso_g := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** 本节：Consing edge onto path IS composing corresponding
 generator, at Leibniz equality — [Lib/TList.v]'s [tlist_app_cons]
 read at quiver. （已译） *)
Lemma wi_cons_f {y : WIsoNode} (t : WI_B ~{FreeWIso}~> y) :
  tcons (B:=@edges WIsoQuiver) _ WI_f t = @compose FreeWIso _ _ _ t wi_f.
Proof. exact (tlist_app_cons WI_f t). Qed.

Lemma wi_cons_g {y : WIsoNode} (t : WI_A ~{FreeWIso}~> y) :
  tcons (B:=@edges WIsoQuiver) _ WI_g t = @compose FreeWIso _ _ _ t wi_g.
Proof. exact (tlist_app_cons WI_g t). Qed.

(** 本节：Hence each loop predecessor followed round trip.
 Supplied term rather than tactics: [simpl] unfolds the
 generators past pattern rewrite looking for. （已译） *)
Definition wi_AA_step (n : nat) :
  wi_AA (S n) = @compose FreeWIso _ _ _
                  (@compose FreeWIso _ _ _ (wi_AA n) wi_g) wi_f :=
  eq_trans (wi_cons_f (tcons (B:=@edges WIsoQuiver) _ WI_g (wi_AA n)))
           (f_equal (fun t => @compose FreeWIso _ _ _ t wi_f)
                    (wi_cons_g (wi_AA n))).

Definition wi_BB_step (n : nat) :
  wi_BB (S n) = @compose FreeWIso _ _ _
                  (@compose FreeWIso _ _ _ (wi_BB n) wi_f) wi_g :=
  eq_trans (wi_cons_g (tcons (B:=@edges WIsoQuiver) _ WI_f (wi_BB n)))
           (f_equal (fun t => @compose FreeWIso _ _ _ t wi_g)
                    (wi_cons_f (wi_BB n))).

(** Every loop at A collapses 恒等. The appeal to
 associativity names [WalkingIso] explicitly; see header. （已译） *)
Lemma wi_AA_collapse (n : nat) :
  @equiv _ (@homset WalkingIso WI_A WI_A) (wi_AA n) (@id WalkingIso WI_A).
Proof.
  induction n as [ | n IH ]; [ reflexivity | ].
  rewrite wi_AA_step.
  rewrite <- (@comp_assoc WalkingIso _ _ _ _ (wi_AA n) wi_g wi_f).
  rewrite wiso_gf, id_right.
  exact IH.
Qed.

Lemma wi_BB_collapse (n : nat) :
  @equiv _ (@homset WalkingIso WI_B WI_B) (wi_BB n) (@id WalkingIso WI_B).
Proof.
  induction n as [ | n IH ]; [ reflexivity | ].
  rewrite wi_BB_step.
  rewrite <- (@comp_assoc WalkingIso _ _ _ _ (wi_BB n) wi_f wi_g).
  rewrite wiso_fg, id_right.
  exact IH.
Qed.

Lemma wi_AB_collapse (n : nat) :
  @equiv _ (@homset WalkingIso WI_A WI_B) (wi_AB n) iso_f.
Proof.
  unfold wi_AB; rewrite (wi_cons_f (wi_BB n)).
  change (@compose FreeWIso ?x ?y ?z ?a ?b)
    with (@compose WalkingIso x y z a b).
  rewrite wi_BB_collapse; apply id_left.
Qed.

Lemma wi_BA_collapse (n : nat) :
  @equiv _ (@homset WalkingIso WI_B WI_A) (wi_BA n) iso_g.
Proof.
  unfold wi_BA; rewrite (wi_cons_g (wi_AA n)).
  change (@compose FreeWIso ?x ?y ?z ?a ?b)
    with (@compose WalkingIso x y z a b).
  rewrite wi_AA_collapse; apply id_left.
Qed.

(* 相关说明。 （已译） *)

(** 本节：Any two parallel arrows agree. Each four cases classifies
 both arrows collapses each same normal form. （已译） *)
Theorem WalkingIso_Thin : Thin WalkingIso.
Proof.
  intros x y p q; destruct x, y;
    destruct (wi_classify _ _ p) as [m Hm];
    destruct (wi_classify _ _ q) as [n Hn]; subst.
  - transitivity (@id WalkingIso WI_A);
      [ apply wi_AA_collapse | symmetry; apply wi_AA_collapse ].
  - transitivity iso_f;
      [ apply wi_AB_collapse | symmetry; apply wi_AB_collapse ].
  - transitivity iso_g;
      [ apply wi_BA_collapse | symmetry; apply wi_BA_collapse ].
  - transitivity (@id WalkingIso WI_B);
      [ apply wi_BB_collapse | symmetry; apply wi_BB_collapse ].
Qed.

(** A chosen inhabitant of each of the four hom-sets. *)
Definition wiso_arrow (x y : WIsoNode) : x ~{WalkingIso}~> y :=
  match x, y with
  | WI_A, WI_A => id
  | WI_A, WI_B => iso_f
  | WI_B, WI_A => iso_g
  | WI_B, WI_B => id
  end.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem wiso_hom_singleton (x y : WIsoNode) :
  ((x ~{WalkingIso}~> y) *
   (forall p q : x ~{WalkingIso}~> y, p ≈ q))%type.
Proof. exact (wiso_arrow x y, WalkingIso_Thin x y). Qed.

(** Every endomorphism 恒等: there no nontrivial loops
 downstairs, though there infinitely many upstairs. （已译） *)
Corollary wiso_endo_id {x : WalkingIso} (p : x ~> x) : p ≈ id.
Proof. exact (WalkingIso_Thin x x p id). Qed.

(*
   本节说明hom、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem WalkingIso_IsGroupoid : IsGroupoid WalkingIso.
Proof.
  intros x y f.
  unshelve eapply Build_IsIsomorphism.
  - exact (wiso_arrow y x).
  - apply WalkingIso_Thin.
  - apply WalkingIso_Thin.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Equivalent paths free 范畴 have equal length —
 [tlist'_equiv_lengths] ([Construction/Free/Quiver.v]) at this
 quiver. （已译） *)
Lemma wi_equiv_length {x y : WIsoNode} (p q : x ~{FreeWIso}~> y) :
  p ≈ q -> tlist_length p = tlist_length q.
Proof. intro H; exact (tlist'_equiv_lengths _ _ _ _ _ _ _ H). Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_iso_lengths {Q : Quiver} {x y : Q}
  (f : x ~{FreeOnQuiver Q}~> y) (g : y ~{FreeOnQuiver Q}~> x)
  (H : @equiv _ (@homset (FreeOnQuiver Q) x x)
         (@compose (FreeOnQuiver Q) x y x g f) (@id (FreeOnQuiver Q) x)) :
  (tlist_length f = 0)%nat /\ (tlist_length g = 0)%nat.
Proof.
  pose proof (tlist'_equiv_lengths _ _ _ _ _ _ _ H) as HL.
  change (@compose (FreeOnQuiver Q) x y x g f) with (f +++ g) in HL.
  rewrite tlist_app_length in HL. simpl in HL. split; lia.
Qed.

Lemma wi_AA_length (n : nat) : tlist_length (wi_AA n) = (n + n)%nat.
Proof.
  induction n as [ | n IH ]; [ reflexivity | ].
  simpl; rewrite PeanoNat.Nat.add_succ_r; do 2 f_equal; exact IH.
Qed.

Lemma wi_BB_length (n : nat) : tlist_length (wi_BB n) = (n + n)%nat.
Proof.
  induction n as [ | n IH ]; [ reflexivity | ].
  simpl; rewrite PeanoNat.Nat.add_succ_r; do 2 f_equal; exact IH.
Qed.

Lemma wi_double_inj (m n : nat) : (m + m)%nat = (n + n)%nat -> m = n.
Proof.
  revert n; induction m as [ | m IH ]; intros [ | n ] H; simpl in H;
    try discriminate; try reflexivity.
  f_equal; apply IH.
  injection H as H.
  rewrite !PeanoNat.Nat.add_succ_r in H.
  now injection H.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_wi_AA_inj (m n : nat) :
  @equiv _ (@homset FreeWIso WI_A WI_A) (wi_AA m) (wi_AA n) -> m = n.
Proof.
  intro H.
  apply wi_double_inj.
  rewrite <- (wi_AA_length m), <- (wi_AA_length n).
  exact (wi_equiv_length _ _ H).
Qed.

Corollary free_wi_AA_distinct (m n : nat) (Hmn : m <> n) :
  @equiv _ (@homset FreeWIso WI_A WI_A) (wi_AA m) (wi_AA n) -> False.
Proof. intro H; exact (Hmn (free_wi_AA_inj m n H)). Qed.

(** The presenting projection. It 恒等 对象 on
 态射; hom-setoid coarsens. （已译） *)
Definition WalkingIsoProj : FreeWIso ⟶ WalkingIso :=
  @PresentedQuiverProj WIsoQuiver (fe_rel WIsoEqns).

Example WalkingIsoProj_hom {x y : WIsoNode} (p : x ~{FreeWIso}~> y) :
  fmap[WalkingIsoProj] p = p := eq_refl.

(** 本节：The two sides contrast at one concrete pair: round trip
 (gf) empty path distinct arrows [FreeWIso] the
 same arrow [WalkingIso]. （已译） *)
Theorem walking_iso_merges_the_loops :
  ((@equiv _ (@homset FreeWIso WI_A WI_A) (wi_AA 1) (wi_AA 0) -> False) *
   (@equiv _ (@homset WalkingIso WI_A WI_A) (wi_AA 1) (wi_AA 0)))%type.
Proof.
  split.
  - apply free_wi_AA_distinct; discriminate.
  - exact (wi_AA_collapse 1).
Qed.

(*
   本节说明hom、（余）强度、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem WalkingIsoProj_not_faithful : Faithful WalkingIsoProj -> False.
Proof.
  intro HF.
  apply (free_wi_AA_distinct 1 0); [ discriminate | ].
  apply (@fmap_inj _ _ _ HF WI_A WI_A (wi_AA 1) (wi_AA 0)).
  exact (wi_AA_collapse 1).
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition wi_nodes : list WIsoNode := WI_A :: WI_B :: nil.

Lemma wi_nodes_complete (x : WIsoNode) : In x wi_nodes.
Proof. destruct x; simpl; auto. Qed.

Lemma wi_nodes_nodup : NoDup wi_nodes.
Proof. repeat constructor; simpl; intuition congruence. Qed.

(** Two objects. *)
Theorem wiso_object_total : length wi_nodes = 2%nat.
Proof. reflexivity. Qed.

Definition wi_all_pairs : list (WIsoNode * WIsoNode) :=
  list_prod wi_nodes wi_nodes.

Example wi_all_pairs_4 : length wi_all_pairs = 4%nat := eq_refl.

Lemma wi_all_pairs_complete (x y : WIsoNode) : In (x, y) wi_all_pairs.
Proof. apply in_prod; apply wi_nodes_complete. Qed.

(** Every hom-set has exactly one arrow — 常值 what
 [wiso_hom_singleton] licenses, nothing else section
 depends pair being counted. （已译） *)
Definition wiso_homcount (x y : WIsoNode) : nat := 1%nat.

Definition wiso_arrow_total : nat :=
  fold_right (fun q n => wiso_homcount (fst q) (snd q) + n)%nat 0%nat
    wi_all_pairs.

(** Four arrows. *)
Theorem wiso_arrow_total_4 : wiso_arrow_total = 4%nat.
Proof. reflexivity. Qed.

Definition wiso_identity_total : nat :=
  fold_right (fun x n => wiso_homcount x x + n)%nat 0%nat wi_nodes.

(** ...two of them identities. *)
Theorem wiso_identity_total_2 : wiso_identity_total = 2%nat.
Proof. reflexivity. Qed.

Definition wiso_nonidentity_total : nat :=
  (wiso_arrow_total - wiso_identity_total)%nat.

(** 本节：...and two them not: [iso_f] [iso_g]. （已译） *)
Theorem wiso_nonidentity_total_2 : wiso_nonidentity_total = 2%nat.
Proof. reflexivity. Qed.

(** The two non-恒等 arrows not identities, because their
 endpoints differ. （已译） *)
Lemma wiso_nonidentity_endpoints : WI_A <> WI_B.
Proof. discriminate. Qed.

(*
   本节说明 WalkingIso 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wiso_generator_total : nat :=
  fold_right
    (fun q n => fq_edges WIsoQuiver WIsoFinite (fst q) (snd q) + n)%nat
    0%nat wi_all_pairs.

Theorem wiso_generator_total_2 : wiso_generator_total = 2%nat.
Proof. reflexivity. Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IndexShape.

Context {C : Category}.

Definition wiso_node {a b : C} (i : a ≅ b) (n : WIsoNode) : C :=
  match n with WI_A => a | WI_B => b end.

Definition wiso_edgemap {a b : C} (i : a ≅ b) (x y : WIsoNode)
  (e : WIsoEdge x y) : wiso_node i x ~> wiso_node i y :=
  match e in WIsoEdge u v return wiso_node i u ~> wiso_node i v with
  | WI_f => to i
  | WI_g => from i
  end.

Definition wiso_quiver_hom {a b : C} (i : a ≅ b) :
  QuiverHomomorphism WIsoQuiver (QuiverOfCat C).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (wiso_node i).
  - exact (wiso_edgemap i).
  - intros x y u v Huv; simpl in Huv; subst; reflexivity.
Defined.

(** The two imposed relations merged: they exactly two
 inverse laws, modulo trailing 恒等 [tlist] fold leaves
 behind. （已译） *)
Lemma wiso_quiver_hom_merges {a b : C} (i : a ≅ b) :
  forall x y (p q : x ~{FreeWIso}~> y), fe_rel WIsoEqns x y p q ->
    fmap[@InducedFunctor WIsoQuiver C (wiso_quiver_hom i)] p
      ≈ fmap[@InducedFunctor WIsoQuiver C (wiso_quiver_hom i)] q.
Proof.
  intros x y p q [k [Hp Hq]].
  destruct x, y; simpl in k; try solve [ exact (Fin.case0 _ k) ];
    simpl in Hp, Hq; rewrite Hp, Hq; simpl; rewrite !id_left.
  - exact (iso_from_to i).
  - exact (iso_to_from i).
Qed.

(** The functor an isomorphism names. *)
Definition WalkingIsoFunctor {a b : C} (i : a ≅ b) : WalkingIso ⟶ C :=
  @PresentedFunctor WIsoQuiver (fe_rel WIsoEqns) C
    (wiso_quiver_hom i) (wiso_quiver_hom_merges i).

Example WalkingIsoFunctor_A {a b : C} (i : a ≅ b) :
  fobj[WalkingIsoFunctor i] WI_A = a := eq_refl.
Example WalkingIsoFunctor_B {a b : C} (i : a ≅ b) :
  fobj[WalkingIsoFunctor i] WI_B = b := eq_refl.

Lemma WalkingIsoFunctor_f {a b : C} (i : a ≅ b) :
  fmap[WalkingIsoFunctor i] iso_f ≈ to i.
Proof.
  exact (@PresentedFunctor_gen WIsoQuiver (fe_rel WIsoEqns) C
           (wiso_quiver_hom i) (wiso_quiver_hom_merges i) _ _ WI_f).
Qed.

Lemma WalkingIsoFunctor_g {a b : C} (i : a ≅ b) :
  fmap[WalkingIsoFunctor i] iso_g ≈ from i.
Proof.
  exact (@PresentedFunctor_gen WIsoQuiver (fe_rel WIsoEqns) C
           (wiso_quiver_hom i) (wiso_quiver_hom_merges i) _ _ WI_g).
Qed.

(** The converse: 函子 out [WalkingIso] carries two
 generators inverse pair, two laws coming [wiso_fg]
 [wiso_gf] under [fmap_respects]. （已译） *)
Lemma functor_iso_to_from (F : WalkingIso ⟶ C) :
  fmap[F] iso_f ∘ fmap[F] iso_g ≈ id.
Proof.
  rewrite <- fmap_comp.
  rewrite (@fmap_respects _ _ F _ _ _ _ wiso_fg).
  apply fmap_id.
Qed.

Lemma functor_iso_from_to (F : WalkingIso ⟶ C) :
  fmap[F] iso_g ∘ fmap[F] iso_f ≈ id.
Proof.
  rewrite <- fmap_comp.
  rewrite (@fmap_respects _ _ F _ _ _ _ wiso_gf).
  apply fmap_id.
Qed.

Definition IsoOfFunctor (F : WalkingIso ⟶ C) :
  fobj[F] WI_A ≅ fobj[F] WI_B := {|
  to          := fmap[F] iso_f;
  from        := fmap[F] iso_g;
  iso_to_from := functor_iso_to_from F;
  iso_from_to := functor_iso_from_to F
|}.

(** Round trip one, 同构 side: 对象 come back on
 nose two 态射 up [≈]. （已译） *)
Example wiso_round_obj_a {a b : C} (i : a ≅ b) :
  fobj[WalkingIsoFunctor i] WI_A = a := eq_refl.
Example wiso_round_obj_b {a b : C} (i : a ≅ b) :
  fobj[WalkingIsoFunctor i] WI_B = b := eq_refl.

Theorem wiso_round_morphisms {a b : C} (i : a ≅ b) :
  ((to (IsoOfFunctor (WalkingIsoFunctor i)) ≈ to i) *
   (from (IsoOfFunctor (WalkingIsoFunctor i)) ≈ from i))%type.
Proof. exact (WalkingIsoFunctor_f i, WalkingIsoFunctor_g i). Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wiso_round_obj (F : WalkingIso ⟶ C) (x : WIsoNode) :
  fobj[F] x = wiso_node (IsoOfFunctor F) x :=
  match x with WI_A => eq_refl | WI_B => eq_refl end.

Theorem wiso_functor_round (F : WalkingIso ⟶ C) :
  forall (x y : WIsoNode) (p : x ~{WalkingIso}~> y),
    hom_cast (wiso_round_obj F x) (wiso_round_obj F y) (fmap[F] p)
      ≈ fmap[WalkingIsoFunctor (IsoOfFunctor F)] p.
Proof.
  apply (@PresentedFunctor_unique WIsoQuiver (fe_rel WIsoEqns) C
           (wiso_quiver_hom (IsoOfFunctor F))
           (wiso_quiver_hom_merges (IsoOfFunctor F))
           F (wiso_round_obj F)).
  intros x y e; destruct e; reflexivity.
Qed.

Theorem wiso_functor_round_strict (F : WalkingIso ⟶ C) :
  @equiv _ (@Functor_StrictEq_Setoid WalkingIso C)
    F (WalkingIsoFunctor (IsoOfFunctor F)).
Proof.
  apply (strict_of_hom_cast F (WalkingIsoFunctor (IsoOfFunctor F))
           (wiso_round_obj F)).
  exact (wiso_functor_round F).
Qed.

(** The 普遍性质, bundled: give 函子 out of
 [WalkingIso] exactly give 同构, 函子 is
 unique at strict strength. （已译） *)
Theorem walking_iso_universal {a b : C} (i : a ≅ b) :
  { F : WalkingIso ⟶ C &
  { Hobj : forall x : WIsoNode, fobj[F] x = wiso_node i x &
    (((hom_cast (Hobj WI_A) (Hobj WI_B) (fmap[F] iso_f) ≈ to i) *
      (hom_cast (Hobj WI_B) (Hobj WI_A) (fmap[F] iso_g) ≈ from i)) *
     (forall (K : WalkingIso ⟶ C)
        (Hobj' : forall x : WIsoNode, fobj[K] x = wiso_node i x),
        (forall (x y : WIsoNode) (e : WIsoEdge x y),
           hom_cast (Hobj' x) (Hobj' y)
             (fmap[K] (@pgen WIsoQuiver (fe_rel WIsoEqns) x y e))
             ≈ wiso_edgemap i x y e) ->
        forall (x y : WIsoNode) (p : x ~{WalkingIso}~> y),
          hom_cast (Hobj' x) (Hobj' y) (fmap[K] p)
            ≈ hom_cast (Hobj x) (Hobj y) (fmap[F] p)))%type } }.
Proof.
  exists (WalkingIsoFunctor i), (fun _ => eq_refl).
  split; [ split | ].
  - exact (WalkingIsoFunctor_f i).
  - exact (WalkingIsoFunctor_g i).
  - intros K Hobj' Hgen x y p.
    exact (@PresentedFunctor_unique WIsoQuiver (fe_rel WIsoEqns) C
             (wiso_quiver_hom i) (wiso_quiver_hom_merges i)
             K Hobj' Hgen x y p).
Qed.

End IndexShape.
